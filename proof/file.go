package proof

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/lightninglabs/taro/asset"
	"github.com/lightninglabs/taro/commitment"
	"github.com/lightningnetwork/lnd/tlv"
)

const (
	// MaxFileSize represents the maximum file size in bytes allowed for a
	// proof file.
	//
	// TODO: Come up with a more sensible value.
	MaxFileSize = math.MaxUint32
)

var (
	// ErrInvalidChecksum is an error returned when an invalid proof file
	// checksum is detected while deserializing it.
	ErrInvalidChecksum = errors.New("invalid proof file checksum")
)

// Version denotes the versioning scheme for proof files.
type Version uint32

const (
	// V0 is the first version of the proof file.
	V0 Version = 0
)

// hashedProof is a struct that contains a proof and its chained checksum.
type hashedProof struct {
	// proof is the proof that is hashed.
	proof Proof

	// hash is the SHA256 sum of (prev_hash || proof).
	hash [sha256.Size]byte
}

// File represents a proof file comprised of proofs for all of an asset's state
// transitions back to its genesis state.
type File struct {
	// Version is the version of the proof file.
	Version Version

	// proofs are the proofs contained within the proof file starting from
	// the genesis proof.
	proofs []*hashedProof
}

// NewEmptyFile returns a new empty file with the given version.
func NewEmptyFile(v Version) *File {
	return &File{
		Version: v,
	}
}

// NewFile returns a new proof file given a version and a series of state
// transition proofs.
func NewFile(v Version, proofs ...Proof) (*File, error) {
	var (
		prevHash     [sha256.Size]byte
		linkedProofs = make([]*hashedProof, len(proofs))
	)

	// We start out with the zero hash as the previous hash and then create
	// the checksum of SHA256(prev_hash || proof) as our incremental
	// checksum for each of the proofs, basically building a proof chain
	// similar to Bitcoin's time chain.
	for idx := range proofs {
		proof := proofs[idx]

		hash, err := hashProof(&proof, prevHash)
		if err != nil {
			return nil, err
		}

		linkedProofs[idx] = &hashedProof{
			proof: proof,
			hash:  hash,
		}
		prevHash = linkedProofs[idx].hash
	}

	return &File{
		Version: v,
		proofs:  linkedProofs,
	}, nil
}

// Encode encodes the proof file into `w` including its checksum.
func (f *File) Encode(w io.Writer) error {
	err := binary.Write(w, binary.BigEndian, uint32(f.Version))
	if err != nil {
		return err
	}

	var (
		buf      [8]byte
		proofBuf bytes.Buffer
	)
	if err := tlv.WriteVarInt(w, uint64(len(f.proofs)), &buf); err != nil {
		return err
	}
	for _, proof := range f.proofs {
		proof := proof

		// To the file we write the proof, followed by its hash, which
		// is SHA256(prev_hash || proof). That way if we serially read
		// the whole file using the zero hash as the first prev_hash,
		// then we can make sure we have no data corruption if the
		// serially built hash is equal to the last proof's hash. On the
		// other hand, if we want to append a proof to a file, we just
		// need to read the last proof, use its hash as the prev_hash
		// for the one to append, and we're done.
		proofBuf.Reset()
		if err = proof.proof.Encode(&proofBuf); err != nil {
			return err
		}

		// Now that we know how many bytes to write, let's actually
		// write them.
		err := tlv.WriteVarInt(w, uint64(proofBuf.Len()), &buf)
		if err != nil {
			return err
		}
		if _, err := w.Write(proofBuf.Bytes()); err != nil {
			return err
		}

		// The hash is not part of the proof's TLV stream, so we didn't
		// count it above.
		if _, err := w.Write(proof.hash[:]); err != nil {
			return err
		}
	}

	return nil
}

// Decode decodes a proof file from `r`.
func (f *File) Decode(r io.Reader) error {
	var version uint32
	if err := binary.Read(r, binary.BigEndian, &version); err != nil {
		return err
	}
	f.Version = Version(version)

	var tlvBuf [8]byte
	numProofs, err := tlv.ReadVarInt(r, &tlvBuf)
	if err != nil {
		return err
	}

	var (
		prevHash, currentHash [sha256.Size]byte
	)
	f.proofs = make([]*hashedProof, numProofs)
	for i := uint64(0); i < numProofs; i++ {
		// We need to find out how many bytes we expect for the proof,
		// so we can limit the TLV reader.
		numProofBytes, err := tlv.ReadVarInt(r, &tlvBuf)
		if err != nil {
			return err
		}

		var (
			proofReader = io.LimitReader(r, int64(numProofBytes))
			proof       Proof
			proofHash   [sha256.Size]byte
		)

		// We read the proof first. This is a TLV stream, so it should
		// know exactly how many bytes to read.
		if err := proof.Decode(proofReader); err != nil {
			return err
		}

		// We now read the proof's hash in the file which reflects the
		// current checksum.
		if _, err := io.ReadFull(r, proofHash[:]); err != nil {
			return err
		}

		// Now that we have read both the proof and the expected
		// checksum of it, we calculate our own checksum and verify they
		// match.
		currentHash, err = hashProof(&proof, prevHash)
		if err != nil {
			return err
		}

		if proofHash != currentHash {
			return ErrInvalidChecksum
		}

		f.proofs[i] = &hashedProof{
			proof: proof,
			hash:  currentHash,
		}
		prevHash = currentHash
	}

	return nil
}

// IsEmpty returns true if the file does not contain any proofs.
func (f *File) IsEmpty() bool {
	return len(f.proofs) == 0
}

// NumProofs returns the number of proofs contained in this file.
func (f *File) NumProofs() int {
	return len(f.proofs)
}

// LastProof returns the last proof in the chain of proofs. If the file is
// empty, this return nil.
func (f *File) LastProof() *Proof {
	if f.IsEmpty() {
		return nil
	}

	return &f.proofs[len(f.proofs)-1].proof
}

// AppendProof appends a proof to the file and calculates its chained hash.
func (f *File) AppendProof(proof Proof) error {
	var prevHash [sha256.Size]byte
	if !f.IsEmpty() {
		prevHash = f.proofs[len(f.proofs)-1].hash
	}

	hash, err := hashProof(&proof, prevHash)
	if err != nil {
		return err
	}

	f.proofs = append(f.proofs, &hashedProof{
		proof: proof,
		hash:  hash,
	})

	return nil
}

// ReplaceLastProof attempts to replace the last proof in the file with another
// one, updating its chained hash in the process.
func (f *File) ReplaceLastProof(proof Proof) error {
	if f.IsEmpty() {
		return fmt.Errorf("file is empty")
	}

	var prevHash [sha256.Size]byte
	if f.NumProofs() > 1 {
		// We want the prev_hash of the last proof, so we need to go
		// back 2. If we're replacing the single proof of the file, then
		// the prev_hash is the zero hash.
		prevHash = f.proofs[len(f.proofs)-2].hash
	}

	hash, err := hashProof(&proof, prevHash)
	if err != nil {
		return err
	}

	f.proofs[len(f.proofs)-1] = &hashedProof{
		proof: proof,
		hash:  hash,
	}

	return nil
}

// hashProof hashes a proof's content together with the previous hash:
//
//	SHA256(prev_hash || proof).
func hashProof(proof *Proof, prevHash [32]byte) ([32]byte, error) {
	var buf bytes.Buffer
	if _, err := buf.Write(prevHash[:]); err != nil {
		return [32]byte{}, err
	}
	if err := proof.Encode(&buf); err != nil {
		return [32]byte{}, err
	}

	return sha256.Sum256(buf.Bytes()), nil
}

// AssetSnapshot commits to the result of a valid proof within a proof file.
// This represents the state of an asset's lineage at a given point in time.
type AssetSnapshot struct {
	// Asset is the resulting asset of a valid proof.
	Asset *asset.Asset

	// OutPoint is the outpoint that commits to the asset specified above.
	OutPoint wire.OutPoint

	// AnchorBlockHash is the block hash that anchors the Bitcoin
	// transaction for this Taro state transition.
	AnchorBlockHash chainhash.Hash

	// AnchorBlockHeight is the height of the block hash above.
	AnchorBlockHeight uint32

	// AnchorTxIndex is the transaction index within the above block where
	// the AnchorTx can be found.
	AnchorTxIndex uint32

	// AnchorTx is the transaction that commits to the above asset.
	AnchorTx *wire.MsgTx

	// OutputIndex is the output index in the above transaction that
	// commits to the output.
	OutputIndex uint32

	// InternalKey is the internal key used to commit to the above asset in
	// the AnchorTx.
	InternalKey *btcec.PublicKey

	// ScriptRoot is the Taro commitment root committed to using the above
	// internal key in the Anchor transaction.
	ScriptRoot *commitment.TaroCommitment

	// SplitAsset is the optional indicator that the asset in the snapshot
	// resulted from splitting an asset. If this is true then the root asset
	// of the split can be found in the asset witness' split commitment.
	SplitAsset bool
}
