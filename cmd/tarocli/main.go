// Copyright (c) 2013-2017 The btcsuite developers
// Copyright (c) 2015-2016 The Decred developers
// Copyright (C) 2015-2022 The Lightning Network Developers

package main

import (
	"context"
	"crypto/tls"
	"fmt"
	"net"
	"os"
	"path/filepath"
	"strings"
	"syscall"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/lightninglabs/taro"
	"github.com/lightninglabs/taro/tarorpc"
	"github.com/lightningnetwork/lnd/lncfg"
	"github.com/lightningnetwork/lnd/lnrpc"
	"github.com/lightningnetwork/lnd/macaroons"
	"github.com/lightningnetwork/lnd/tor"
	"github.com/urfave/cli"
	"golang.org/x/term"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
)

const (
	defaultDataDir          = "data"
	defaultTLSCertFilename  = "tls.cert"
	defaultMacaroonFilename = "admin.macaroon"
	defaultRPCPort          = "10029"
	defaultRPCHostPort      = "localhost:" + defaultRPCPort
)

var (
	defaultTaroDir     = btcutil.AppDataDir("taro", false)
	defaultTLSCertPath = filepath.Join(defaultTaroDir, defaultTLSCertFilename)

	// maxMsgRecvSize is the largest message our client will receive. We
	// set this to 200MiB atm.
	maxMsgRecvSize = grpc.MaxCallRecvMsgSize(lnrpc.MaxGrpcMsgSize)
)

func fatal(err error) {
	fmt.Fprintf(os.Stderr, "[tarocli] %v\n", err)
	os.Exit(1)
}

func getClient(ctx *cli.Context) (tarorpc.TaroClient, func()) {
	conn := getClientConn(ctx, false)

	cleanUp := func() {
		conn.Close()
	}

	return tarorpc.NewTaroClient(conn), cleanUp
}

func getClientConn(ctx *cli.Context, skipMacaroons bool) *grpc.ClientConn {
	// First, we'll get the selected stored profile or an ephemeral one
	// created from the global options in the CLI context.
	profile, err := getGlobalOptions(ctx, skipMacaroons)
	if err != nil {
		fatal(fmt.Errorf("could not load global options: %v", err))
	}

	// Load the specified TLS certificate.
	certPool, err := profile.cert()
	if err != nil {
		fatal(fmt.Errorf("could not create cert pool: %v", err))
	}

	// Build transport credentials from the certificate pool. If there is no
	// certificate pool, we expect the server to use a non-self-signed
	// certificate such as a certificate obtained from Let's Encrypt.
	var creds credentials.TransportCredentials
	if certPool != nil {
		creds = credentials.NewClientTLSFromCert(certPool, "")
	} else {
		// Fallback to the system pool. Using an empty tls config is an
		// alternative to x509.SystemCertPool(). That call is not
		// supported on Windows.
		creds = credentials.NewTLS(&tls.Config{})
	}

	// Create a dial options array.
	opts := []grpc.DialOption{
		grpc.WithTransportCredentials(creds),
	}

	// Only process macaroon credentials if --no-macaroons isn't set and
	// if we're not skipping macaroon processing.
	if !profile.NoMacaroons && !skipMacaroons {
		// Find out which macaroon to load.
		macName := profile.Macaroons.Default
		if ctx.GlobalIsSet("macfromjar") {
			macName = ctx.GlobalString("macfromjar")
		}
		var macEntry *macaroonEntry
		for _, entry := range profile.Macaroons.Jar {
			if entry.Name == macName {
				macEntry = entry
				break
			}
		}
		if macEntry == nil {
			fatal(fmt.Errorf("macaroon with name '%s' not found "+
				"in profile", macName))
		}

		// Get and possibly decrypt the specified macaroon.
		//
		// TODO(guggero): Make it possible to cache the password so we
		// don't need to ask for it every time.
		mac, err := macEntry.loadMacaroon(readPassword)
		if err != nil {
			fatal(fmt.Errorf("could not load macaroon: %v", err))
		}

		macConstraints := []macaroons.Constraint{
			// We add a time-based constraint to prevent replay of the
			// macaroon. It's good for 60 seconds by default to make up for
			// any discrepancy between client and server clocks, but leaking
			// the macaroon before it becomes invalid makes it possible for
			// an attacker to reuse the macaroon. In addition, the validity
			// time of the macaroon is extended by the time the server clock
			// is behind the client clock, or shortened by the time the
			// server clock is ahead of the client clock (or invalid
			// altogether if, in the latter case, this time is more than 60
			// seconds).
			macaroons.TimeoutConstraint(profile.Macaroons.Timeout),

			// Lock macaroon down to a specific IP address.
			macaroons.IPLockConstraint(profile.Macaroons.IP),
		}

		// Apply constraints to the macaroon.
		constrainedMac, err := macaroons.AddConstraints(
			mac, macConstraints...,
		)
		if err != nil {
			fatal(err)
		}

		// Now we append the macaroon credentials to the dial options.
		cred, err := macaroons.NewMacaroonCredential(constrainedMac)
		if err != nil {
			fatal(fmt.Errorf("error cloning mac: %v", err))
		}
		opts = append(opts, grpc.WithPerRPCCredentials(cred))
	}

	// If a socksproxy server is specified we use a tor dialer
	// to connect to the grpc server.
	if ctx.GlobalIsSet("socksproxy") {
		socksProxy := ctx.GlobalString("socksproxy")
		torDialer := func(_ context.Context, addr string) (net.Conn, error) {
			return tor.Dial(
				addr, socksProxy, false, false,
				tor.DefaultConnTimeout,
			)
		}
		opts = append(opts, grpc.WithContextDialer(torDialer))
	} else {
		// We need to use a custom dialer so we can also connect to
		// unix sockets and not just TCP addresses.
		genericDialer := lncfg.ClientAddressDialer(defaultRPCPort)
		opts = append(opts, grpc.WithContextDialer(genericDialer))
	}

	opts = append(opts, grpc.WithDefaultCallOptions(maxMsgRecvSize))

	conn, err := grpc.Dial(profile.RPCServer, opts...)
	if err != nil {
		fatal(fmt.Errorf("unable to connect to RPC server: %v", err))
	}

	return conn
}

// extractPathArgs parses the TLS certificate and macaroon paths from the
// command.
func extractPathArgs(ctx *cli.Context) (string, string, error) {
	// We'll start off by parsing the active network. These are needed to
	// determine the correct path to the macaroon when not specified.
	network := strings.ToLower(ctx.GlobalString("network"))
	switch network {
	case "mainnet", "testnet", "regtest", "simnet", "signet":
	default:
		return "", "", fmt.Errorf("unknown network: %v", network)
	}

	// We'll now fetch the tarodir so we can make a decision  on how to
	// properly read the macaroons (if needed) and also the cert. This will
	// either be the default, or will have been overwritten by the end
	// user.
	taroDir := lncfg.CleanAndExpandPath(ctx.GlobalString("tarodir"))

	// If the macaroon path as been manually provided, then we'll only
	// target the specified file.
	var macPath string
	if ctx.GlobalString("macaroonpath") != "" {
		macPath = lncfg.CleanAndExpandPath(ctx.GlobalString("macaroonpath"))
	} else {
		// Otherwise, we'll go into the path:
		// tarodir/data/<network> in order to fetch the
		// macaroon that we need.
		macPath = filepath.Join(
			taroDir, defaultDataDir, network, defaultMacaroonFilename,
		)
	}

	tlsCertPath := lncfg.CleanAndExpandPath(ctx.GlobalString("tlscertpath"))

	// If a custom tarod directory was set, we'll also check if custom paths
	// for the TLS cert and macaroon file were set as well. If not, we'll
	// override their paths so they can be found within the custom tarod
	// directory set. This allows us to set a custom tarod directory, along
	// with custom paths to the TLS cert and macaroon file.
	if taroDir != defaultTaroDir {
		tlsCertPath = filepath.Join(taroDir, defaultTLSCertFilename)
	}

	return tlsCertPath, macPath, nil
}

func main() {
	app := cli.NewApp()
	app.Name = "tarocli"
	app.Version = taro.Version() + " commit=" + taro.Commit
	app.Usage = "control plane for your Taro Daemon (tarod)"
	app.Flags = []cli.Flag{
		cli.StringFlag{
			Name:  "rpcserver",
			Value: defaultRPCHostPort,
			Usage: "The host:port of LN daemon.",
		},
		cli.StringFlag{
			Name:      "tarodir",
			Value:     defaultTaroDir,
			Usage:     "The path to taro's base directory.",
			TakesFile: true,
		},
		cli.StringFlag{
			Name: "socksproxy",
			Usage: "The host:port of a SOCKS proxy through " +
				"which all connections to the Taro " +
				"daemon will be established over.",
		},
		cli.StringFlag{
			Name:      "tlscertpath",
			Value:     defaultTLSCertPath,
			Usage:     "The path to tarod's TLS certificate.",
			TakesFile: true,
		},
		cli.StringFlag{
			Name: "network, n",
			Usage: "The network tarod is running on, e.g. mainnet, " +
				"testnet, etc.",
			Value: "testnet",
		},
		cli.BoolFlag{
			Name:  "no-macaroons",
			Usage: "Disable macaroon authentication.",
		},
		cli.StringFlag{
			Name:      "macaroonpath",
			Usage:     "The path to macaroon file.",
			TakesFile: true,
		},
		cli.Int64Flag{
			Name:  "macaroontimeout",
			Value: 60,
			Usage: "Anti-replay macaroon validity time in seconds.",
		},
		cli.StringFlag{
			Name:  "macaroonip",
			Usage: "If set, lock macaroon to specific IP address.",
		},
		cli.StringFlag{
			Name: "profile, p",
			Usage: "Instead of reading settings from command " +
				"line parameters or using the default " +
				"profile, use a specific profile. If " +
				"a default profile is set, this flag can be " +
				"set to an empty string to disable reading " +
				"values from the profiles file.",
		},
		cli.StringFlag{
			Name: "macfromjar",
			Usage: "Use this macaroon from the profile's " +
				"macaroon jar instead of the default one. " +
				"Can only be used if profiles are defined.",
		},
	}
	app.Commands = []cli.Command{
		stopCommand,
		debugLevelCommand,
		profileSubCommand,
	}
	app.Commands = append(app.Commands, assetsCommands...)
	app.Commands = append(app.Commands, addrCommands...)
	app.Commands = append(app.Commands, proofCommands...)

	if err := app.Run(os.Args); err != nil {
		fatal(err)
	}
}

// readPassword reads a password from the terminal. This requires there to be an
// actual TTY so passing in a password from stdin won't work.
func readPassword(text string) ([]byte, error) {
	fmt.Print(text)

	// The variable syscall.Stdin is of a different type in the Windows API
	// that's why we need the explicit cast. And of course the linter
	// doesn't like it either.
	pw, err := term.ReadPassword(int(syscall.Stdin)) // nolint:unconvert
	fmt.Println()
	return pw, err
}
