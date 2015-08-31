# QUIPPER-LANGUAGE

Quipper: embedded, scalable functional programming language for quantum computing, based on the Quantum Lambda Calculus; v0.7 (10/14/2014).

Unofficial fork from: http://www.mathstat.dal.ca/~selinger/quipper/

Tested with the Haskell Platform 2012 & 2013 on Linux x86_64/OS X 10.7

To-do
-----

* Make Quipper Cabal installable and sandboxed

Installation & Use
------------------

Clone this repo to somewhere obvious, like `~/quipper-language/`.

Install or update to the latest version of `cabal-install` and `ghc` from your package manager.

Double-check the dependencies list below, and ensure you have them all installed under your `~/.cabal` directory.  `cabal install ...` manually as needed.

Run `make` in the parent directory.

Add `quipper/scripts/` from the repo to your PATH.  This provides wrapper scripts around GHC and GHCi which loads all the necessary libraries for quantum hacking.

You can then call the Quipper compiler by:

	$ quipper And_gate.hs

Or run quipper in interactive mode:

	$ quipperi
	...
	GHCi, version 7.6.3: http://www.haskell.org/ghc/  :? for help
	Loading package ghc-prim ... linking ... done.
	Loading package integer-gmp ... linking ... done.
	Loading package base ... linking ... done.
	Prelude> _

Dependencies
------------

Ensure these packages are installed from Hackage before compilation:

 * random v.1.0.1.1
 * mtl v.2.1.2
 * primes v.0.2.1.0
 * Lattices v.0.0.1
 * zlib v.0.5.4.1
 * easyrender v.0.1.0.0
 * fixedprec v.0.2.1.0
 * newsynth v.0.1.0.0
 * containers v.0.5.2.1
 * set-monad v.0.1.0.0
 * QuickCheck v.2.6
