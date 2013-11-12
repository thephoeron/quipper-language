QUIPPER-LANGUAGE
================

Quipper: embedded, scalable functional programming language for quantum computing.

Unofficial fork from: http://www.mathstat.dal.ca/~selinger/quipper/

Tested with the Haskell Platform 2012 & 2013 on Linux x86_64/OS X 10.7

To-do
-----

* Make Quipper `cabal-install`able

Installation & Use
------------------

Clone this repo to somewhere obvious, like `~/quipper-language/`.

Install or update to the latest version of [The Haskell Platform](http://www.haskell.org/platform/).

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

 * random v1.0.1.1
 * mtl v2.1.2
 * primes v0.2.1.0
 * Lattices v0.0.1
 * zlib v0.5.4.1
 * fixedprec v0.1
 * containers v0.5.2.1
 * set-monad v0.1.0.0
 * quickcheck v2.6
