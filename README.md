# mini-prover
[![Build Status](https://travis-ci.org/lsrcz/mini-prover.svg?branch=master)](https://travis-ci.org/lsrcz/mini-prover)
[![Coverage Status](https://coveralls.io/repos/github/lsrcz/mini-prover/badge.svg?branch=master)](https://coveralls.io/github/lsrcz/mini-prover?branch=master)

Term project for TaPL. A mini coq-like proof assistant.

---

## Usage 

### System Requirement

- Linux or macOS, currently not tested on Windows.
- The Haskell Tool Stack

### Compiling

`stack build`

### Execution

`stack exec mini-prover-exe`

For verbose output:

`stack exec mini-prover-exe -- -v[0-3]`

### Demos

See `./demo/demo.v`.

### Unit Test

`stack test`

## Detail

See `./tex/report`.
