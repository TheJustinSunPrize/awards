#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p .build
lean --version
lean -o .build/Proof.olean Proof.lean
LEAN_PATH="$PWD/.build${LEAN_PATH:+:$LEAN_PATH}" leanchecker -v Proof
