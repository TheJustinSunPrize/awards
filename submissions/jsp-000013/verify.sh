#!/bin/sh
set -eu
cd "$(dirname "$0")"
export LEAN_NUM_THREADS=1
lake build StandardStatement
lake env lean src/StandardStatement.lean
python3 verify_certificate.py
