#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p generated-work
"${CXX:-c++}" -O3 -std=c++17 tools/discover.cpp -o generated-work/discover
generated-work/discover
python3 tools/generate_certificates.py
python3 tools/generate_bound.py
