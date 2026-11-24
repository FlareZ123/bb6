#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD/fixture"
lean -o fixture/BusyBeaver/Basic.olean fixture/BusyBeaver/Basic.lean
lean -o fixture/WitnessExtract.olean WitnessExtract.lean
lean -o fixture/Source.olean fixture/Source.lean
lean fixture/Test.lean
