#!/usr/bin/env bash
set -euo pipefail
cd "$WORK"
export LEAN_PATH="$WORK:$WORK/tree:$DEPS"
lean -j1 -o tree/Box12Cover.olean tree/Box12Cover.lean | tee /tmp/box12-final.log
lean -j1 -o Raw10RefinedBox12.olean Raw10RefinedBox12.lean | tee -a /tmp/box12-final.log
if grep -Eq 'sorryAx|native_decide|Lean.ofReduceBool' /tmp/box12-final.log; then exit 1; fi
grep -F 'BB6.Agent48Box12.box12_weighted' /tmp/box12-final.log
grep -F 'BB6.Agent48Raw10RefinedBox12.parentCover29' /tmp/box12-final.log
grep -F 'BB6.Agent48Raw10RefinedBox12.parentCover27' /tmp/box12-final.log
tar -czf /tmp/box12-final.tar.gz ./*.lean ./*.olean tree/*.lean tree/*.olean
