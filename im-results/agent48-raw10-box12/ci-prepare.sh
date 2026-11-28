#!/usr/bin/env bash
set -euo pipefail
python3 "$D/unpack.py" "$WORK"
cp "$D"/PackedFinite.lean "$D"/Raw10RefinedBox12Cut.lean "$D"/Raw10RefinedBox12.lean "$WORK/"
cp "$D/pack-tree.py" "$WORK/"
cd "$WORK"
export LEAN_PATH="$WORK:$WORK/tree:$DEPS"
python3 prepare.py "$GITHUB_WORKSPACE"
python3 search.py
python3 extend.py
python3 extend2.py
python3 extend3.py
python3 emit_blocks.py
python3 emit_tree.py
python3 pack-tree.py
for m in Box12Core Box12Small OneRASparseBlock2 OneRASparse2 OneRASparseBlock3 OneRASparse3 PackedFinite Box12Hard{0..11} Box12External Raw10RefinedBox12Cut; do
  lean -j1 -o "$m.olean" "$m.lean"
done
tar -czf /tmp/box12-common.tar.gz ./*.lean ./*.olean tree/*.lean
