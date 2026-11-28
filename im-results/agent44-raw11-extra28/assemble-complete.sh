#!/usr/bin/env bash
# Assemble one original-source Lean theorem from twelve separately accepted,
# exact-table sibling certificates. Nothing is asserted if any input is absent.
set -euo pipefail

: "${EIGHT_RUN:?CI workflow run ID for accepted eight-child matrix required}"
: "${FOUR_RUN:?CI workflow run ID for accepted four-child matrix required}"
: "${GH_TOKEN:?A GitHub token with actions:read required}"
REPO="FlareZ123/bb6"
ROOT="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-/tmp/raw11}"
DEPS="${DEPS:-/tmp/raw11-deps}"
OUTPUT="${OUTPUT:-/tmp/raw11-final-output}"
mkdir -p "$WORK" "$DEPS" "$OUTPUT" /tmp/raw11-artifacts
command -v gh
command -v lean
command -v node

for id in 7 8 9 10 12 13 14 15; do
  gh run download "$EIGHT_RUN" -R "$REPO" \
    --name "agent44-raw11-extra28-confirmed-$id" \
    --dir "/tmp/raw11-artifacts/$id"
done
for id in 16 17 18 19; do
  gh run download "$FOUR_RUN" -R "$REPO" \
    --name "agent44-raw11-extra28-child-$id" \
    --dir "/tmp/raw11-artifacts/$id"
done

# Never silently replace one proof object with another object's name.
for id in 7 8 9 10 12 13 14 15 16 17 18 19; do
  DIR="/tmp/raw11-artifacts/$id/compiled"
  test -d "$DIR" || { echo "no compiled proof objects for D1=$id" >&2; exit 1; }
  for FILE in "$DIR"/*.olean; do
    test -f "$FILE" || { echo "missing .olean for D1=$id" >&2; exit 1; }
    NAME="$(basename "$FILE")"
    if [ -e "$WORK/$NAME" ]; then
      cmp "$FILE" "$WORK/$NAME" || {
        echo "Nonidentical duplicate Lean object $NAME from D1=$id" >&2
        exit 1
      }
    else
      cp "$FILE" "$WORK/$NAME"
    fi
  done
done

declare -A ROOTS=(
  [7]=Raw11Extra28M7Join
  [8]=Raw11Extra28D1LCJoin
  [9]=Raw11Extra28M9Join
  [10]=Raw11Extra28M10Join
  [12]=Raw11Extra28LDJoin
  [13]=Raw11Extra28M13Join
  [14]=Raw11Extra28M14Join
  [15]=Raw11Extra28M15Join
  [16]=Raw11Extra28M16Join
  [17]=FastRaw11M17Join
  [18]=FastRaw11M18Join
  [19]=FastRaw11M19Join
)
for id in 7 8 9 10 12 13 14 15 16 17 18 19; do
  test -s "$WORK/${ROOTS[$id]}.olean" || {
    echo "no checked main theorem for D1=$id" >&2
    exit 1
  }
done

curl --retry 2 --retry-delay 5 -fsSL \
  -H "Authorization: Bearer $GH_TOKEN" \
  -H "Accept: application/vnd.github+json" \
  "https://api.github.com/repos/$REPO/actions/artifacts/15144626755/zip" \
  -o "$OUTPUT/original-cache.zip"
unzip -q "$OUTPUT/original-cache.zip" -d "$DEPS"
export LEAN_PATH="$WORK:$(find "$DEPS" -name '*.olean' -printf '%h\n' | sort -u | paste -sd:)"
export PATH="$HOME/.elan/bin:$PATH"

cp "$ROOT/Raw11Extra28AllChildren.lean" "$ROOT/Raw11Extra28MinimalJoin.lean" "$WORK/"
cd "$WORK"
lean -o Raw11Extra28AllChildren.olean Raw11Extra28AllChildren.lean \
  2>&1 | tee "$OUTPUT/frontier.log"
lean -o Raw11Extra28MinimalJoin.olean Raw11Extra28MinimalJoin.lean \
  2>&1 | tee "$OUTPUT/minimal-conditional-join.log"
node "$ROOT/generate-minimal-join.cjs" "$WORK/Raw11Extra28LiteralComplete.lean"
lean -o Raw11Extra28LiteralComplete.olean Raw11Extra28LiteralComplete.lean \
  2>&1 | tee "$OUTPUT/literal-complete.log"

grep -F "'BB6.Agent44Extra28Completed.literal_complete' depends on axioms:" \
  "$OUTPUT/literal-complete.log"
if grep -E 'sorryAx|native_decide' "$OUTPUT"/*.log; then
  echo "Unapproved axiom in entire composed source" >&2; exit 1
fi
cp "$WORK/Raw11Extra28LiteralComplete.lean" \
   "$WORK/Raw11Extra28LiteralComplete.olean" "$OUTPUT/"
sha256sum "$OUTPUT/Raw11Extra28LiteralComplete.lean" \
  "$OUTPUT/Raw11Extra28LiteralComplete.olean" \
  > "$OUTPUT/final-source-and-object.sha256"
echo "Full six-hole parent source theorem checked; confirm all child input runs succeeded."
