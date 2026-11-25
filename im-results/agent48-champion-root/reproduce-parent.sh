#!/usr/bin/env bash
set -euo pipefail
work="$PWD/.tmp/a48-parent"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/imports"
base64 -d im-results/agent13-coverage/BB6Coverage.lean.xz.b64 | xz -d > "$work/imports/BB6Coverage.lean"
python3 tools/lean_compile_closure.py \
  im-results/agent48-champion-root/ChampionParentCover.lean \
  im-results/agent48-counted-inc0/ChampionParentExact.lean \
  --override TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean \
  --workdir "$work/build" --jobs 4 | tee "$work/log"
for theorem in parent_cover parent_reachable parentCertificate sibling_never lc_never re_never champion_parent_exact_cover championParentExactCertificate; do
  grep -E "$theorem.*depends on axioms" "$work/log"
done
if grep -E 'depends on axioms.*(sorryAx|native_decide)' "$work/log"; then exit 1; fi
