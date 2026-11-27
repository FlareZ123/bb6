#!/usr/bin/env bash
set -euo pipefail
c="$1"; shift
base="$PWD/im-results/agent3-raw139-e0-oneLB"
mkdir -p /tmp/oneLB-discovery /tmp/oneLB-long
gh api "repos/$GITHUB_REPOSITORY/actions/artifacts/15169504259/zip" > /tmp/oneLB-discovery.zip
unzip -q /tmp/oneLB-discovery.zip -d /tmp/oneLB-discovery
dirs=()
for id in "$@"; do
  [[ "$id" =~ ^[0-9]+$ ]]
  mkdir -p "/tmp/oneLB-long/$id"
  gh api "repos/$GITHUB_REPOSITORY/actions/artifacts/$id/zip" > "/tmp/oneLB-long/$id.zip"
  unzip -q "/tmp/oneLB-long/$id.zip" -d "/tmp/oneLB-long/$id"
  dirs+=("/tmp/oneLB-long/$id")
done
python3 - "$c" "${dirs[@]}" <<'PY'
import json,pathlib,sys
need={"09":{"BB6.Agent3OneLBReturn.both_weighted","BB6.Agent3OneLBF1Return.weighted"},
      "21":{"BB6.Agent3OneLBD0.weighted"}}[sys.argv[1]]
got=set()
for d in map(pathlib.Path,sys.argv[2:]):
    p=list(d.rglob("manifest.json"));assert len(p)==1,p
    got.add(json.loads(p[0].read_text())["claim"]["theorem"])
assert got==need,(got,need)
PY
bash "$base/check-child.sh" "$c" /tmp/oneLB-discovery "${dirs[@]}"
