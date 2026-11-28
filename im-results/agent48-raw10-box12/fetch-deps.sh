#!/usr/bin/env bash
set -euo pipefail
mkdir -p /tmp/box12-deps
gh api repos/FlareZ123/bb6/actions/artifacts/15158192432/zip > /tmp/box12-deps.zip
echo '783b0daa58f8d42e6bc49bb29b6cb743b70acc6070337faa2686aa02379c55e9  /tmp/box12-deps.zip' | sha256sum -c -
unzip -q /tmp/box12-deps.zip -d /tmp/box12-deps
test -s "$DEPS/Raw10BoxCore.olean"
test -s "$DEPS/Box6Core.olean"
