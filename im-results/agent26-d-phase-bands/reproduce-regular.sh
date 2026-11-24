#!/usr/bin/env bash
set -eu
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
base64 -d "$here/../agent35-d-regular-certificate/LeanSources.tar.xz.b64" > "$work/source.tar.xz"
echo '33380f7460ac295ee259d6e81182cd57afdcbbabdf73b0d8a729e49c077cd18b  source.tar.xz' > "$work/checksum"
cd "$work"
sha256sum -c checksum
tar -xJf source.tar.xz
cp "$here/GrowthBands.lean" "$here/RegularBands.lean" .
export LEAN_PATH="$PWD"
lean -o DRegular.olean DRegular.lean
lean -o GrowthBands.olean GrowthBands.lean
lean RegularBands.lean
