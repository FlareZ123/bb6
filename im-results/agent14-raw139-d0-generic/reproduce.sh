#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-d0-generic"
common="$PWD/im-results/agent14-raw139-d0-zeroLF"
sibling="$1"
extraspec=""
extra_args=()
case "$sibling" in
  OneLA) label=LA; bound=1361; code=2; rootsha=6bc5c852ae4850ab0b121a0a082b0aa76738e619b2e905447f81cba16a983875; archive=source.tar.xz.b64; archivesha=af3ca0f10ca181c6b37c14764fff715c8d6aee6871b759d7e2d5e944fb92b449; script=sibling.py; spec=oneLA-spec.json ;;
  OneLF) label=OneLF; bound=42038; code=22; rootsha=b9da28e853bcf3b37606453d488ff2bb6a8f7a52216aa2702f9b99f3e8f01c57; archive=source-v2.tar.xz.b64; archivesha=d7df8ff3f2e38cef9e24e56e754163eabac7792d4da5d452e5416bcfec2db924; script=sibling-v2.py; spec=oneLF-spec.json ;;
  ZeroRC) label=ZeroRC; bound=775; code=9; rootsha=41b6b03422798ffc4f3325cbe49fa8fdd0d1c6449e1f282852e103d6655c5fe0; archive=source-v2.tar.xz.b64; archivesha=d7df8ff3f2e38cef9e24e56e754163eabac7792d4da5d452e5416bcfec2db924; script=sibling-v2.py; spec=zeroRC-spec.json; extraspec=zeroRC-spec.json.xz.b64; extraspecsha=3539b830711f1b97997d36965a61a612ab0f1f36c078dc7c987ea24b6f12878c ;;
  OneRF) label=OneRF; bound=6250; code=23; rootsha=6ca0dc341acf0aa3c54fb4e3ddbf277476829c6681d16b840ff85f5cf1cfccc5; archive=source-v2.tar.xz.b64; archivesha=d7df8ff3f2e38cef9e24e56e754163eabac7792d4da5d452e5416bcfec2db924; script=sibling-v2.py; spec=oneRF-spec.json; extraspec=oneRF-spec.json.xz.b64; extraspecsha=d8156ee92b768502ad10f5eff2a7f9f69ad348333af5486ea6f00a4fb24159f4 ;;
  ZeroRA) label=ZeroRA; bound=8840; code=1; rootsha=bafd8de380fe0e0323265a733343fa578e47b323d01d4818daf60e8c0b644c09; archive=source-v3.tar.xz.b64; archivesha=74dd96b96eff2a4ae2e79589a1450816e698a5eb5f4dac855908578731b6678b; script=sibling-v3.py; spec=zeroRA-spec.json; extraspec=zeroRA-spec.json.xz.b64; extraspecsha=6ef6b4e8c20cbcf71c54b49f5a09fd22a026a415e22e24bb52f128fc8130d385 ;;
  ZeroRF) label=ZeroRF; bound=9110; code=21; rootsha=292e8f8b7d9f0f7ce41280f374d32c103d1f0682fbc69d39a4b70ea91d81a9a9; archive=source-v3.tar.xz.b64; archivesha=74dd96b96eff2a4ae2e79589a1450816e698a5eb5f4dac855908578731b6678b; script=sibling-v3.py; spec=zeroRF-spec.json; extraspec=zeroRF-spec.json.xz.b64; extraspecsha=40b2d166ed81bcdd6e330dc4d53b825183ce389b81640ae70b37c10a12633fd2 ;;
  *) echo "Unknown sibling $sibling" >&2; exit 2 ;;
esac
work="$PWD/.tmp/a48-d0-$sibling"
mkdir -p "$work/src/common" "$work/src/generic" "$work/imports" "$work/build"
base64 -d "$common/source.tar.xz.b64" > "$work/common.tar.xz"
base64 -d "$base/$archive" > "$work/generic.tar.xz"
echo "96f3fb39a1beabc8319147f25e9a3e612fec818ae57c52c54d81fa1248e50559  $work/common.tar.xz" | sha256sum -c
echo "$archivesha  $work/generic.tar.xz" | sha256sum -c
tar -xJf "$work/common.tar.xz" -C "$work/src/common"
tar -xJf "$work/generic.tar.xz" -C "$work/src/generic"
if [[ -n "$extraspec" ]]; then
  base64 -d "$base/$extraspec" > "$work/spec.xz"
  echo "$extraspecsha  $work/spec.xz" | sha256sum -c
  xz -dc "$work/spec.xz" > "$work/src/generic/$spec"
  extra_args+=(--provenance-input "$base/$extraspec")
fi
PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA:$PWD/im-results/agent48-raw139-f1-oneLA" python3 "$work/src/generic/$script" "$work/src/common" "$work/imports" "$work/src/generic/$spec"
if [[ "$sibling" == ZeroRF ]]; then
  python3 "$base/patch-ray.py" "$work/imports"
  extra_args+=(--provenance-input "$base/patch-ray.py")
fi
root="$work/imports/Raw139D0${label}Cover.lean"
echo "$rootsha  $root" | sha256sum -c
python3 im-results/agent13-coverage/unpack.py
if [[ "$sibling" == OneLF || "$sibling" == ZeroRA || "$sibling" == ZeroRF ]]; then
  python3 im-results/agent13-block-far/specialize.py 4
fi
if [[ "$sibling" == ZeroRA ]]; then
  python3 im-results/agent13-block-far/specialize.py 5
fi
python3 tools/lean_compile_closure.py "$root" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label "raw139-d0-$sibling" --theorem "BB6.Agent14Raw139D0${label}.all_completions_weighted" --parent-table "[7,24,11,24,14,24,$code,16,12,11,24,24]" --weighted-bound "$bound" --artifact-name "raw139-d0-$sibling-certified" --provenance-input "$base/$archive" --provenance-input "$common/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneRA/blockcert.py" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneLA/scan.py" "${extra_args[@]}" | tee "$work/log"
