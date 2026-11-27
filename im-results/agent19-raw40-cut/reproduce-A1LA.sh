#!/usr/bin/env bash
# Compile the nine A1=1LA quotient children and their attained weighted max.
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to accepted Canonical77 dependencies (artifact 14997966221)}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version
check() { local f="$1"; "$LEAN" -j1 -o "${f%.lean}.olean" "$f"; }
for m in CanonicalPartial Raw40Nores Raw40MorePumps Raw40A1LABase Raw40A1LAUnaryGrammar; do check "$m.lean"; done
(cd ../agent32-raw59; "$LEAN" -j1 -o "$root/FastBiDFA.olean" FastBiDFA.lean)
dirs=()
for c in 0LC 0LE 0RC 0RE 1LB 1LC 1LE 1RC 1RE; do
    python3 prepare_a1la.py "$c"
    dirs+=("$root/a1la/$c/shards")
done
# All compact graph modules import only FastBiDFA. Compile them in parallel,
# using distinct log files so a failed module is immediately identifiable.
python3 - <<'PY'
import concurrent.futures,os,pathlib,subprocess
root=pathlib.Path.cwd()
fs=sorted(root.glob('Raw40A1LA*Compact*.lean'))
def check(f):
    p=subprocess.run([os.environ['LEAN'],'-j1','-o',str(f.with_suffix('.olean')),f.name],
                     cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    f.with_suffix('.log').write_text(p.stdout)
    print(f.name,p.returncode,p.stdout,flush=True)
    assert p.returncode==0 and 'sorryAx' not in p.stdout, f
with concurrent.futures.ThreadPoolExecutor(max_workers=int(os.environ['WORKERS'])) as pool:
    list(pool.map(check,fs))
PY
python3 build_manifests.py "${dirs[@]}"
for d in "${dirs[@]}"; do export LEAN_PATH="$LEAN_PATH:$d"; done
check Raw40A1LA.lean
