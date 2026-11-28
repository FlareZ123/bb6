#!/usr/bin/env bash
# Rebuild all nine Raw40 A1=0RB quotient children and exact weighted maximum.
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to accepted Canonical77 dependencies (artifact 14997966221)}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version

check() {
  local f="$1"
  "$LEAN" -j1 -o "${f%.lean}.olean" "$f"
}

for m in CanonicalPartial Raw40Nores Raw40A0RBBase Raw40ZeroRBCounters Raw40ZeroRBCycles; do
  check "$m.lean"
done

cp ../agent46-raw13-cut/Agent46AutoPump.lean Agent46AutoPump.lean
check Agent46AutoPump.lean

# The two large n-gram witnesses are regenerated from the checker source,
# rather than trusted as committed generated Lean.
python3 build_a0rb_ngrams.py 655 515
check Raw40ZeroRBNGram655.lean
check Raw40ZeroRBNGram515.lean

dirs=()
for c in 0LA 0LE 0RC 0RE 1LB 1LC 1LE 1RC 1RE; do
  python3 prepare_a0rb.py "$c"
  dirs+=("$root/a0rb/$c/shards")
done

# prepare_a0rb.py emits one AutoPump module for every child with pump rows.
python3 - <<'PY'
import concurrent.futures, os, pathlib, subprocess
root=pathlib.Path.cwd()
fs=sorted(root.glob('Raw40ZeroRB*Pump.lean'))
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

# The family lower bound is attained in the 0LE child.
check "$root/a0rb/0LE/shards/Raw40C0RB0LEExact.lean"
check Raw40A0RB.lean
