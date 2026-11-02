"""Reproducible B8/M32 Machine C Lean certificate; generated statements require kernel checking."""
import base64
import fcntl
import io
import os
from pathlib import Path
import re
import tarfile
import tempfile
from collections import deque

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[0]
BASE, MOD, N = 8, 32, 40

def q(x):
    return x if x < BASE else BASE + (x - BASE) % MOD

def enc(a, k, c):
    return (a*N+k)*N+c

def nxt(a, k, c):
    if c == 1: return a,k+1,0
    if c == 2: return None
    if c == 3: return a,k+2,1
    if c == 0:
        if a == 0: return 1,0,2*k+2
        if a == 1: return (5,0,1) if k == 0 else (2,2,2*k-1)
        return a-2,1,2*k+1
    if a == 0:
        return (2*k+2,2,c-3) if k % 2 == 0 else (2*k+3,0,c)
    return a-1,k+1,c-1

def graph():
    seen = bytearray(N**3)
    start = enc(5,0,1)
    queue = deque([start])
    seen[start] = 1
    edges = 0
    while queue:
        i = queue.popleft()
        a, k, c = i//(N*N), i//N%N, i%N
        for aa in ((a,a+MOD) if a>=BASE else (a,)):
            for kk in ((k,k+MOD) if k>=BASE else (k,)):
                for cc in ((c,c+MOD) if c>=BASE else (c,)):
                    t = nxt(aa,kk,cc)
                    if t is None: continue
                    edges += 1
                    j = enc(*map(q,t))
                    if not seen[j]:
                        seen[j] = 1
                        queue.append(j)
    assert (sum(seen),edges) == (31570,189834)
    for a in range(N):
        for k in range(N):
            for c in range(N):
                if not seen[enc(a,k,c)]: continue
                for aa in ((a,a+MOD) if a>=BASE else (a,)):
                    for kk in ((k,k+MOD) if k>=BASE else (k,)):
                        for cc in ((c,c+MOD) if c>=BASE else (c,)):
                            t = nxt(aa,kk,cc)
                            assert t is None or seen[enc(*map(q,t))]
    assert not seen[enc(1,q(20),0)]
    return seen

def write(path, content):
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile("w",encoding="utf-8",dir=path.parent,delete=False) as f:
        f.write(content)
        tmp = f.name
    os.replace(tmp,path)

def old_sources():
    src = REPO / "im-results/agent43-c-quotient-kernel/c-cert16.tar.xz.b64"
    with tarfile.open(fileobj=io.BytesIO(base64.b64decode(src.read_text().strip())),mode="r:xz") as tf:
        return {Path(m.name).name:tf.extractfile(m).read().decode("utf-8")
                for m in tf.getmembers() if m.isfile()}

def gen():
    with (ROOT/".generator.lock").open("w") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        src = old_sources()
        seen = graph()
        rows = [sum(int(seen[enc(a,k,c)])<<c for c in range(N))
                for a in range(N) for k in range(N)]
        base = src["CCert16Pure.lean"]
        base = base.replace("def modulus : Nat := 16","def modulus : Nat := 32")
        base = base.replace("def N : Nat := 24","def N : Nat := 40")
        base, count = re.subn(r"def rows : Array Nat := #\[[^]]*\]",
                              "def rows : Array Nat := #["+", ".join(map(str,rows))+"]",base)
        assert count == 1
        write(ROOT/"CCert32Pure.lean",base)
        for a in range(N):
            proofs = "\n".join(f"theorem prow32_{a}_{k} : checkRow {a} {k} = true := by decide +kernel" for k in range(N))
            ors = " ∨ ".join(f"k={k}" for k in range(N))
            destruct = " | ".join(["rfl"]*N)
            cases = "\n".join(f"  · exact prow32_{a}_{k}" for k in range(N))
            block = f"""import CCert32Pure
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CCert
{proofs}
theorem pblock32_{a} : checkBlock {a} = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hlt : k < 40 := by simpa [N] using (List.mem_range.mp hk)
  have hc : {ors} := by omega
  rcases hc with {destruct}
{cases}
end CCert
"""
            write(ROOT/f"P32Block{a}.lean",block)
        imports = "\n".join("import P32Block"+str(i) for i in range(N))
        ors = " ∨ ".join(f"a={i}" for i in range(N))
        destruct = " | ".join(["rfl"]*N)
        cases = "\n".join(f"  · exact pblock32_{i}" for i in range(N))
        oldglobal = src["CGlobal16.lean"]
        start = oldglobal.index("theorem check_state_verified")
        body = oldglobal[start:].replace("end CCert", "end CCert")
        global_src = f"""{imports}
import Lean.Elab.Tactic.Omega
namespace CCert
def closed2 : Bool := (List.range N).all checkBlock
theorem closed2_verified : closed2 = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have halt : a < 40 := by simpa [N] using (List.mem_range.mp ha)
  have hc : {ors} := by omega
  rcases hc with {destruct}
{cases}

{body}
"""
        write(ROOT/"CGlobal32.lean",global_src)
        write(ROOT/"CQuotientSound32.lean",
              src["CQuotientSound16.lean"].replace("16","32").replace("24","40"))
        write(ROOT/"CMapIf32.lean",
              src["CMapIf16.lean"].replace("CQuotientSound16","CQuotientSound32").replace("24","40"))
        write(ROOT/"CFull32.lean",
              src["CFull16.lean"].replace("CMapIf16","CMapIf32").replace("CGlobal16","CGlobal32"))
        exclusions = """import CFull32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CCert
theorem low_twenty_absent (k : Nat) (hk : k % 32 = 20) :
    seen (q 1) (q k) (q 0) = false := by
  have hq : q k = q 20 :=
    q_congr_big k 20 (by omega) (by omega) (by omega)
  rw [hq]
  decide

theorem low_twenty_unreachable (k : Nat) (hk : k % 32 = 20) :
    ¬ Reach (1,k,0) := by
  intro h
  have hs := reachable_seen h
  rw [low_twenty_absent k hk] at hs
  cases hs
#print axioms low_twenty_unreachable
end CCert
"""
        write(ROOT/"CExclusions32.lean",exclusions)
        bridge = """import CExclusions32
import CLine
namespace CCert
theorem published_next_agrees32 (s : S) : nextC s = BB6CLine.nextC s := by
  rfl
theorem source_reachable_embeds32 {s : S} (h : BB6CLine.Reach s) : Reach s := by
  induction h with
  | init => exact Reach.init
  | next s t _ ht ih =>
      exact Reach.step ih (by rw [published_next_agrees32]; exact ht)
theorem original_low_twenty_unreachable (k : Nat) (hk : k % 32 = 20) :
    ¬ BB6CLine.Reach (1,k,0) := by
  intro h
  exact low_twenty_unreachable k hk (source_reachable_embeds32 h)
#print axioms original_low_twenty_unreachable
end CCert
"""
        write(ROOT/"CSourceBridge32.lean",bridge)
        print(f"B8/M32: {sum(seen)} / {N**3} states; 189834 edges; source modules generated")

if __name__ == "__main__":
    gen()
