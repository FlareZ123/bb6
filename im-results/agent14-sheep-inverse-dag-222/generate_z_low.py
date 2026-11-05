from pathlib import Path
import os, fcntl, tempfile

ROOT = Path(__file__).resolve().parent
P = 122472
ROWS = {
    1:(5,4,1), 3:(17,8,1), 4:(243,162,1), 5:(5,4,1),
    6:(243,162,1), 7:(257,16,2), 8:(19,18,1), 9:(41,20,5),
    10:(243,162,1), 11:(17,8,1), 12:(243,162,1), 13:(5,4,1),
    14:(729,486,1), 15:(65537,32,4), 16:(243,162,1),
    17:(5,4,1),
}

def generate(rows):
    out = [
        "import Sheep31104ZLowPeriod",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
        "set_option exponentiation.threshold 100000",
        "namespace Sheep31104ZLow",
    ]
    for a, (m, p, q) in rows.items():
        K = 6966*a + 29669
        M = 3483*((1 << (a+1))+1)
        assert pow(2,p,m)==1 and (P*q)%p==0 and M%m==0
        assert all(pow(2,31115+P*t,m)!=K%m for t in range(q))
        cases = " ∨ ".join(f"t={i}" for i in range(q))
        phase_proofs = "\n".join(
            f"    · rw [Sheep31104ZLowPeriod.pow_mod_remainder {m} {p} "
            f"(31115+122472*{t}) (by decide) (by decide) (by decide)]\n"
            f"      decide"
            for t in range(q)
        )
        out.append(f'''/-- Every k excludes generic source valuation a={a}, modulo {m}. -/
theorem a{a}_mod (k : Nat) :
    2^(31115+122472*k)%{m} ≠ ({K}:Nat)%{m} := by
  apply Sheep31104ZLowPeriod.no_mod_eq_from_period {m} {p} 31115 122472 {q} {K}
  · decide
  · decide
  · decide
  · decide
  · intro t ht
    have hr : {cases} := by omega
    rcases hr with {' | '.join('rfl' for _ in range(q))}
{phase_proofs}

/-- Every k,v excludes the exact original-source generic equation at a={a}. -/
theorem a{a}_source (k v : Nat)
    (hs : 3483*(2^({a}+1)+1)*v + 2*{a}*3483 + 2*3483 + 2*16576 =
      2^(31115+122472*k) + 3*3483) : False := by
  have he : 2^(31115+122472*k) =
      (3483*(2^({a}+1)+1))*v + {K} := by
    have hp : (2:Nat)^({a}+1) = {1 << (a+1)} := by decide
    rw [hp] at hs ⊢
    omega
  have hc : 2^(31115+122472*k)%{m} = {K}%{m} := by
    rw [he,Nat.add_mod]
    have hz : ((3483*(2^({a}+1)+1))*v)%{m}=0 := by
      have hm : (3483*(2^({a}+1)+1))%{m}=0 := by decide
      rw [Nat.mul_mod,hm]
      simp
    rw [hz]
  exact (a{a}_mod k) hc
''')
    out.append("".join(f"#print axioms a{a}_source\n" for a in rows))
    out.append("end Sheep31104ZLow\n")
    return "\n".join(out)

if __name__ == "__main__":
    import sys
    key = int(sys.argv[1]) if len(sys.argv)>1 else 0
    rows = {key:ROWS[key]} if key else ROWS
    data = generate(rows)
    target = ROOT/("Sheep31104ZLow"+(str(key) if key else "")+".lean")
    with open(str(target)+".lock","a+b") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        fd,tmp = tempfile.mkstemp(dir=ROOT,prefix=target.name+".")
        try:
            with os.fdopen(fd,"w") as f:
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp,target)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
    print(target,len(data))
