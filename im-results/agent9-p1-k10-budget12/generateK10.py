"""Deterministic generator of five Lean parametric P1 shadow certificates.

All generated theorems are checked by the Lean kernel in the original-source
workflow. This generator is not trusted as an oracle by those theorems.
"""
from collections import deque
from pathlib import Path

CANDIDATES = [213,661,917,977,998]

def graph(q0: int, root: int) -> list[tuple[int,int,int]]:
    qstep=1024
    L0=16*q0+8+root
    z0=(12 if root==0 else 10)*q0+4
    states={(0,z0):qstep*(12 if root==0 else 10)}
    pending=deque([(0,z0)])
    while pending:
        m,z=pending.popleft()
        a=states[m,z]
        v=(z&-z).bit_length()-1
        assert v<10 and a%(2**(v+1))==0 and m<=12, (q0,root,m,z,a,v)
        for t in range(v+1):
            numerator=L0+m+t-1+z//2**t
            if numerator%2: continue
            child=(m+t+1,numerator//2)
            slope=(16*qstep+a//2**t)//2
            if child in states:
                assert states[child]==slope
                continue
            states[child]=slope
            pending.append(child)
    return sorted((m,z,a) for (m,z),a in states.items())

def make_files() -> None:
    directory=Path(__file__).parent/"generated"
    directory.mkdir(parents=True,exist_ok=True)
    assert len(CANDIDATES)==5
    for i,shard in enumerate("ABCDE"):
        qs=CANDIDATES[i:i+1]
        namespace=f"BB6.Agent9BatchK10{shard}"
        lines=["import Lean","set_option maxHeartbeats 20000000",
               "set_option maxRecDepth 8192",f"namespace {namespace}"]
        finals=[f"import Batch{shard}Arithmetic","import GenericCritical12K",
                f"namespace {namespace}"]
        for q in qs:
            for root in (0,1):
                states=graph(q,root)
                name=f"q{q}L{root}Nodes"
                lines += ["",f"def {name} (r : Nat) : List (Nat × Nat) :=",
                          "  ["+", ".join(f"({m},{z}+{a}*r)" for m,z,a in states)+"]"]
                for suffix,goal in [("positive","0<z"),("small","m≤12"),("no1024","¬1024 ∣ z")]:
                    lines += ["",f"theorem q{q}L{root}_{suffix} (r m z : Nat)",
                              f"    (h : (m,z) ∈ {name} r) : {goal} := by",
                              f"  simp only [{name},List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at h",
                              "  omega"]
                lines += ["",f"theorem q{q}L{root}_closed (r m z t v zp : Nat)",
                          f"    (hmem : (m,z) ∈ {name} r)",
                          "    (hdiv : z=2^t*v)",
                          f"    (hnext : 2*zp+1=16*({q}+1024*r)+{8+root}+m+t+v) :",
                          f"    (m+t+1,zp) ∈ {name} r := by",
                          f"  have hzpos : 0<z := q{q}L{root}_positive r m z hmem",
                          f"  have hnodiv : ¬1024 ∣ z := q{q}L{root}_no1024 r m z hmem",
                          "  have hvpos : 0<v := by",
                          "    by_cases h0 : v=0",
                          "    · simp [h0] at hdiv",
                          "      omega",
                          "    · omega",
                          "  have ht : t<10 := by",
                          "    by_cases hh : t<10",
                          "    · exact hh",
                          "    have hd : (2:Nat)^10 ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)",
                          "    have hd' : 1024 ∣ 2^t := by simpa using hd",
                          "    have hzz : 1024 ∣ z := by",
                          "      rcases hd' with ⟨a,ha⟩",
                          "      refine ⟨a*v, ?_⟩",
                          "      simp [hdiv, ha, Nat.mul_assoc, Nat.mul_comm]",
                          "    exact False.elim (hnodiv hzz)",
                          "  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7∨t=8∨t=9 := by omega",
                          f"  simp only [{name},List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem",
                          "  rcases hmem with "+" | ".join(["h"]*len(states)),
                          "  all_goals rcases h with ⟨hm,hz⟩",
                          "  all_goals simp only [hm,hz] at hdiv hnext ⊢",
                          "  all_goals rcases hcases with "+" | ".join(["h"]*10)+" <;> subst t <;>",
                          f"    simp_all [{name}] <;> omega",
                          "",f"#print axioms q{q}L{root}_closed"]
            finals += ["",f"/-- Genuine P1 blank-root gateway exclusion for q={q}+1024*r. -/",
                       f"theorem q{q}_critical_unreachable (r : Nat) :",
                       f"    ¬ BB6.Agent1.Reach 2",
                       f"      (14*2^(16*({q}+1024*r)+2)-2*(16*({q}+1024*r)+2)-10) := by",
                       f"  apply BB6.Agent9Generic12K.critical_unreachable_of_shadow12K ({q}+1024*r)",
                       f"    (by omega) (q{q}L0Nodes r) (q{q}L1Nodes r)",
                       f"  · simp [q{q}L0Nodes] <;> omega",
                       f"  · simp [q{q}L1Nodes] <;> omega",
                       f"  · exact q{q}L0_closed r",
                       f"  · exact q{q}L1_closed r",
                       f"  · exact q{q}L0_small r",
                       f"  · exact q{q}L1_small r",
                       f"  · exact q{q}L0_no1024 r",
                       f"  · exact q{q}L1_no1024 r",
                       "",f"#print axioms q{q}_critical_unreachable"]
        lines.append(f"end {namespace}")
        finals.append(f"end {namespace}")
        (directory/f"Batch{shard}Arithmetic.lean").write_text("\n".join(lines)+"\n")
        (directory/f"Batch{shard}Final.lean").write_text("\n".join(finals)+"\n")
        print(shard,qs,flush=True)

if __name__=="__main__":
    make_files()
