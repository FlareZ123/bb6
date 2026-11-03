"""Reproduce all source-verified r138 child residues, cases, and final Lean theorem.

Run after reconstruct_root138.py and reconstruct_child138_high.py.
Outputs use locked atomic replacement and are checked against the hashes of
the original Lean 4.36.0-rc2 kernel-compiled sources.
"""
from pathlib import Path
from filelock import FileLock
from math import gcd
import hashlib
import tempfile
import os

root = Path(__file__).resolve().parent
nodes = [("child1", 15, 2, 141, (8, 10, 12, 14)),
         ("child2", 81, 68, 143, (11, 13))]

def save(name, source):
    path = root / name
    with FileLock(str(path) + ".lock"):
        fd, temporary = tempfile.mkstemp(dir=root, prefix="." + name + ".")
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as file:
                file.write(source)
                file.flush()
                os.fsync(file.fileno())
            os.replace(temporary, path)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)
    print("Generated:", name, len(source))

def order(n):
    x, p = 2 % n, 1
    while x != 1:
        x = x * 2 % n
        p += 1
        if p > 1000000:
            raise ValueError(n)
    return p

base = (root / "Sheep138LowResidues.lean").read_text()
start = base.index("/-- Complete all-k parity-correct inverse residue exclusion")
s = base[:start].replace("namespace Sheep138LowResidues", "namespace Sheep138ChildLowResidues")
s = s.replace("set_option exponentiation.threshold 50000", "set_option exponentiation.threshold 100000")
meta = []
for name,d,c,n0,limits in nodes:
    for h,A in enumerate(limits):
        D=d*3**h
        for a in range(1,A):
            T=D*(2**(a+1)+1)
            B=2*D*a-3*D+2**(h+1)*(d+c)
            C=2*T-B if B>=0 else -B
            p=order(T)
            q=p//gcd(p,4860)
            R=n0+h+1
            meta.append((name,h,a,T,B,C,p,q,R))
            s+=f"""/-- Uniform parity-correct {name} h={h},a={a} modular exclusion. -/
theorem {name}_{h}_{a} (k : Nat) :
    (2^({R}+4860*k)+{C}) % {2*T} ≠ {T} := by
  apply no_twice_from_period {T} {p} {R} 4860 {q} {C} {T}
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro t ht
"""
            s+='    have hcases : '+' ∨ '.join(f't={i}' for i in range(q))+' := by omega\n'
            if q==1: s+='    subst t\n'
            else: s+='    rcases hcases with '+' | '.join(f'h{i}' for i in range(q))+'\n'
            for i in range(q):
                exponent=R+4860*i;b=(exponent-1)%p+1;w=(exponent-b)//p
                indent='    ' if q==1 else '      '
                if q>1: s+='    · subst t\n'
                s+=indent+f'change (2^{exponent}+{C})%{2*T} ≠ {T}\n'
                s+=indent+f'have he : 2^{exponent}%{2*T}=2^{b}%{2*T} := by\n'
                s+=indent+f'  rw [show {exponent}={b}+{p}*{w} by decide]\n'
                s+=indent+f'  all_goals exact pow_mod_twice_period {T} {p} {b} {w} (by decide) (by decide) (by decide)\n'
                s+=indent+f'have hc : (2^{exponent}+{C})%{2*T}=(2^{b}+{C})%{2*T} := by\n'
                s+=indent+'  rw [Nat.add_mod,he,←Nat.add_mod]\n'
                s+=indent+'rw [hc]\n'
                s+=indent+'decide\n'
            s+='\n'
s+='\n'.join(f'#print axioms {name}_{h}_{a}' for name,h,a,*_ in meta)+'\nend Sheep138ChildLowResidues\n'
save("Sheep138ChildLowResidues.lean",s)

s="""import Sheep138ChildLowResidues
import Sheep138RootParents
set_option maxHeartbeats 2000000

namespace Sheep138ChildLowCases

"""
meta=[]
for name,d,c,n0,limits in nodes:
    for h,A in enumerate(limits):
        D=d*3**h
        for a in range(1,A):
            T=D*(2**(a+1)+1)
            B=2*D*a-3*D+2**(h+1)*(d+c)
            C=2*T-B if B>=0 else -B
            R=n0+h+1
            meta.append((name,h,a))
            s+=f"""/-- Source generic {name} h={h},a={a} violates all-k residue. -/
theorem no_{name}_{h}_{a} (k v u : Nat) (hodd : v%2=1)
    (hy : {d}*(1+3^{h}*u)+{c}=2^({n0}+4860*k))
    (hz : 2*(1+2^{h}*u)+1=(2^({a}+1)+1)*v+2*{a}) : False := by
  have hp : 2^({R}+4860*k)=2^({n0}+4860*k)*{2**(h+1)} := by
    rw [show {R}+4860*k=({n0}+4860*k)+{h+1} by omega, Nat.pow_add]
    all_goals decide
"""
            if B>=0:
                s+=f"""  have he : {T}*v+{B}=2^({R}+4860*k) := by
    rw [hp]
    omega
  have hmod : (2^({R}+4860*k)+{C})%{2*T}={T} :=
    Sheep138RootParents.odd_mod {T} {B} {C} ({R}+4860*k) v
      (by decide) (by decide) hodd he
"""
            else:
                s+=f"""  have he : {T}*v=2^({R}+4860*k)+{C} := by
    rw [hp]
    omega
  have hmod : (2^({R}+4860*k)+{C})%{2*T}={T} :=
    Sheep138RootParents.odd_mod_plus {T} {C} ({R}+4860*k) v
      (by decide) hodd he
"""
            s+=f"""  exact Sheep138ChildLowResidues.{name}_{h}_{a} k hmod

"""
s+='\n'.join(f'#print axioms no_{name}_{h}_{a}' for name,h,a in meta)+'\nend Sheep138ChildLowCases\n'
save("Sheep138ChildLowCases.lean",s)

s="""import Sheep138ChildLowCases
import Sheep138ChildFinite
import Sheep138RootTwoChildren

namespace Sheep138FullClass

"""
for name,d,c,n0,limits in nodes:
    s+=f"""/-- Complete source-exact all-k exclusion of the {name} rational child. -/
theorem {name}_unreachable (k y : Nat)
    (ht : {d}*y+{c}=2^({n0}+4860*k))
    (hr : SheepEven.EvenReach 10 y) : False := by
  obtain ⟨x,a,h,v,u,hreach,ha,hv,hodd,hu,hx,hy,hz,hcases⟩ :=
    Sheep138ChildFinite.{name}_finite k y ht hr
  have htarget : {d}*(1+3^h*u)+{c}=2^({n0}+4860*k) := by rw [←hy]; exact ht
"""
    s+='  rcases hcases with '+' | '.join(f'⟨hh{h},hal{h}⟩' for h in range(len(limits)))+'\n'
    for h,A in enumerate(limits):
        s+='  · subst h\n'
        s+='    have a_cases : '+' ∨ '.join(f'a={a}' for a in range(1,A))+' := by omega\n'
        s+='    rcases a_cases with '+' | '.join(f'ha{a}' for a in range(1,A))+'\n'
        for a in range(1,A):
            s+=f"""    · subst a
      exact Sheep138ChildLowCases.no_{name}_{h}_{a} k v u hodd htarget hz
"""
    s+='\n'
s+="""/-- Certified exclusion of the entire previously written infinite
r=138+4860k Sheep halting gate family, for every k simultaneously,
using actual original even-orbit reachability and no unverified axioms. -/
theorem root138_unreachable (k : Nat) :
    ¬ SheepEven.EvenReach 10 (2^(138+4860*k)) := by
  intro hr
  rcases Sheep138RootTwoChildren.root_reaches_one_child k hr with
      ⟨x,hreach,hchild⟩ | ⟨x,hreach,hchild⟩
  · exact child1_unreachable k x hchild hreach
  · exact child2_unreachable k x hchild hreach

#print axioms root138_unreachable
#print axioms child1_unreachable
#print axioms child2_unreachable
end Sheep138FullClass
"""
save("Sheep138FullClass.lean",s)

EXPECTED = {
    "Sheep138ChildLowResidues.lean": "7ce461415631229b433c9b0951081f5b4d7d2e2159e5f408857628d4b51f242a",
    "Sheep138ChildLowCases.lean": "caf6d6fd00e8ecdf8fd668800d4f9622073f5af9f9020ffd0a5ce5b34dc03339",
    "Sheep138FullClass.lean": "6312806560d958861720f016d9fd048faec7163f9fb1dc3d078fde62e72218dd",
}
for name, expected in EXPECTED.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"Generated {name} differs: {actual} expected {expected}")
print("Verified all three Lean-source SHA256 checksums")
