from collections import deque
import sys
from pathlib import Path
import os
import tempfile
from filelock import FileLock

s=int(sys.argv[1])
step=64;Q=64

def v2(n):return 999 if n==0 else (n&-n).bit_length()-1
start=(0,8*s+8,8*Q)
nodes={start};queue=deque([start]); L=16*s+19; Ecoef=16*Q
while queue:
 m,z,e=queue.popleft()
 assert z>0 and v2(e)>v2(z),(s,(m,z,e),v2(e),v2(z))
 for t in range(v2(z)+1):
  v=z//2**t
  a=L+m+t+v
  assert (Ecoef+e//2**t)%2==0
  if a%2==0:continue
  child=(m+t+1,(a-1)//2,(Ecoef+e//2**t)//2)
  if child not in nodes:
   nodes.add(child);queue.append(child)
nodes=sorted(nodes);index={p:i for i,p in enumerate(nodes)}
assert max(m for m,z,e in nodes)<=8
assert 0<=s<64
for m,z,e in nodes:
 assert v2(e)>v2(z)
 assert v2(z)<(9 if s==31 else 8)
expr=' ∨\n'.join(f'  (m = {m} ∧ z = {z} + {e}*r)' for m,z,e in nodes)
proof=' | '.join('⟨hm, hz⟩' for _ in nodes)
branches=[]
for m,z,e in nodes:
 steps=[]
 for t in range(9 if s==31 else 8):
  lines=['    ·']
  if z%(1<<t)!=0:
   lines.append('      omega')
  else:
   num=L+m+t+z//(1<<t)
   if num%2==0:
    lines.append('      omega')
   else:
    new=(m+t+1,(num-1)//2,(Ecoef+e//(1<<t))//2)
    assert new in index,(s,(m,z,e),t,new)
    h=index[new]
    lines.extend([f'      have hmp : m\' = {new[0]} := by omega',f'      have hzp : z\' = {new[1]} + {new[2]}*r := by omega',f'      exact {"Or.inr ("*h}{"Or.inl " if h < len(nodes)-1 else ""}⟨hmp, hzp⟩{ ")"*h}'])
  steps.append('\n'.join(lines))
 branches.append('  · rcases htcase with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7\n    all_goals subst t\n'+ '\n'.join(steps))
code=f'''import N14GenericDecision
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace Agent23N14Residue{s}
open Agent23N14Generic

def State (r m z : Nat) : Prop :=
{expr}

private theorem no256 (r m z : Nat) (h : State r m z) : ¬256 ∣ z := by
  intro hd
  obtain ⟨v,hv⟩ := hd
  rcases h with {proof}
  all_goals omega

private theorem depth_bound (r m z t : Nat) (h : State r m z)
    (hd : 2^t ∣ z) : t < 8 := by
  by_cases ht : t < 8
  · exact ht
  have hle : 8≤t := by omega
  have hp : (2:Nat)^8 ∣ 2^t := Nat.pow_dvd_pow 2 hle
  have h256 : 256 ∣ z := Nat.dvd_trans (by simpa using hp) hd
  exact False.elim ((no256 r m z h) h256)

theorem state_root (r : Nat) : State r 0 (8*(64*r+{s})+8) := by
  exact Or.inl ⟨rfl, by omega⟩

theorem state_step (r m z m' z' t v : Nat)
    (h : State r m z)
    (hdiv : z=2^t*v)
    (hm : m'=m+t+1)
    (hnext : 2*z'+1=16*(64*r+{s})+19+m+t+v) :
    State r m' z' := by
  have ht : t<8 := depth_bound r m z t h ⟨v,hdiv⟩
  have htcase : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7 := by omega
  rcases h with {proof}
  all_goals subst m
  all_goals subst z
{chr(10).join(branches)}

/-- Concrete finite list of all scalar odd inverse shadows. -/
def nodes (r : Nat) : List (Nat × Nat) :=
  [{',\n   '.join(f'({m},{z}+{e}*r)' for m,z,e in nodes)}]

theorem mem_iff (r m z : Nat) : ((m,z) ∈ nodes r) ↔ State r m z := by
  simp only [nodes, State, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]

theorem nodes_root (r : Nat) : (0,8*(64*r+{s})+8) ∈ nodes r :=
  (mem_iff r 0 (8*(64*r+{s})+8)).mpr (state_root r)

theorem nodes_small (r m z : Nat) (h : (m,z) ∈ nodes r) : m ≤ 8 := by
  have hs := (mem_iff r m z).mp h
  rcases hs with {proof}
  all_goals omega

theorem nodes_no256 (r m z : Nat) (h : (m,z) ∈ nodes r) : ¬256 ∣ z :=
  no256 r m z ((mem_iff r m z).mp h)

theorem nodes_closed (r m z t v zp : Nat)
    (h : (m,z)∈nodes r)
    (hd : z=2^t*v)
    (hn : 2*zp+1=16*(64*r+{s})+19+m+t+v) :
    (m+t+1,zp)∈nodes r := by
  apply (mem_iff r (m+t+1) zp).mpr
  exact state_step r m z (m+t+1) zp t v ((mem_iff r m z).mp h)
    hd rfl hn

def certificate (r : Nat) : Certificate (64*r+{s}) :=
  ⟨nodes r, nodes_root r, nodes_closed r, nodes_small r, nodes_no256 r⟩

theorem critical_unreachable (r : Nat) :
    ¬BB6.Agent1.Reach 2
      (14*2^(16*(64*r+{s})+14)-2*(16*(64*r+{s})+14)-10) :=
  critical_unreachable_of_certificate (64*r+{s}) (by omega) (certificate r)

#print axioms state_step
#print axioms critical_unreachable
end Agent23N14Residue{s}
'''
if s==0:
 code=code.replace('theorem critical_unreachable (r : Nat) :','theorem critical_unreachable (r : Nat) (hr : 1≤r) :')
if s==31:
 code=code.replace("import N14GenericDecision", "import N14K9Decision")
 code=code.replace("Agent23N14Generic", "Agent23N14K9")
 code=code.replace("no256", "no512")
 code=code.replace("¬256 ∣ z", "¬512 ∣ z")
 code=code.replace("have hle : 8≤t", "have hle : 9≤t")
 code=code.replace("(2:Nat)^8 ∣ 2^t", "(2:Nat)^9 ∣ 2^t")
 code=code.replace("have h256 : 256 ∣ z", "have h512 : 512 ∣ z")
 code=code.replace("h256)", "h512)")
 code=code.replace("t < 8", "t < 9")
 code=code.replace("t<8", "t<9")
 code=code.replace("t=7 := by omega", "t=7∨t=8 := by omega")
 code=code.replace("h5 | h6 | h7", "h5 | h6 | h7 | h8")
target=Path(sys.argv[2]) if len(sys.argv)>2 else Path(__file__).parent/'generated'/f'N14Residue{s}.lean'
target.parent.mkdir(parents=True,exist_ok=True)
with FileLock(str(target)+'.lock'):
 with tempfile.NamedTemporaryFile('w',dir=target.parent,delete=False,encoding='utf-8') as fp:
  fp.write(code)
  tempname=fp.name
 os.replace(tempname,target)
print(s,len(nodes),len(code),'maxcost',max(m for m,z,e in nodes),'output',target)
