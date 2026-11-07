from pathlib import Path
from math import gcd
import os, fcntl, tempfile, sys
ROOT=Path(__file__).resolve().parent
P=40824

def order(m):
 x=2%m
 for n in range(1,100001):
  if x==1:return n
  x=(x*2)%m
 raise AssertionError(('long order',m))

def mod_for(h,a):
 if a in (1,5,13):return 5
 if a in (3,11):return 17
 if a==2:return 3**(h+1)
 if a==4:return 11 if h==6 else 3**(h+1)
 if a==6:return 43 if h!=3 else None
 if a==7:return 257
 if a==8:return 3**(h+1) if h<=1 else 19
 if a==9:return 41
 if a==10:return 683 if h==6 else 3**(h+1)
 if a==12:return 2187 if h==6 else 2731
 if a==14:return 2187 if h==6 else 3**(h+1)
 raise AssertionError((h,a))

def gen(h):
 D=3**h; Nexp=31105+h; C=3*D; pow2=2**(h+1)
 out=['import Sheep31104ZLowPeriod','set_option maxRecDepth 32768','set_option maxHeartbeats 0','set_option exponentiation.threshold 100000',f'namespace Sheep31104RootLow{h}']
 for a in range(1,15):
  m=mod_for(h,a)
  if m is None:continue
  M=D*(2**(a+1)+1)
  N=2*a*D+pow2
  K=(N-C)%m
  p=order(m)
  q=p//gcd(p,P)
  assert M%m==0 and pow(2,p,m)==1 and (P*q)%p==0
  assert all(pow(2,Nexp+P*t,m)!=K for t in range(q)),(h,a,m,p,q)
  cases=' ∨ '.join(f't={i}' for i in range(q))
  phase_proofs='\n'.join(f'    · rw [Sheep31104ZLowPeriod.pow_mod_remainder {m} {p} ({Nexp}+40824*{t}) (by decide) (by decide) (by decide)]\n      decide' for t in range(q))
  out += [f'''theorem a{a}_mod (k : Nat) :
    2^({Nexp}+40824*k)%{m} ≠ {K}%{m} := by
  apply Sheep31104ZLowPeriod.no_mod_eq_from_period {m} {p} {Nexp} 40824 {q} {K}
  · decide
  · decide
  · decide
  · decide
  · intro t ht
    have hr : {cases} := by omega
    rcases hr with {' | '.join('rfl' for _ in range(q))}
{phase_proofs}

theorem a{a}_source (k v : Nat)
    (hs : {D}*(2^({a}+1)+1)*v + 2*{a}*{D} + 2^({h}+1) =
      2^((31104+40824*k)+{h}+1) + 3*{D}) : False := by
  have he : (31104+40824*k)+{h}+1={Nexp}+40824*k := by omega
  rw [he] at hs
  have hs' : {M}*v+{N}=2^({Nexp}+40824*k)+{C} := by
    have hp : (2:Nat)^({a}+1)={2**(a+1)} := by decide
    rw [hp] at hs
    omega
  have hmod : (2^({Nexp}+40824*k)+{C})%{m} = {N}%{m} := by
    calc
      (2^({Nexp}+40824*k)+{C})%{m} = ({M}*v+{N})%{m} :=
        congrArg (fun z:Nat=>z%{m}) hs'.symm
      _ = {N}%{m} := by simp [Nat.add_mod,Nat.mul_mod]
  have hr : 2^({Nexp}+40824*k)%{m}={K}%{m} := by
    rw [Nat.add_mod] at hmod
    have hlt : 2^({Nexp}+40824*k)%{m}<{m} :=
      Nat.mod_lt _ (by decide)
    omega
  exact (a{a}_mod k) hr
''']
 out.append(''.join(f'#print axioms a{a}_source\n' for a in range(1,15) if mod_for(h,a) is not None))
 out.append(f'end Sheep31104RootLow{h}\n')
 return '\n'.join(out)

if __name__=='__main__':
 h=int(sys.argv[1]) if len(sys.argv)>1 else 3
 s=gen(h)
 target=ROOT/f'Sheep31104RootLow{h}.lean'
 with open(str(target)+'.lock','a+b') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  fd,tmp=tempfile.mkstemp(dir=ROOT)
  try:
   with os.fdopen(fd,'w') as f:
    f.write(s)
    f.flush()
    os.fsync(f.fileno())
   os.replace(tmp,target)
  finally:
   if os.path.exists(tmp):os.unlink(tmp)
 print(target,len(s))
