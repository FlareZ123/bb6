"""Reconstruct the kernel-checked 71 low-valuation Sheep 138 inverse exclusions.

Requires uniform_138.py in this directory, Python 3.10+, and filelock.
Generation is deterministic. The 181,253-byte Lean source has SHA256
5f9c2737aa168b3eee0ec33e81d078f8afdb3151f3f12508e721019b756a94eb.
Compile after EvenPeriod.lean, using Lean 4.36.0-rc2.
"""
from pathlib import Path
from math import gcd
import uniform_138 as s

R=138;M=4860
nodes=[s.ROOT,s.P1,s.P2]
lines=['import EvenPeriod', 'set_option maxRecDepth 200000','set_option exponentiation.threshold 200000','set_option maxHeartbeats 0', 'namespace SheepEvenCert', '']
checked=[]
for i,node in enumerate(nodes):
 for h,A in enumerate(node.limits):
  D=node.d*3**h;C=(1<<h)*(node.b-node.d)+D
  assert s.cycle_modulus(D)==1 and (pow(2,R+node.s,D)+node.b-node.d)%D==0
  for a in range(1,A):
   den=D*((1<<(a+1))+1);b1=2*C-D*(2*a-1)
   B=b1%(2*den);base=R+node.s+h+1
   p=s.period2(den);q=p//gcd(p,M)
   assert pow(2,p,den)==1 and (M*q)%p==0
   valid=[k for k in range(q) if (pow(2,base+M*k,2*den)+B)%(2*den)==den]
   if valid:
    assert (i,h,a) in [(0,1,1),(0,2,2)],(i,h,a,valid)
    continue
   name=f'node{i}_h{h}_a{a}_excluded'
   checked.append(name)
   lines+= [f'/-- Uniform modular exclusion: symbolic Sheep inverse node {i}, h={h}, a={a}. -/',
            f'theorem {name} (k : Nat) :',
            f'    (2^({base}+4860*k)+{B})%{2*den} ≠ {den} := by',
            f'  have hp : 2^{p}%{den}=1 := by decide',
            f'  apply no_twice_value_from_period {den} {p} {base} 4860 {q} {B} {den}',
            '  · decide',
            '  · decide',
            '  · decide',
            '  · exact hp',
            '  · decide',
            '  · intro t ht']
   ors=' ∨ '.join(f't={z}' for z in range(q)) if q>1 else 't=0 ∨ False'
   lines += [f'    have hc : {ors} := by omega']
   lines+=['    rcases hc with '+'|'.join(f'h{z}' for z in range(q))+(' | hFalse' if q==1 else '')]
   for t in range(q):
    e=base+M*t;rem=(e-1)%p+1;quot=(e-rem)//p
    assert rem>=1 and e==rem+p*quot and (pow(2,rem,2*den)+B)%(2*den)!=den
    lines += ['    · subst t',
              f'      have hexp : {base}+4860*{t}={rem}+{p}*{quot} := by decide',
              f'      have hmod : 2^({base}+4860*{t})%{2*den}=2^{rem}%{2*den} := by',
              '        calc',
              f'          2^({base}+4860*{t})%{2*den}=2^({rem}+{p}*{quot})%{2*den} :=',
              f'            congrArg (fun x => 2^x%{2*den}) hexp',
              f'          _=2^{rem}%{2*den} :=',
              f'            pow_mod_twice_period {den} {p} {rem} {quot} (by decide) hp (by decide)',
              f'      have hconst : (2^{rem}+{B})%{2*den}≠{den} := by decide',
              '      intro contra',
              '      apply hconst',
              f'      have hcalc : (2^({base}+4860*{t})+{B})%{2*den}=',
              f'          (2^{rem}+{B})%{2*den} := by',
              '        rw [Nat.add_mod,hmod,←Nat.add_mod]',
              '      rw [←hcalc]',
              '      exact contra',
              '']
   if q==1: lines+=['    · contradiction']
lines +=['#print axioms '+v for v in checked]
lines+=['end SheepEvenCert']
source='\n'.join(lines)+'\n'


def atomic_write(output: Path, source: str) -> None:
    import os
    from tempfile import NamedTemporaryFile
    from filelock import FileLock
    with FileLock(str(output)+'.lock'):
        with NamedTemporaryFile('w', encoding='utf-8', dir=output.parent,
                                prefix='.Low138.', suffix='.tmp', delete=False) as handle:
            temp=Path(handle.name)
            handle.write(source)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp,output)


if __name__ == '__main__':
    import hashlib
    assert len(checked)==71
    assert hashlib.sha256(source.encode('utf-8')).hexdigest()==(
        '5f9c2737aa168b3eee0ec33e81d078f8afdb3151f3f12508e721019b756a94eb')
    atomic_write(Path(__file__).with_name('Low138.lean'),source)
    print('generated',len(checked),'theorems;',len(source.encode('utf-8')),'bytes')
