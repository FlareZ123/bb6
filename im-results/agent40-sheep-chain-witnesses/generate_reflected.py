"""Generate source-classification Lean proofs using trusted kernel reflection."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
from reflected_branches import CONES,branch,title
import os
import sys

def generate():
    z=['import SheepEvenInverseAlgebra','import SheepHCases',
       'import SheepHighCases','import SheepPeriodicGate',
       'import GenericHighNoParent','',
       'set_option maxRecDepth 16384','set_option maxHeartbeats 0','',
       'namespace SheepReflectedGeneric','']
    for r,nodes in CONES.items():
        for i,(s,b,d,limits) in enumerate(nodes):
            for h,amax in enumerate(limits):
                z.extend(branch(r,i,s,b,d,h,amax))
    for r,nodes in CONES.items():
        for i,(s,b,d,limits) in enumerate(nodes):
            n=r+s
            c=-b
            H=len(limits)
            z += [f'theorem generic_r{r}_n{i} (k x y : Nat)',
               '    (edge : SheepEvenInverseAlgebra.GenericEdge x y)',
               f'    (hy : {d}*y+{c}=2^({n}+4860*k)) : {title(r,i)} := by',
               '  obtain ⟨a,h,v,u,ha,hv,hodd,hu,hx,hform,heq⟩ :=',
               f'    SheepEvenInverseAlgebra.generic_inverse_negative x y {d} {c} ({n}+4860*k) edge hy',
               f'  have hh : h<{H} := SheepHBound.h_bounded y {d} {c} ({n}+4860*k) {H} h u hy hform (by',
               f'    simpa using SheepHCases.hstop_r{r}_n{i} k)',
               f'  have hc : '+'∨'.join(f'h={h}' for h in range(H))+' := by omega',
               '  rcases hc with '+'|'.join(f'h{h}' for h in range(H))]
            for h,_ in enumerate(limits):
                D=d*3**h
                E=2**(h+1)*(d+c)
                base=n+h+1
                shift=3*D
                z += ['  · subst h',
                   f'    have heqRow : {D}*(2^(a+1)+1)*v+2*a*{D}+{E} = 2^({base}+4860*k)+{shift} := by',
                   f'      have hexp : {n}+4860*k+{h}+1={base}+4860*k := by omega',
                   '      rw [hexp] at heq',
                   '      simp at heq ⊢',
                   '      omega',
                   f'    exact branch_r{r}_n{i}_h{h} k x a v ha hx heqRow']
            z.append('')
    z += ['#print axioms generic_r402_n0','#print axioms generic_r402_n2',
          '#print axioms generic_r1738_n1','#print axioms generic_r1738_n2',
          'end SheepReflectedGeneric']
    return '\n'.join(z)+'\n'

if __name__=='__main__':
    target=Path(sys.argv[1] if len(sys.argv)>1 else 'ReflectedGeneric.lean')
    with FileLock(str(target)+'.lock'):
        with NamedTemporaryFile('w',encoding='utf-8',dir=target.parent,delete=False) as f:
            f.write(generate())
            f.flush()
            os.fsync(f.fileno())
            tmp=f.name
        os.replace(tmp,target)
    print('Generated source-linked Lean inverse classifiers:',target)
