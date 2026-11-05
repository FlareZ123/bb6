"""Generate 56 individual Lean proofs transporting Sheep original-source inverse equations to modular exclusions."""
from pathlib import Path
from filelock import FileLock
from hashlib import sha256
from os import fdopen, fsync, replace, unlink
from tempfile import mkstemp
from seven_cones import CASES, v3

def main():
    J,P,nodes,edges=CASES[-1]
    assert J==648 and P==122472 and len(nodes)==2
    outdir=Path(__file__).with_name('generated-648-source')
    outdir.mkdir(exist_ok=True)
    count=0
    digests=[]
    for i,(s,b,d) in enumerate(nodes):
        c=-b
        H=v3(((1<<(J+s))+b)//d-1)+1
        for h in range(H):
            D=d*3**h
            C=D+2**h*(b-d)
            A=1
            while not (1<D*(2*A-1)-2*C<2**A and 2**A>=2*D): A+=1
            for a in range(1,A):
                if (i,h,a)==(0,5,2):
                    continue
                m=D*(2**(a+1)+1)
                K=D*(2*a-1)-2*C
                assert -m<K<m
                B=(-K)%m
                L=2*a*D+2**(h+1)*(d+c)
                Rconst=3*D
                t=0 if K<=0 else 1
                assert m*t-K==B
                R=J+s+h+1
                exp=f'{J}+{P}*k+{s}+{h}+1'
                name=f'no_{i}_{h}_{a}'
                lines=[
                    'import Sheep648LowResidues',
                    'set_option maxRecDepth 32768',
                    'set_option maxHeartbeats 0',
                    'set_option exponentiation.threshold 100000',
                    '',
                    'namespace Sheep648SourceLow',
                    f'theorem {name} (k v : Nat)',
                    f'    (hEq : ({d}*3^{h})*(2^({a}+1)+1)*v +',
                    f'      2*{a}*({d}*3^{h}) + 2^({h}+1)*{d} + 2^({h}+1)*{c} =',
                    f'      2^({exp}) + 3*({d}*3^{h})) : False := by',
                    f'  have hp : 2^({exp})=2^({R}+{P}*k) := by congr 1; omega',
                    '  rw [hp] at hEq',
                    f'  have hlin : {m}*(v+{t})=2^({R}+{P}*k)+{B} := by',
                    f'    change {m}*v+{L}=2^({R}+{P}*k)+{Rconst} at hEq',
                    f'    have hstep (z pow : Nat) (he : z+{L}=pow+{Rconst}) :',
                    f'        z+{m*t}=pow+{B} := by omega',
                    f'    have hlinAux := hstep ({m}*v) (2^({R}+{P}*k)) hEq',
                    '    simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero] using hlinAux',
                    f'  have hmod : (2^({R}+{P}*k)+{B})%{m}=0 := by',
                    '    rw [← hlin]',
                    '    simp',
                    f'  exact Sheep648LowResidues.exclude_{i}_{h}_{a} k hmod',
                    f'#print axioms {name}',
                    'end Sheep648SourceLow',
                    ''
                ]
                content='\n'.join(lines)
                target=outdir/f'Sheep648SourceLow{count:02d}.lean'
                with FileLock(str(target)+'.lock'):
                    fd,tmp=mkstemp(dir=outdir,prefix='.Sheep648SourceLow.')
                    try:
                        with fdopen(fd,'w',encoding='utf-8',newline='\n') as stream:
                            stream.write(content)
                            stream.flush()
                            fsync(stream.fileno())
                        replace(tmp,target)
                    finally:
                        if Path(tmp).exists(): unlink(tmp)
                digests.append(sha256(content.encode()).hexdigest())
                count+=1
    assert count==56
    print("Generated",count,"one-theorem source-equation proof modules; digest",sha256(''.join(digests).encode()).hexdigest())

if __name__=='__main__': main()
