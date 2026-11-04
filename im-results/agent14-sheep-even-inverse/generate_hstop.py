"""Generate 21 h-cutoff congruence proofs for five Sheep inverse cones."""
from pathlib import Path
from filelock import FileLock
import tempfile
import os
import hashlib
from independent_cones_data import FAMILIES,v3,node_value

def source():
    out=['import IndependentHBound','set_option maxRecDepth 32768',
         'set_option exponentiation.threshold 10000','','namespace SheepFiveHStop','']
    count=0
    for j,p,nodes in FAMILIES:
        for i,(s,b,d) in enumerate(nodes):
            H=v3(node_value((s,b,d),j)-1)+1
            M=d*3**H
            q=(d-b)%M
            assert pow(2,p,M)==1
            assert pow(2,j+s,M)!=q
            name=f'hstop_{j}_{i}'
            out.extend([f'theorem {name} (k : Nat) :',
                        f'    2^({j}+{p}*k+{s}) % {M} ≠ {q} := by',
                        f'  have hp : 2^{p} % {M}=1 := by decide',
                        f'  have hr := SheepIndependentHBound.pow_mod_period',
                        f'    {M} {p} ({j}+{s}) k (by decide) hp',
                        f'  have he : {j}+{p}*k+{s}=({j}+{s})+{p}*k := by omega',
                        '  rw [he, hr]',
                        '  decide',
                        f'#print axioms {name}', ''])
            count+=1
    assert count==21
    return '\n'.join(out+['end SheepFiveHStop'])+'\n'

def main():
    output=Path(__file__).with_name('SheepFiveHStop.lean')
    data=source()
    with FileLock(str(output)+'.lock'):
        fd,tmp=tempfile.mkstemp(prefix='.hstop-',dir=output.parent)
        try:
            with os.fdopen(fd,'w',encoding='utf-8',newline='\n') as f:
                f.write(data);f.flush();os.fsync(f.fileno())
            os.replace(tmp,output)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)
    print('sha256',hashlib.sha256(data.encode()).hexdigest(),'size',len(data))

if __name__=='__main__':main()
