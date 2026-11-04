"""Generate reproducible all-valuation Lean bounds for five Sheep E cones."""
import hashlib
import os
import tempfile
from pathlib import Path
from filelock import FileLock
from independent_cones_data import FAMILIES,node_value,v3

def source():
    lines=['import IndependentGenericHigh','set_option maxRecDepth 32768','','namespace SheepFiveGenericHigh','',
           '/-- Inductive high-valuation congruence remainder bounds for all 44 rows. -/']
    count=0
    for j,p,nodes in FAMILIES:
        for i,(s,b,d) in enumerate(nodes):
            H=v3(node_value((s,b,d),j)-1)+1
            for h in range(H):
                D=d*3**h;C=D+2**h*(b-d)
                a0=1
                while True:
                    K=D*(2*a0-1)-2*C
                    if 1<K<2**a0 and K%2==1 and 2**a0>=2*D:
                        break
                    a0+=1
                    assert a0<200
                name=f'high_{j}_{i}_{h}'
                lines += [
                    f'theorem {name} (a : Nat) (ha : {a0} ≤ a) :',
                    f'    (1:Int)<SheepIndependentGenericHigh.K {D} ({C}:Int) a ∧',
                    f'    SheepIndependentGenericHigh.K {D} ({C}:Int) a % 2 = 1 ∧',
                    f'    SheepIndependentGenericHigh.K {D} ({C}:Int) a < (2:Int)^a := by',
                    f'  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all',
                    f'    {D} {a0} ({C}:Int) (by decide) a ha',
                    f'  exact ⟨hlo,hodd,hupper⟩',
                    f'#print axioms {name}',
                    ''
                ]
                count+=1
    assert count==44
    return '\n'.join(lines+['end SheepFiveGenericHigh'])+'\n'

def main():
    output=Path(__file__).with_name('SheepFiveGenericHigh.lean')
    data=source()
    with FileLock(str(output)+'.lock'):
        fd,tmp=tempfile.mkstemp(prefix='.sheep-generic-high-',dir=output.parent)
        try:
            with os.fdopen(fd,'w',encoding='utf-8',newline='\n') as f:
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp,output)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)
    print('generated 44 all-a generic high certificates SHA256:',hashlib.sha256(data.encode()).hexdigest(),len(data))

if __name__=='__main__': main()
