"""Generate 44 all-exponent Sheep special-source Lean proofs; standard library + filelock."""
import hashlib
import os
import tempfile
from pathlib import Path
from filelock import FileLock
from independent_cones_data import FAMILIES, node_value, v3

def source():
    lines = ['import IndependentExceptionalGap', 'set_option maxRecDepth 32768',
             '', 'namespace SheepFiveSpecial', '',
             '/-- Universal quantified exceptional inverse certificates from a checked base gap. -/']
    count = 0
    for j, period, nodes in FAMILIES:
        for i, (s, b, d) in enumerate(nodes):
            H = v3(node_value((s,b,d),j)-1)+1
            for h in range(H):
                D=d*3**h
                C=2*D+2**h*(d-b)
                A=3*D
                e=A.bit_length()-1
                L=2**(e+1)-A
                t0=1
                while D*t0+C >= L*2**t0:
                    t0+=1
                assert 2**e<A<2**(e+1)
                assert j+s+h-e-1>=t0
                name=f'special_{j}_{i}_{h}'
                exp=f'{j}+{period}*k+{s}+{h}'
                t=f'({exp} - {e+1})'
                lines.extend([
                    f'theorem {name} (k a : Nat) :',
                    f'    {A}*2^a + {D}*a + {C} ≠ 2^({exp}) := by',
                    f'  have h : {A}*2^a + {D}*a + {C} ≠ 2^({t}+{e+1}) :=',
                    f'    SheepIndependentGap.no_special_equal {A} {D} {C} {e} {L} {t0}',
                    '      (by decide) (by decide) (by decide) (by decide)',
                    f'      {t} (by omega) a',
                    f'  have he : {t}+{e+1} = {exp} := by omega',
                    '  simpa only [he] using h',
                    f'#print axioms {name}', ''
                ])
                count += 1
    assert count == 44
    lines.append('end SheepFiveSpecial')
    return '\n'.join(lines)+'\n'

def main():
    output=Path(__file__).with_name('SheepFiveSpecial.lean')
    data=source()
    with FileLock(str(output)+'.lock'):
        fd,tmp=tempfile.mkstemp(prefix='.sheep-special-',suffix='.tmp',dir=output.parent)
        try:
            with os.fdopen(fd,'w',encoding='utf-8',newline='\n') as f:
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp,output)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
    print('generated 44 special-source Lean proofs:',len(data),'bytes SHA256',hashlib.sha256(data.encode()).hexdigest())

if __name__=='__main__':
    main()
