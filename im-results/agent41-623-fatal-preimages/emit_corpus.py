"""Generate the finite symbolic certificate corpus; Lean checks every certificate."""
from fitfamilies import cert, match
from near_power import initial
from symbolic_exclusion import verify

lines = []
names = []
totalnodes = 0
for R in (30, 31):
    for off in range(-100, 102, 2):
        cs = [cert(initial(6*3**r+off)) for r in (R,R+2,R+4)]
        if any(c is None for c in cs):
            continue
        t = match(cs,R)
        if not t:
            continue
        try:
            nodes, depth = verify(t,R,off)
        except AssertionError:
            continue
        totalnodes += nodes

        def ser(t,d=0):
            if t is None:
                return 'SymCert.stop'
            refs, ws = [], []
            for _,w,_,ch in t[1]:
                refs.append(ser(ch,d+1))
                ws.append(f'⟨{w[0]*3**(R-d-1)},0,{w[1]}⟩')
            return f'(SymCert.fork {ws[0]} {ws[1]} {refs[0]} {refs[1]})'

        name = f'f{R}'+('m'+str(-off) if off<0 else 'p'+str(off))
        names.append(name)
        lines.append(f'def {name} : CertifiedFamily := ⟨{R},{off},{ser(t)},by decide +kernel⟩')

assert len(names)==133 and totalnodes==370, (len(names),totalnodes)
print('''import NearPowerFamilyCore
namespace BB6.Agent41NearPower
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
''')
print('\n\n'.join(lines))
print('def allFamilies : List CertifiedFamily := ['+','.join(names)+']')
print('#print axioms allFamilies\nend BB6.Agent41NearPower')
