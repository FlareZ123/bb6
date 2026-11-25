import json,sys
from pathlib import Path

def bits(s):return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def word(xs):
    if not xs:return '.lit []'
    pre=xs[0] if not xs[0].startswith('*') else ''
    tail=xs[1:] if pre else xs
    if not tail:return f'.lit {bits(pre)}'
    return f'.periodic {bits(pre)} {bits(tail[0][1:])} ({word(tail[1:])})'
def pz(c):return f'⟨{c[0]}, {word(c[1])}, {word(c[2])}⟩'
def table(s):
    s=s.replace('_','')
    out=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    for i in range(12):
        v=s[3*i:3*i+3]
        if v=='---':continue
        out.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)')
    return '\n'.join(out+['  | _,_ => none',''])
def cert(row):
    i,s,e,fam,a,b,groups=row
    acts=[]
    for op in groups:
        if isinstance(op,int):acts.append(f'List.replicate {op} Action.step')
        else:
            side,lp,rp,P,O,L,R,k=op
            acts.append(f'[.{"left" if side=="L" else "right"} {bits(lp)} {bits(rp)} {bits(P)} {bits(O)} ({word(L)}) ({word(R)}) {k}]')
    return f"""
namespace Leaf{i}
-- {s}
{table(s)}
def cert : Cert := ⟨{e}, {pz(fam)}, 1,
  {' ++ '.join(acts)}, {a}, {b}⟩
theorem checked : check table cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm
#print axioms never
end Leaf{i}
"""
print("""import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Auto
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto""")
for row in Path(sys.argv[1]).read_text().splitlines():
    if row.strip():print(cert(json.loads(row)))
print('end BB6.Agent19Raw40.Auto')
