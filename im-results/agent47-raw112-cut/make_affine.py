"""Four affine-growth certificates missed by single-sweep discovery."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/'agent47-raw115-cut'),str(ROOT.parent)]
import counter as c
R,W,C=c.R,c.W,c.C

def generate(i,p):
    if i==72:
        q=3;st=C(q,W('00110',R('110'),'111111',R('1111')),W());ta=C(q,W('00110110',R('110'),'1111111111',R('1111')),W());entry=58;a,b=103,48
    elif i==121:
        q=1;st=C(q,W(),W('0000',R('0'),'10100',R('0'),'10'));ta=C(q,W(),W('00000',R('0'),'101000',R('0'),'10'));entry=129;a,b=62,6
    else:
        q=4;d=12 if i==62 else 8;st=C(q,W(),W('0101',R('01'*d)));ta=C(q,W(),W('01'*(2+d),R('01'*d)));entry=11;a,b=(228,288) if i==62 else (130,128)
    return '\n\n'.join([f'''import Raw115CounterBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6Coverage.Agent31Pump.Raw112Counter{i}
open BB6Coverage BB6Coverage.Agent31Pump.Raw115CounterBase''',c.pump.tab(p),c.macro(p,'growthCore',st,ta,False,(a,b)),f'''def fam (n : Nat) : Z0 := {c.cfg(st)}

theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (fam 0) := by rfl

theorem growth (n : Nat) : run0 table ({a}+{b}*n) (fam n) = some (fam (n+1)) := by
  simpa only [fam,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using growthCore n

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table fam (fun _ => True) 0 trivial {entry} entry
    (fun n _ => ⟨n+1,{a}+{b}*n,trivial,by omega,growth n⟩) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw112Counter{i}'''])+'\n'
if __name__=='__main__':
    rows=(ROOT/'hard.txt').read_text().splitlines()
    for i in [62,72,73,121]:
        (ROOT/f'Raw112Counter{i}.lean').write_text(generate(i,c.pump.parse(rows[i])))
