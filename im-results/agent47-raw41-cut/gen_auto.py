"""Emit original-semantics Lean certificates from compact AutoPump fixtures.
The fixture discovery is untrusted; Agent46AutoPump.check and its soundness theorem are authoritative.
"""
import json,sys
from pathlib import Path

def bits(w): return '['+','.join('true' if x=='1' else 'false' for x in w)+']'
def word(w): return f'(.lit {bits(w)})' if isinstance(w,str) else f'(.periodic {bits(w[0])} {bits(w[1])} {word(w[2])})'
def config(z): return f'⟨{z[0]},{word(z[1])},{word(z[2])}⟩'

def emit(i,d):
 t=d['table'].replace('_',''); assert len(t)==36
 out=[f'namespace Leaf{i}',f'-- {t}','def table : PartialMachine := fun s => match s.1.val,s.2 with']
 for j in range(12):
  x=t[3*j:3*j+3]
  if x!='---':out.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(x[0]=="1").lower()},{str(x[1]=="R").lower()},{ord(x[2])-65}⟩)')
 out.append('  | _,_ => none')
 ops=[]
 for op in d['ops']:
  if isinstance(op,int):ops.append(f'List.replicate {op} Action.step')
  else:
   dr,lp,rp,I,O,L,R,k=op
   ops.append(f'[.{"left" if dr=="L" else "right"} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {word(L)} {word(R)} {k}]')
 out += [f'def cert : Cert := ⟨{d["entry"]},{config(d["family"])},{d["inc"]},',f'  {" ++ ".join(ops)}, {d["a"]}, {d["b"]}⟩', 'theorem checked : check table cert = true := by decide +kernel', 'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := check_never table cert checked m hm', '#print axioms never',f'end Leaf{i}']
 return '\n'.join(out)

def generate(folder,name):
 ns='BB6.Agent47Raw41.'+name+'Auto';rows=[json.loads(l) for l in (folder/'auto.jsonl').read_text().splitlines() if l.strip()]
 out=['import Agent46AutoPump','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto']
 out.extend(emit(i,d) for i,d in rows)
 out.append('end '+ns)
 Path(name+'Auto.lean').write_text('\n\n'.join(out)+'\n')
 return {int(i):f'.closed (.proven {name}Auto.Leaf{i}.table {name}Auto.Leaf{i}.never)' for i,d in rows}

if __name__=='__main__':generate(Path(sys.argv[1]),sys.argv[2])
