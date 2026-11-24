from pathlib import Path
import json
ROOT=Path(__file__).parent
def encode(s):
    t=s.replace("_","")
    return [24 if t[i:i+3]=="---" else 4*(ord(t[i+2])-65)+2*int(t[i])+int(t[i+1]=="R") for i in range(0,36,3)]
def shape(s):
    q,l,r=s
    return f'⟨{q}, word {" ".join(json.dumps(x) for x in l)}, word {" ".join(json.dumps(x) for x in r)}⟩'
def op(x):
    if isinstance(x,int):return f'List.replicate {x} Op.step'
    if x[0]=="rewrite":return f'[.rewrite {shape(x[1])}]'
    k,i,n,w=x
    return f'[.{k} {i} {n} (bits "{w}")]'
s='import BlockPump\nimport DepthEightFAR\nnamespace BB6.Agent7F1Pumps\nopen BB6Coverage BB6Coverage.FAR BB6Coverage.Agent50Pump\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
for i,c,entry,z,ops in json.loads((ROOT/'pumps.json').read_text()):
    s+=f'''
def p{i} : PartialMachine := fromCodes {encode(c)}
def c{i} : Certificate := ⟨{entry}, {shape(z)}, {" ++ ".join(map(op,ops))}⟩
theorem c{i}_checked : c{i}.check p{i} = true := by decide
theorem p{i}_never (m : Machine) (hm : compatible p{i} m) : NeverHalts m :=
  Certificate.never p{i} c{i} c{i}_checked m hm
#print axioms p{i}_never
'''
(ROOT/'F1SiblingPumps.lean').write_text(s+'\nend BB6.Agent7F1Pumps\n')
