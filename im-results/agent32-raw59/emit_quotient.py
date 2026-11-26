"""Emit original FastBiDFA kernel certificates for deterministic quotient candidates."""
from collections import defaultdict
from pathlib import Path
from quotient_search import witness
import json,sys
BASE='BB6.Agent32AsymNGram'
CHECK='BB6.Agent32FastBiDFA'
def arr(xs):return '#['+','.join(xs)+']'
def bs(b):return str(bool(b)).lower()
def emit(root,name,record):
 table,D=record['table'],record['dfa'];Es,n,S=witness(table,D)
 assert Es is not None and n==record['states'] and sum(len(v) for e in Es for v in e.values())==record['edges']
 ns=f'{BASE}.{name}'
 header=['set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false',f'namespace {ns}','open BB6Coverage BB6.Agent1NGram BB6.Agent32FastBiDFA']
 def write(mod,imports,body):
  (root/(mod+'.lean')).write_text('\n'.join([*(f'import {x}' for x in imports),*header,*body,f'end {ns}','']))
 p=table.replace('_','');moves=[]
 for j in range(12):
  a=p[j*3:j*3+3]
  v='none' if a=='---' else f'some (some ⟨{bs(a[0]=="1")},{bs(a[1]=="R")},{ord(a[2])-65}⟩)'
  moves.append(f'  | {j//2},{bs(j%2)} => {v}')
 data=['def table : PartialMachine := fun s => match s.1.val,s.2 with',*moves,'  | _,_ => none']
 for nm,d,esd in zip(['leftGraph','rightGraph'],D,Es):
  pred=arr('['+','.join(f'({bs(b)},{y})' for b,y in sorted(esd[x]))+']' for x in range(len(d)//2))
  data.append(f'def {nm} : Graph := ⟨{arr(map(str,d))},{pred}⟩')
 nodes={};defs=[]
 def trie(xs):
  if not xs:return '.empty'
  if xs==[0]:return '.leaf'
  key=(trie([x//2 for x in xs if x%2==0]),trie([x//2 for x in xs if x%2==1]))
  if key not in nodes:
   nodes[key]=f't{len(defs)}';defs.append(f'def {nodes[key]} : Trie := .branch {key[0]} {key[1]}')
  return nodes[key]
 rs=defaultdict(set)
 for s,l,r in S:rs[s,l].add(r)
 rows=[f'def row{s} : Array Trie := '+arr(trie(sorted(rs[s,l])) for l in range(len(D[0])//2)) for s in range(12)]
 data += defs+rows+['def cert : BB6.Agent32FastBiDFA.Cert := ⟨leftGraph,rightGraph,'+arr(f'row{s}' for s in range(12))+'⟩']
 write(name+'Data',['FastBiDFA'],data)
 modules=[];body=[]
 for s in range(12):
  proof=f'theorem row{s:02}_checked : {CHECK}.rowCheck table cert {s//2} {bs(s%2)} = true := by decide +kernel'
  if n<=2000:body.append(proof)
  else:
   mod=name+f'Row{s:02}';modules.append(mod)
   write(mod,[name+'Data'],[proof])
 write(name,modules or [name+'Data'],body+[f'theorem allRows (q : Fin 6) (a : Bool) : {CHECK}.rowCheck table cert q a = true := by','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases a',*(f'  · exact row{s:02}_checked' for s in range(12)),f'theorem checked : {CHECK}.check table cert = true :=',f'  {CHECK}.check_of_rows (by decide) (by decide) (by decide) allRows','theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  {CHECK}.never table cert checked m hm','#print axioms never'])
 print(name,record['states'],record['edges'],len(D[0])//2,len(D[1])//2,len(nodes),flush=True)
 return name
if __name__=='__main__':emit(Path('.'),'QuotPilot',json.loads(Path(sys.argv[1] if len(sys.argv)>1 else 'fold113.json').read_text()))
