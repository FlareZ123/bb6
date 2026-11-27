"""Emit sharded original-checker proofs for a classified exact query tree.
Uses the same block encoding and allMoves composition as Agent48 package6.py,
with PackedPrefixAudit for repeated prefix checks. Every leaf remains checked.
"""
import json,pathlib,sys,re
from blockcert import generate
from collections import Counter
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
PARENT=[7,24,11,24,14,24,17,16,24,13,24,24]
NS='BB6.Agent3Raw139E1ZeroRDD0ZeroRE'
PREFIX='A3E1ZeroRDD0ZeroRE'
def bl(x):return str(bool(x)).lower()
def slot(s):return f'({s//2},{bl(s%2)})'
def mov(v):return f'⟨{bl(v&2)},{bl(v&1)},{v//4}⟩'
def pack(xs,b):return sum(v<<(b*i) for i,v in enumerate(xs))
def vec(xs,b,stride=16):return f'⟨{b},{stride},#['+','.join(hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride))+']⟩'
def rows(xs,b):
 k=max(1,max(map(len,xs)))
 return f'⟨{vec([pack([v+1 for v in x],b) for x in xs],b*k,8)},{b},{k}⟩'
def block_source(i,t,c):
 ns='BB6BlockFAR2' if c['width']==2 else 'BB6BlockFAR'
 assert c['width'] in (2,3)
 d,n=c['left_states'],c['right_nodes'];b=max(d,n).bit_length();pb=(2**c['width']*d).bit_length()
 moves=', '.join('none' if m is None else f'some ⟨{bl(m[0])},{bl(m[1])},{m[2]}⟩' for m in c['moves'])
 ns2=f'{NS}Blocks.H{i}'
 src=f"""namespace {ns2}
def machine : BB6BlockFAR.Table := fun q b => ([{moves}] : List (Option BB6BlockFAR.Move))[2*q.val+b.toNat]?.getD none
def cert : {ns}.Data {d-1} {n-1} := {{
  start := 0
  pushCodes := {vec(c['push'],b)}
  controlCodes := {vec(c['ctrl'],b)}
  auxiliaryCodes := {vec(c['aux'],b)}
  predecessorCodes := {rows(c['pred'],pb)}
  edgeCodes := {rows(c['edges'],b)}
  zeroCodes := {sum(1<<x for x in c['zero_states'])}
  zeroNextCodes := {vec(c['zeroNext'],b)}
}}
"""
 if d<10:src+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩\n'
 else:
  src+='\n'.join(f'theorem row_{l} : cert.rowsAt machine ({l} : Fin {d}) = true := by decide +kernel' for l in range(d))
  src+=f'\ntheorem rows_valid : cert.rowsCheck machine = true := by\n  unfold {ns}.Data.rowsCheck\n  rw [show List.finRange {d} = ({list(range(d))} : List (Fin {d})) by decide]\n  simp ['+', '.join(f'row_{l}' for l in range(d))+']\n'
  src+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,rows_valid⟩\n'
 src+=f"""theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c :=
  cert.sound machine valid
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}
theorem same : ctr = BB6BlockFAR.partialTable machine :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever
end {ns2}
"""
 return src

def main(part,recipes,out,cap):
 out.mkdir(parents=True,exist_ok=True);p=json.loads(part.read_text());solved={int(i):v for i,v in json.loads(recipes.read_text()).items()}
 tree,opens=p['tree'],p['open'];idx={tuple(t):i for i,t in enumerate(opens)}
 assert len(idx)==len(opens)==len(solved) and set(solved)==set(range(len(opens)))
 assert all(v[0] in ('block','last','cycle') for v in solved.values())
 B=max([p['counts']['maxquery']]+[v[1][0] for v in solved.values() if v[0]=='last'])+6
 base='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
 blocks={};bi=[i for i,v in solved.items() if v[0]=='block']
 for k in range(0,len(bi),8):
  mod=f'{PREFIX}Block{k//8:02d}';src='import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\n'+base
  for i in bi[k:k+8]:
   r=solved[i][1];assert not r[-2];c=generate(opens[i],*r[:-1],phase=r[-1],event_limit=50000);assert c is not None
   src+=block_source(i,opens[i],c);blocks[i]=mod
  (out/(mod+'.lean')).write_text(src)
 sizes={}
 def size(n):
  s=sum(map(size,n[3])) if n[0]=='split' else 1;sizes[id(n)]=s;return s
 assert size(tree)==1+23*p['counts']['split']
 module_for={}
 base+=f'namespace {NS}\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6Coverage.Agent10ZipAudit BB6.Agent3PackedAudit BB6.Agent48PackedPrefix\n'
 def imports_for(s):
  needed={blocks[int(i)] for i in re.findall(r'Blocks\.H(\d+)\.ctr',s)}
  needed|={module_for[n] for n in re.findall(r'\b[pth](R\d+(?:_\d+)*)\b',s) if n in module_for}
  return 'import FastThreeHoleAudit\nimport PackedPrefixAudit\n'+''.join(f'import {m}\n' for m in sorted(needed))
 def leaf(n):
  k,*a=n
  if k=='cycle':
   e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
  if k=='last':return f'.last {a[0]} {slot(a[1])}'
  if k=='far':
   rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
  if k=='open':
   i=idx[tuple(a[0])];s=solved[i]
   if s[0] in ('last','cycle'):return leaf((s[0],*s[1]))
   return f'.proven {NS}Blocks.H{i}.ctr {NS}Blocks.H{i}.never'
  raise ValueError(k)
 def emit_check(name,t,steps,s,children,lines):
  lines.append(f'def p{name} : PartialMachine := fromCodes {t}')
  lines.append(f'def t{name} : Audit := .split {steps} {slot(s)} (byMove [\n'+',\n'.join(a for a,_ in children)+'])')
  if all(h is None for _,h in children):
   lines.append(f'theorem h{name} : packedCheck {B} p{name} t{name} = true := by\n  rw [← packedPrefixCheck_eq]\n  decide +kernel')
  else:
   lines.append(f'''theorem h{name} : packedCheck {B} p{name} t{name} = true := by
  simp only [t{name}, packedCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r
  all_goals
    have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
      have hlt := q.isLt
      simp only [Fin.ext_iff]
      omega
    rcases hcases with h | h | h | h | h | h
    all_goals subst q''')
   for i,(a,h) in enumerate(children):
    v=ORDER[i]
    if h is None:lines.append('  · decide +kernel')
    else:
     cname=h[1:];lines.append(f'''  · change packedCheck {B} (refine p{name} {slot(s)} (some {mov(v)})) {a} = true
    have hp : refine p{name} {slot(s)} (some {mov(v)}) = p{cname} := tableOK_sound _ _ (by decide +kernel)
    rw [hp]
    exact {h}''')
  return f't{name}',f'h{name}'
 def build(n,t,name,lines):
  if n[0]!='split':return leaf(n),None
  _,steps,s,kids=n;assert len(kids)==24 and t[s]==24
  items=[]
  for i,(v,ch) in enumerate(zip(ORDER,kids)):
   tt=t.copy();tt[s]=v;items.append((ch,tt,f'{name}_{i}'))
  # If the entire subtree fits, check it as one term, not a chain of tiny proofs.
  if sizes[id(n)]<=cap:
   def literal(n):
    if n[0]!='split':return leaf(n)
    _,steps,s,cs=n
    return f'.split {steps} {slot(s)} (byMove [\n'+',\n'.join(map(literal,cs))+'])'
   lines.append(f'def p{name} : PartialMachine := fromCodes {t}')
   lines.append(f'def t{name} : Audit := {literal(n)}')
   lines.append(f'theorem h{name} : packedCheck {B} p{name} t{name} = true := by\n  rw [← packedPrefixCheck_eq]\n  decide +kernel')
   return f't{name}',f'h{name}'
  return emit_check(name,t,steps,s,emit_children(items),lines)
 def emit_group(items):
  lines=[];r=[build(n,t,name,lines) for n,t,name in items]
  mod=PREFIX+'Branch'+items[0][2].replace('_','X');src=base+'\n'.join(lines)+f'\nend {NS}\n'
  (out/(mod+'.lean')).write_text(imports_for(src)+src)
  for _,_,name in items:module_for[name]=mod
  return r
 def emit_children(items):
  result=[None]*len(items);pending=[];mass=0
  def flush():
   nonlocal pending,mass
   if pending:
    for j,x in zip(pending,emit_group([items[j] for j in pending])):result[j]=x
    pending=[];mass=0
  for i,(n,t,name) in enumerate(items):
   if n[0]!='split':result[i]=(leaf(n),None)
   elif sizes[id(n)]>cap:
    flush();result[i]=emit_group([(n,t,name)])[0]
   else:
    if mass+sizes[id(n)]>cap:flush()
    pending.append(i);mass+=sizes[id(n)]
  flush();assert all(x is not None for x in result);return result
 _,steps,s,kids=tree;items=[]
 for i,(v,ch) in enumerate(zip(ORDER,kids)):
  t=PARENT.copy();t[s]=v;items.append((ch,t,f'R{i}'))
 lines=[];emit_check('Root',PARENT,steps,s,emit_children(items),lines)
 lines.append(f'''def parent : PartialMachine := pRoot
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent pRoot fromCodes
  cases h : ({PARENT} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedPacked {B} parent tRoot root nohalt hRoot
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {B} m := certificate.sound
theorem weighted : Cover (WeightedBound {B}) parent := Cover.leaf _ all_completions_weighted
#print axioms hRoot
#print axioms all_completions_weighted
#print axioms weighted
end {NS}
''')
 src=base+'\n'.join(lines);(out/(PREFIX+'Cover.lean')).write_text(imports_for(src)+src)
 print('Bound',B,'block proofs',len(bi),'branch modules',len(set(module_for.values())),'leaves',sizes[id(tree)])
if __name__=='__main__':main(pathlib.Path(sys.argv[1]),pathlib.Path(sys.argv[2]),pathlib.Path(sys.argv[3]),int(sys.argv[4]) if len(sys.argv)>4 else 600)
