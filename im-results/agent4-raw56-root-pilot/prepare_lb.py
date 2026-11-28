#!/usr/bin/env python3
"""Replay frozen Raw56 E1=1LB witnesses; emit a partial Cover with exact residual roster."""
import argparse,base64,hashlib,json,lzma,shutil,struct,subprocess,sys,tarfile,io
from pathlib import Path
from lb_cut_patch import patch
TAG='E11LB';BOUND=1000000;PARENT='1RB---_1RC---_0RD---_1LD1LE_---1LB_------'
SHA={'json':'94864ce7d66c4ac0bfde873fc65c621072ffa85bc1e167b144c8dec2e4c1aaaf','open':'30309656f31a1003c4a47571e9b7e5c508013a6964b48e96076ec6d754350d7f','far':'9822b74ee87b9c04bfcb9fbc2f63ce3bad888e1c53ac3d43934ca9a05425486d'}
LONG={6168,21109}
def digest(b):return hashlib.sha256(b).hexdigest()
def decoded(p,h):
 b=lzma.decompress(base64.b64decode(p.read_text().strip(),validate=True));assert digest(b)==h;return b
def finite_groups(p):
 b=decoded(p,'3ec13ed6a8ec3e15750e3b7bddd6c61d6a2e7d15878360ac5bcf36d4805c352e');a=0;out={}
 while a<len(b):
  pid,n=struct.unpack_from('<HH',b,a);a+=4;prev=0
  for _ in range(n):
   v=shift=0
   while True:
    x=b[a];a+=1;v|=(x&127)<<shift
    if x<128:break
    shift+=7
   prev+=v;assert prev not in out;out[prev]=pid
 assert a==len(b) and len(out)==2242
 return out
def parse(s):
 s=s.replace('_','');assert len(s)==36;return [s[i:i+3] for i in range(0,36,3)]
def move(i):return f'{i//12}{"R" if i%12>=6 else "L"}{chr(65+i%6)}'
def mv(i):return f'⟨{str(bool(i//12)).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def slot(s):return f'({s//2},{str(bool(s%2)).lower()})'
def run(a,cwd,**kw):subprocess.run(a,cwd=cwd,check=True,**kw)
def valid_far(c):
 n=(len(c)-1)//2;return len(c)%2==1 and c[0] in '01' and 1<=n<=10 and all(x.isdigit() and int(x)<n for x in c[1:])
def table_expr(p):return '_'.join(''.join(p[j:j+2]) for j in range(0,12,2))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--dossier',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--reuse-cut',type=Path);a=ap.parse_args()
 out=a.out.resolve();D=a.dossier.resolve();assert not out.exists();shutil.copytree(a.source.resolve(),out)
 sys.path.insert(0,str(out));from discover_siblings import method;from minimize_cert import quotient,validate;from emit_automata import emit as emit_finite;from emit_symbolic import emit as emit_growth,table;import emit_symbolic
 from symbolic_sweep import run_symbolic
 # Single-step equality chains use a direct proof instead of a one-line calc.
 original_eq=emit_symbolic.eq_word
 def eq_word(a,b):
  proof=original_eq(a,b);lines=proof.splitlines()
  return "by\n    "+lines[-1].strip() if len(lines)==4 and lines[1].strip()=="calc" else proof
 emit_symbolic.eq_word=eq_word
 stem=out/TAG
 if a.reuse_cut:
  for ext in SHA:shutil.copyfile(a.reuse_cut.with_suffix('.'+ext),stem.with_suffix('.'+ext))
 else:
  run(['g++','-O3','-std=c++20','cut.cpp','-o','cut'],out);run(['g++','-O3','-std=c++20','farbank.cpp','-o','farbank'],out)
  run([str(out/'cut'),PARENT,'1000','32','7',str(stem)],out)
  codes=(out/'bank-candidates.txt').read_text().split();(out/'valid-bank.txt').write_text('\n'.join(c for c in codes if valid_far(c))+'\n')
  rows=stem.with_suffix('.open').read_text().splitlines();query=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(rows))
  with stem.with_suffix('.far').open('w') as f,stem.with_suffix('.far.log').open('w') as log:run([str(out/'farbank'),'4',str(out/'valid-bank.txt')],out,input=query,text=True,stdout=f,stderr=log)
 for ext,h in SHA.items():assert digest(stem.with_suffix('.'+ext).read_bytes())==h,ext
 rows=stem.with_suffix('.open').read_text().splitlines();assert len(rows)==len(set(rows))==43348
 bank={int(i):c for i,c in (x.split() for x in stem.with_suffix('.far').read_text().splitlines())};assert len(bank)==40968 and all(map(valid_far,bank.values()))
 run([sys.executable,'portfolio_fast.py'],out);raw=(out/'fastportfolio.json').read_bytes();assert digest(raw)=='2692355452c0bf1cde526c665435df183c80d8634fa5bf4d4a4b87dad4a927f1';params=json.loads(raw)
 finite=finite_groups(D/'E11LB-finite-groups.xz.b64');ledger=json.loads((D/'E11LB-residual-ledger.json').read_text())
 late={i:['last',n,s] for i,n,s in ledger['late']};splits={int(i):x for i,x in ledger['splits'].items()};cycles={int(i):x for i,x in ledger['cycles'].items()};sym=set(ledger['symbolic']);special=set(ledger['special']);unresolved=set(ledger['unresolved']);sets=[set(bank),set(finite),set(late),set(splits),set(cycles),sym,special,unresolved];assert sum(map(len,sets))==len(set.union(*sets))==len(rows);assert set.union(*sets)==set(range(len(rows)))
 fdir=out/'finite'/TAG;fdir.mkdir(parents=True,exist_ok=True);ns='BB6.Agent4Raw56BranchFinite.'+TAG;proven={};certmods=[];states=[]
 for i,pid in sorted(finite.items()):
  t=rows[i];tbl=parse(t);c=method(tbl,*params[pid],12000);assert c[0],(i,pid,c[:2]);states.append((i,pid,c[1]));c=quotient(c);validate(tbl,c);mod=f'finite.{TAG}.F{i}';(fdir/f'F{i}.lean').write_text('import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage\n'+emit_finite(i,tbl,c)+'\nend '+ns+'\n');certmods.append(mod);proven[t]=[mod,f'{ns}.M{i}']
 assert digest(b''.join(struct.pack('<HHH',*x) for x in states))=='e316cb3ef030a67e6c44edaac526a7acc5ee496ab60537f1f2f727ec153bc86d'
 gdir=out/'rootgrowth';gdir.mkdir(exist_ok=True);growthmods=[]
 def symbol(z):return z[0],*[[(tuple(x) if isinstance(x,list) else x) for x in a] for a in z[1:]]
 targets=json.loads(decoded(D/'E11LB-growth-targets.xz.b64','15aa5c50230f0a0dfa77652a3a5b73281a418bdb9c5c4a14b0722ceae67c5012'));assert {x[0] for x in targets}==sym
 for i,entry,start,target in targets:
  z=run_symbolic(parse(rows[i]),symbol(start),symbol(target));assert z,i;r=json.loads(json.dumps(dict(index=i,table=rows[i],entry=entry,start=start,target=target,ops=z[0],end=z[1])));(gdir/f'{TAG}M{i}.lean').write_text(emit_growth(r,TAG))
 (out/'rootbranches').mkdir(exist_ok=True);(out/'rootbranches'/f'{TAG}.aftergrowth').write_text(''.join(f'{i} {rows[i]}\n' for i in sorted(special)))
 shutil.copyfile(D/'emit_lb_multi.py',out/'emit_lb_multi.py');run([sys.executable,'emit_lb_multi.py'],out)
 for k,h in [(2,'9f724a907406531735bf9dc811af6126375271eadcde6d1ed2d5628e982d35ec'),(3,'e819ba2d6815192638427fda16147c5893d2ae43bd6aeb9018bfe4fa29584fec'),(4,'cad8f62a9779b9fbf9668c33efa565108db7704ae4a86490d2cc60d4d0b94ee8')]:
  raw=base64.b64decode((D/f'lb-proofset{k}-src.tar.xz.b64').read_text().strip(),validate=True);assert digest(raw)==h
  with tarfile.open(fileobj=io.BytesIO(raw),mode='r:xz') as t:t.extractall(out,filter='data')
 for i in sorted(sym|special):
  name=f'{TAG}M{i}';mod=f'rootgrowth.{name}';assert (gdir/(name+'.lean')).exists();growthmods.append(mod);proven[rows[i]]=[mod,f'BB6.Agent4Raw56Root{TAG}.M{i}']
 # Replace exactly the frozen original open leaves, retaining original table order.
 tree=json.loads(stem.with_suffix('.json').read_text());it=iter(enumerate(rows));newrows=[];newfar=[];respaths=[]
 def rec(t,p):
  if t[0]=='open':
   i,s=next(it);assert s==t[1]==table_expr(p)
   if i in unresolved|LONG:return ['unresolved']
   if i in late:return late[i]
   if i in splits:return splits[i]
   if i in cycles:return cycles[i]
   if i in bank:newfar.append((len(newrows),bank[i]))
   else:assert s in proven
   newrows.append(s);return t
  if t[0]=='split':
   n,s,kids=t[1:];assert len(kids)==24 and p[s]=='---';return ['split',n,s,[rec(k,p[:s]+[move(i)]+p[s+1:]) for i,k in enumerate(kids)]]
  return t
 tree=rec(tree,parse(PARENT));assert next(it,None) is None
 def residual(t,p,pa=()):
  if t[0]=='unresolved':respaths.append((rows.index(table_expr(p)),pa));return
  if t[0]=='split':
   n,s,kids=t[1:]
   for q in range(6):
    for w in range(2):
     for r in range(2):
      i=12*w+6*r+q;residual(kids[i],p[:s]+[move(i)]+p[s+1:],pa+((s,i),))
 residual(tree,parse(PARENT));assert {i for i,_ in respaths}==unresolved|LONG
 stem.with_suffix('.json').write_text(json.dumps(tree,separators=(',',':')));stem.with_suffix('.open').write_text('\n'.join(newrows)+'\n');stem.with_suffix('.far').write_text(''.join(f'{i} {c}\n' for i,c in newfar))
 od=out/TAG;od.mkdir(exist_ok=True);(od/'proven.json').write_text(json.dumps(proven));(od/'automata_modules.json').write_text(json.dumps(certmods+growthmods));(od/'late.json').write_text('{}');patch(out/'emit_cut.py',out/'emit_lb_cut.py');run([sys.executable,'emit_lb_cut.py',TAG,str(BOUND)],out)
 from lb_long import emit as emit_long
 for i in sorted(LONG):
  _,n,s=late[i];(gdir/f'{TAG}Long{i}.lean').write_text(emit_long(i,rows[i],n,s));growthmods.append(f'rootgrowth.{TAG}Long{i}')
 man=json.loads((od/'manifest.json').read_text());meta={'tag':TAG,'bound':BOUND,'open':len(rows),'valid_far':len(bank),'finite':len(finite),'cert_modules':certmods,'growth_modules':growthmods,'cut_modules':len(man),'top_roots':man[-1][1],'final_module':man[-1][0],'residuals':[{'index':i,'table':rows[i],'path':pa} for i,pa in respaths]};(od/'accept-meta.json').write_text(json.dumps(meta,indent=2)+'\n');print({k:v for k,v in meta.items() if k not in ('cert_modules','growth_modules','top_roots')},flush=True)
 emit_consumer(od,rows,respaths,unresolved,table)
def emit_consumer(od,rows,respaths,unresolved,table):
 ns='BB6.Agent4Raw56LB.E11LB';out=['import Raw56LBE11LBAll']+[f'import rootgrowth.E11LBLong{i}' for i in sorted(LONG)]+['set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit','open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier']
 for i,pa in respaths:
  if i in LONG:out.append(f'abbrev table{i} := BB6.Agent4Raw56LBLong.M{i}.table')
  else:out.append(table(rows[i]).replace('def table :',f'def table{i} :',1))
  expr='p'
  for s,j in pa:expr=f'refine ({expr}) {slot(s)} (some {mv(j)})'
  out.append(f'''theorem eq{i} : {expr} = table{i} := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl''')
 ids=[i for i,_ in respaths];names=','.join(f'table{i}' for i in ids);rs=','.join(f'table{i}' for i in ids if i in unresolved)
 out.append(f'''theorem residual_tables : residuals.map Prod.snd = [{names}] := by
  unfold residuals
  simp only [List.map_cons,List.map_nil,{','.join(f'eq{i}' for i in ids)}]
def hardTables : List PartialMachine := [{rs}]
theorem reduced_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound {BOUND} m ∨ ∃ q, q ∈ hardTables ∧ TNFQuotientCompatible q m := by
  intro m hm
  rcases partial_quotient m hm with h | ⟨e,he,hc⟩
  · exact Or.inl h
  · have hh : e.snd ∈ residuals.map Prod.snd := List.mem_map_of_mem Prod.snd he
    rw [residual_tables] at hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with {'|'.join('h' for _ in ids)}''')
 for i in ids:
  out.append(f'''    · rw [h] at hc
      exact Or.inl (BB6.Agent4Raw56LBLong.M{i}.bound_quotient m hc)''' if i in LONG else f'''    · rw [h] at hc
      exact Or.inr ⟨table{i}, by simp [hardTables], hc⟩''')
 out+=['#print axioms reduced_quotient',f'end {ns}'];(od/'Raw56LBE11LBReduced.lean').write_text('\n'.join(out)+'\n')
if __name__=='__main__':main()
