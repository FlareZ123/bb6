#!/usr/bin/env python3
"""Transform generated exact graft into weighted prefix-checking form.
Each long late proof is imported by literal table, never by time alone.
"""
import sys,json,pathlib,re,collections,ast
src=pathlib.Path(sys.argv[1]);out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
part,spec=(json.load(open(x)) for x in sys.argv[3:5]); threshold=int(sys.argv[5]) if len(sys.argv)>5 else 10000
late={tuple(part['open'][int(k)]):(k,n,s) for k,(n,s) in spec['late'].items() if n>=threshold}
assert len(late)==sum(n>=threshold for n,s in spec['late'].values()); seen=collections.Counter()
weighted={tuple(part['open'][int(k)]):(k,entry) for k,entry in spec.get('weighted_external',{}).items()}
assert len(weighted)==len(spec.get('weighted_external',{})) and not set(weighted)&set(late)
seen_weighted=collections.Counter()
for p in src.glob('*.lean'):
 text=p.read_text()
 if ' : Audit := ' not in text:
  (out/p.name).write_text(text);continue
 stack=[];parent=None;tree=False; imports=set();lines=[]
 def current():
  if not stack:return parent
  t,s,i=stack[-1]; t=t.copy();assert t[s]==24 and 0<=i<24;t[s]=4*(i%6)+2*(i//12)+(i//6%2);return t
 def advance():
  global tree
  while stack:
   stack[-1][2]+=1
   if stack[-1][2]<24:return
   stack.pop()
  tree=False
 for line in text.splitlines():
  m=re.fullmatch(r'def p\w+ : PartialMachine := fromCodes (\[.*\])',line)
  if m: parent=ast.literal_eval(m[1]);assert not stack and not tree
  m=re.match(r'(def t\w+ : Audit := )(.*)',line)
  prefix=''
  if m:
   assert parent is not None and not tree;tree=True;prefix=m[1].replace(' : Audit := ',' : WeightedAudit '+str(spec['bound'])+' := ');line=m[2]
  if tree:
   m=re.match(r'\.split \d+ \((\d+),(true|false)\) \(byMove \[',line)
   if m:
    t=current();s=2*int(m[1])+(m[2]=='true');assert t[s]==24;stack.append([t,s,0]);line=line.replace('(byMove [','(byWeightedMove [')
   else:
    t=current()
    m=re.match(r'(\.last \d+ \(\d+,(?:true|false)\)|\.cycle \d+ \d+ (?:true|false) \(-?\d+\)|\.far (?:true|false) \d+ ⟨[^⟩]+⟩|\.proven \S+\.ctr \S+\.never)(.*)$',line)
    if m:
     term,tail=m.groups(); assert not tail or re.fullmatch(r'(?:\]\))*[,]?',tail),tail
     if tuple(t) in late:
      k,n,s=late[tuple(t)]; assert term==f'.last {n} ({s//2},{str(bool(s%2)).lower()})',(term,k,n,s)
      ns=f'BB6.Agent48OneLALate.R{k}';line=f'.bounded {ns}.parent {ns}.all_completions_weighted'+tail
      imports.add('OneLALate'+k);seen[k]+=1
     elif tuple(t) in weighted:
      k,entry=weighted[tuple(t)];ns=entry['namespace']
      assert entry['table']==t and entry['kind']=='weighted' and entry['bound']==spec['bound']
      assert term==f'.proven {ns}.ctr {ns}.never',(term,k,ns)
      line=f'.bounded {ns}.ctr {ns}.all_completions_weighted'+tail
      imports.add(spec['external_module_by_namespace'][ns]);seen_weighted[k]+=1
     else: line='.ordinary ('+term+')'+tail
    else: assert re.fullmatch(r't\w+(?:\]\))*[,]?',line),line[:120]
    advance()
   line=prefix+line
  lines.append(line)
 assert not tree and not stack,p
 text='\n'.join(lines)+'\n';text=text.replace('import FastThreeHoleAudit','import FastThreeHoleAudit\nimport WeightedAudit'+''.join('\nimport '+m for m in sorted(imports)),1)
 text=text.replace('open BB6Coverage BB6Coverage.FAR','open BB6.Agent48WeightedAudit\nopen BB6Coverage BB6Coverage.FAR',1)
 text=re.sub(r'\bfastCheck\b','BB6.Agent48WeightedAudit.check',text)
 text=re.sub(r'\bcertifiedFast\b','BB6.Agent48WeightedAudit.certified',text)
 text=re.sub(r'(^theorem h[^\n]+ := by) decide \+kernel$',r'\1\n  rw [← checkPrefix_eq]\n  decide +kernel',text,flags=re.M)
 (out/p.name).write_text(text)
assert set(seen)=={k for k,n,s in late.values()} and all(v==1 for v in seen.values()),seen
assert set(seen_weighted)=={k for k,_ in weighted.values()} and all(v==1 for v in seen_weighted.values()),seen_weighted
print('Exact late imports:',sorted(seen),'weighted external:',sorted(seen_weighted))
