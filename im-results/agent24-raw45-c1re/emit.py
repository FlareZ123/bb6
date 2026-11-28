"""Generate exact Lean proof-tree modules from untrusted search data."""
import json,sys,lzma
from pathlib import Path
def parse(s):
 s=s.replace('_','');return [24 if v=='---' else (ord(v[2])-65)*4+int(v[0])*2+(v[1]=='R') for v in (s[i:i+3] for i in range(0,36,3))]
def string(a):
 s=['---' if x==24 else f'{(x>>1)&1}{"R" if x&1 else "L"}{chr(65+(x>>2))}' for x in a];return '_'.join(''.join(s[i:i+2]) for i in range(0,12,2))

def bools(s):return 'true' if s else 'false'
def bits(s):return '['+','.join(bools(x=='1') for x in s)+']'
def move(v):return f'⟨{bools(v&2)},{bools(v&1)},{v>>2}⟩'
def slot(j):return f'({j//2},{bools(j%2)})'
def table(p):
 return 'fun s => match s.1.val,s.2 with\n'+''.join(f'  | {j//2},{bools(j%2)} => some (some {move(v)})\n' for j,v in enumerate(p) if v!=24)+'  | _,_ => none'
def word(w):
 if not w:return '(.lit [])'
 if w[0].startswith('*'):return f'(.periodic [] {bits(w[0][1:])} {word(w[1:])})'
 if len(w)==1:return f'(.lit {bits(w[0])})'
 assert w[1].startswith('*'),w
 return f'(.periodic {bits(w[0])} {bits(w[1][1:])} {word(w[2:])})'
def pump(c):
 _,_,entry,(q,l,r),a,b,ops=c
 groups=[]
 for op in ops:
  if isinstance(op,int):groups.append(f'List.replicate {op} .step')
  else:
   side,lp,rp,P,O,L,R,k=op
   groups.append(f'[.{"left" if side=="L" else "right"} {bits(lp)} {bits(rp)} {bits(P)} {bits(O)} {word(L)} {word(R)} {k}]')
 return f'(.pump ⟨{entry},⟨{q},{word(l)},{word(r)}⟩,1,('+' ++ '.join(groups)+f'),{a},{b}⟩)'
def trie(xs):
 if not xs:return '.empty'
 if xs==[0]:return '.leaf'
 return '(.branch '+trie([x//2 for x in xs if x%2==0])+' '+trie([x//2 for x in xs if x%2==1])+')'
def gram(c):
 _,_,cert=c
 _,k,n,L,R,S=cert.split();k=int(k);M=1<<k
 rows=[[] for _ in range(12)]
 for j in map(int,S.rstrip(',').split(',')):rows[j//(M*M)].append(j%(M*M))
 assert sum(map(len,rows))==int(n)
 edge=lambda s:hex(sum(int(x)<<(2*j) for j,x in enumerate(s)))
 return f'(.ngram ⟨{k-1},{edge(L)},{edge(R)},#['+','.join(trie(r) for r in rows)+']⟩)'

def generate(j,folder,prefix="Raw45Re"):
 out=Path(folder);out.mkdir(exist_ok=True,parents=True)
 bound=j['maxquery']+1
 def header(name,imports):return '\n'.join('import '+i for i in imports)+f'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent24Raw45.{name}\nopen BB6Coverage BB6.Agent24Raw45.ReAudit\n'
 def body(t,p,path):
  k=t[0]
  if k=='cycle':return f'.cycle {t[1]} {t[2]} {bools(t[3])} ({t[4]})'
  if k=='last':return f'.last {t[1]} {slot(t[2])}'
  if k=='pump':
   c=j['pumps'][t[1]];assert parse(c[1])==p,(c,p);return pump(c)
  if k=='ngram':
   c=j['ngrams'][t[1]];assert parse(c[1])==p,(c,p);return gram(c)
  if k=='quad':
   assert string(p)=='1RB1LB_1RC0LA_0RD1RE_1LD1RB_1LA1RF_---0RB'
   return '.proven BB6.Agent24Raw45.ReQuadratic.table BB6.Agent24Raw45.ReQuadratic.never'
  if k=='split':
   _,n,s,kids=t;assert p[s]==24 and len(kids)==24
   rs=[]
   for v,x in enumerate(kids):
    pp=p[:s]+[v]+p[s+1:]
    if x[0]=='split':
     name=emit(x,pp,path+'_'+str(v));rs.append(f'.covered {name}P {name}Cover')
    else:rs.append(body(x,pp,path+'_'+str(v)))
   return f'.split {n} {slot(s)} (byMove [\n  '+',\n  '.join(rs)+'\n])'
  raise ValueError(t)
 def emit(t,p,path):
  name='node'+path
  a=body(t,p,path)
  lines.append(f'-- {string(p)}\ndef {name}P : PartialMachine := {table(p)}\ndef {name}A : Audit {bound} := {a}\ntheorem {name}OK : check {bound} {name}P {name}A = true := by decide +kernel\ntheorem {name}Cover : Cover (DecidedBelow {bound}) {name}P := sound _ _ _ {name}OK\n')
  return name
 parent=parse(j['parent']);kind,n,s,kids=j['tree'];assert kind=='split'
 names=[]
 for v,t in enumerate(kids):
  name=f'{prefix}Child{v:02}';names.append(name);lines=[]
  p=parent[:s]+[v]+parent[s+1:];node=emit(t,p,'Root')
  lines.append(f'abbrev parent := {node}P\ntheorem cover : Cover (DecidedBelow {bound}) parent := {node}Cover\n#print axioms cover\nend BB6.Agent24Raw45.{name}\n')
  (out/(name+'.lean')).write_text(header(name,['Raw45ReAudit'])+'\n'.join(lines))
 name=prefix+'Parent';rs=[f'.covered BB6.Agent24Raw45.{name}.parent BB6.Agent24Raw45.{name}.cover' for name in names];lines=[]
 lines.append(f'def parent : PartialMachine := {table(parent)}\ndef audit : Audit {bound} := .split {n} {slot(s)} (byMove [\n  '+',\n  '.join(rs)+f'\n])\ntheorem checked : check {bound} parent audit = true := by decide +kernel\ntheorem cover : Cover (DecidedBelow {bound}) parent := sound _ _ _ checked\n#print axioms cover\nend BB6.Agent24Raw45.{name}\n')
 (out/(name+'.lean')).write_text(header(name,names)+'\n'.join(lines))
 print('bound',bound,'modules',len(names)+1,'bytes',sum((out/(x+'.lean')).stat().st_size for x in names+[name]))

if __name__=='__main__':
 with (lzma.open(sys.argv[1],'rt') if sys.argv[1].endswith('.xz') else open(sys.argv[1])) as f:
  generate(json.load(f),sys.argv[2],*sys.argv[3:])
