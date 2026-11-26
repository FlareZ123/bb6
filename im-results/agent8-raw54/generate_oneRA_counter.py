"""Two independent arbitrary repeats, and nine variants sharing the carry loop."""
from generate_digit_sections import C,M,w,sweep,rotations
from dataclasses import dataclass
from collections import deque
from pathlib import Path
import sys

@dataclass(frozen=True)
class D:
 q:int;l:str;r:str;ps:tuple

def project(c,i):
 x='VW'[i];y='WV'[i]
 return C(c.q,c.l.replace(y,'H').replace(x,'V'),c.r.replace(y,'H').replace(x,'V'),c.ps[i])
def lift(c,d,i):
 x='VW'[i];y='WV'[i];ps=list(c.ps);ps[i]=d.p
 return D(d.q,d.l.replace('V',x).replace('H',y),d.r.replace('V',x).replace('H',y),tuple(ps))
def sweeps(m,c):
 for i in range(2):
  for t,d,info in sweep(m,project(c,i)):
   yield t,lift(c,d,i),(i,info)
def rots(c):
 for i in range(2):
  for d,info in rotations(project(c,i)):
   yield lift(c,d,i),(i,info)
def eq(c):
 seen={c};todo=deque([(c,[])])
 while todo:
  u,path=todo.popleft();yield u,path
  for v,info in rots(u):
   if v not in seen and len(seen)<256:seen.add(v);todo.append((v,path+[(v,info)]))
def replay2(m,start,target,coeff):
 c=start;ops=[];cost=[0,0,0];seen=set()
 for _ in range(1000):
  if any(x>y for x,y in zip(cost,coeff)) or c in seen:return
  es=list(eq(c));seen.add(c)
  if tuple(cost)==coeff:
   for v,path in es:
    if v==target:
     for d,info in path:ops.append(('rotate',c,d,info));c=d
     return ops
  found=None
  for v,path in es:
   for t,d,info in sweeps(m,v):
    if cost[info[0]]+t<=coeff[info[0]]:found=v,path,t,d,info;break
   if found:break
  if found:
   v,path,t,d,info=found
   for x,ii in path:ops.append(('rotate',c,x,ii));c=x
   ops.append(('sweep',v,d,(t,info)));c=d;cost[info[0]]+=t;continue
  for v,path in es:
   z=m.step(v.q,v.l,v.r)
   if z is not None and cost[2]<coeff[2]:
    for x,ii in path:ops.append(('rotate',c,x,ii));c=x
    d=D(*z,v.ps);ops.append(('step',v,d,1));c=d;cost[2]+=1;break
  else:return

def word(s,ps):
 xs=[];buf=''
 for c in s:
  if c in '01':buf+=c;continue
  if buf:xs.append(w(buf));buf=''
  if c in 'VW':i='VW'.index(c);xs.append(f'(rep {w(ps[i])} {"jk"[i]})')
  elif c=='X':xs.append('T')
  else:raise ValueError(c)
 if buf:xs.append(w(buf))
 return '('+' ++ '.join(xs)+')' if len(xs)>1 else (xs[0] if xs else '[]')
def cfg2(c):return f'⟨{c.q},{word(c.l,c.ps)},{word(c.r,c.ps)}⟩'
def prove2(name,start,target,coeff,ops,tail):
 a,b,cost=coeff;lines=[f'theorem {name} (j k : Nat)'+(' (T : List Bool)' if tail else '')+f' : run0 table ({a}*j+{b}*k+{cost}) {cfg2(start)} = some {cfg2(target)} := by'];cur=None;times=[];j=0;i=0
 while i<len(ops):
  kind,c,d,info=ops[i];i+=1
  if kind=='step':
   t=1
   while i<len(ops) and ops[i][0]=='step':d=ops[i][2];i+=1;t+=1
   time=str(t);proof='by rfl'
  elif kind=='sweep':
   t,(v,(left,pre,dp,suf,ds,p,o))=info
   ren=lambda s:s.replace('V','VW'[v]).replace('H','WV'[v]);lp,rp=(pre,dp) if left else (dp,pre);L,R=(suf,ds) if left else (ds,suf)
   n='jk'[v];time=f'({t}*{n})';proof=f'by\n    simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using sweep{"L" if left else "R"} table {c.q} {w(lp)} {w(rp)} {w(p)} {w(o)} {t} (fun _ _ => rfl) {n} {word(ren(L),c.ps)} {word(ren(R),c.ps)}'
  elif kind=='rotate':
   v,(typ,left,pre,bit,p,suf)=info;ren=lambda s:s.replace('V','VW'[v]).replace('H','WV'[v]);n='jk'[v];arg=f'moveCut {word(ren(pre),c.ps)} {word(ren(suf),c.ps)} {w(p)} {str(bit=="1").lower()} {n}'
   if typ=='rotR':arg=f'({arg}).symm'
   f=f'fun x => (⟨{c.q},x,{word(c.r,c.ps)}⟩ : Z0)' if left else f'fun x => (⟨{c.q},{word(c.l,c.ps)},x⟩ : Z0)'
   lines.extend([f'  have e{j} : ({cfg2(c)} : Z0) = {cfg2(d)} := by',f'    simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using congrArg ({f}) ({arg})'])
   if cur is not None:lines.append(f'  rw [e{j}] at {cur}');j+=1;continue
   time='0';proof=f'by rw [e{j}]; rfl'
  else:raise ValueError(kind)
  lines.append(f'  have h{j} : run0 table {time} {cfg2(c)} = some {cfg2(d)} := {proof}');times.append(time)
  if cur is None:cur=f'h{j}'
  else:lines.append(f'  have g{j} := join0 {cur} h{j}');cur=f'g{j}'
  j+=1
 lines.append(f'  rw [show {"+".join(times)}={a}*j+{b}*k+{cost} by omega] at {cur}\n  exact {cur}');return '\n'.join(lines)

ENTRIES=[(18,104,0,'1'),(27,104,0,'1'),(137,142,0,'001'),(184,142,0,'001'),(219,178,2,'1'),(276,144,0,'001'),(334,264,3,'01'),(339,506,6,'1'),(364,920,7,'00001')]
def emit(rows,out):
 m=M(rows[18]);m.a[5]='---';P='001100111';Z='00000'
 lines=['import Raw54BinaryShape','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent8Raw54.OneRACounter','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.DigitSection BB6.Agent8Raw54.BinaryShape','def table (c1 : Move) : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for j,a in enumerate(m.a):
  if j==5:lines.append('  | 2,true => some (some c1)');continue
  if a=='---':continue
  b,r,q=a;lines.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(b=="1").lower()},{str(r=="R").lower()},{ord(q)-65}⟩)')
 lines+=['  | _,_ => none','section','variable (c1 : Move)']
 for tail in (True,False):
  start=D(0,'01',P+'V'+Z+'W'+('000X' if tail else ''),('0011','111'));target=D(0,'01',P+'0011V'+Z+'W111'+('X' if tail else ''),('0011','000'));ops=replay2(m,start,target,(16,8,98));assert ops
  lines.append(prove2('stop' if tail else 'over',start,target,(16,8,98),ops,tail).replace(' table ', ' (table c1) '))
 lines.append('''def z : List Bool := [false,false,false]
def o : List Bool := [true,true,true]
def f (p : Nat × List Bool) : Z0 :=
  ⟨0,[false,true],[false,false,true,true,false,false,true,true,true] ++ rep [false,false,true,true] p.1 ++ [false,false,false,false,false] ++ enc z o p.2⟩
theorem closed (p : Nat × List Bool) : ∃ t p', 0 < t ∧ run0 (table c1) t (f p) = some (f p') := by
  obtain ⟨j,xs⟩ := p
  rcases shape xs with ⟨k,ys,h⟩ | ⟨k,h⟩
  · subst xs
    refine ⟨16*j+8*k+98,(j+1,rep [false] k ++ true::ys),by omega,?_⟩
    simpa only [f,enc_append,enc_ones,enc_zeros,enc,z,o,rep,List.cons_append,List.append_assoc,List.nil_append,List.append_nil] using stop c1 j k (enc z o ys)
  · subst xs
    refine ⟨16*j+8*k+98,(j+1,rep [false] k ++ [true]),by omega,?_⟩
    simpa only [f,enc_append,enc_ones,enc_zeros,enc,z,o,rep,List.cons_append,List.append_assoc,List.nil_append,List.append_nil] using over c1 j k
end''')
 for i,t,j,ds in ENTRIES:
  b,r,q=M(rows[i]).a[5];lines.append(f'''namespace M{i}
abbrev table : PartialMachine := OneRACounter.table ⟨{str(b=='1').lower()},{str(r=='R').lower()},{ord(q)-65}⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.RAClosed.neverOfSection table (Nat × List Bool) f ({j},{w(ds)}) {t} (by rfl) (closed _) m hm
#print axioms never
end M{i}''')
 lines.append('end BB6.Agent8Raw54.OneRACounter');out.joinpath('Raw54OneRACounter.lean').write_text('\n'.join(lines)+'\n')
if __name__=='__main__':
 emit(Path(sys.argv[1]).read_text().splitlines(),Path(sys.argv[2]))
