from autopump import *
from pathlib import Path

def ungap(x):return G(x['g']) if isinstance(x,dict) else x
def word(w):return tuple(map(ungap,w))
def conf(c):return c[0],word(c[1]),word(c[2])
def bits(s):return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def expr(xs,n='n'):
 if not xs:return '[]'
 return ' ++ '.join(bits(x) if isinstance(x,str) else f'rep {bits(x.p)} {n}' for x in xs)
def zexpr(c,n='n'):
 return f'⟨{c[0]}, {expr(c[1],n)}, {expr(c[2],n)}⟩'
def normseq(w):
 w=normalize(w);out=[];i=0
 while i<len(w):
  if not isinstance(w[i],G) or i==0 or not isinstance(w[i-1],str):i+=1;continue
  s=w[i-1];P=w[i].p
  if s[-1]!=P[-1]:i+=1;continue
  b=s[-1];pre=normalize([*w[:i-1],s[:-1]]);suf=w[i+1:]
  v=normalize([*pre,G(b+P[:-1]),b,*suf]);out.append((w,v,pre,suf,P[:-1],b));w=v;i=0
 return w,out

def equality(w1,w2,indent='    '):
 n1,s1=normseq(w1);n2,s2=normseq(w2)
 assert n1==n2,(w1,w2,n1,n2)
 if w1==w2:return [indent+'rfl']
 out=[indent+'calc']
 for a,b,pre,suf,P,d in s1:
  out.append(indent+f'  {expr(a)} = {expr(b)} := by')
  out.append(indent+f'    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ({expr(pre)}) ({expr(suf)}) {bits(P)} {str(d=="1").lower()} n)')
 if not s1:out.append(indent+f'  {expr(w1)} = {expr(n1)} := rfl')
 for a,b,pre,suf,P,d in reversed(s2):
  out.append(indent+f'  {expr(b)} = {expr(a)} := by')
  out.append(indent+f'    symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ({expr(pre)}) ({expr(suf)}) {bits(P)} {str(d=="1").lower()} n)')
 return out

def emit(path):
 data=json.load(open(path));p=data['table'];i=int(path.stem.split('-')[1]);entry,c0,(ops,cend)=data['result'];c0=conf(c0);cend=conf(cend);target=targetnext(c0)
 out=[f'namespace H{i}',f'def ctr : PartialMachine := FAR.fromCodes {p}',f'def family (n : Nat) : Z0 := {zexpr(c0)}',f'theorem entry : run0 ctr {entry} ⟨0,[],[]⟩ = some (family 0) := rfl']
 groups=[];cur=None
 for op in ops:
  if op[0]=='step':
   if cur is None:cur=[1,conf(op[1]),conf(op[2])]
   else:cur[0]+=1;cur[2]=conf(op[2])
  else:
   if cur:groups.append(('fin',*cur));cur=None
   groups.append(('pump',conf(op[1]),conf(op[2]),op[3]))
 if cur:groups.append(('fin',*cur))
 cost0=sum(g[1] for g in groups if g[0]=='fin');cost1=sum(g[3][6] for g in groups if g[0]=='pump');out.append(f'theorem growth (n : Nat) : run0 ctr ({cost1}*n+{cost0}) (family n) = some (family (n+1)) := by')
 costs=[];hs=[]
 for j,g in enumerate(groups):
  h=f'h{j}';hs.append(h)
  if g[0]=='fin':
   _,k,a,b=g;costs.append(str(k));out.append(f'  have {h} : run0 ctr {k} {zexpr(a)} = some {zexpr(b)} := rfl')
  else:
   _,a,b,pumpdata=g;side,q,sp,dp,P,O,k,sr,dr=pumpdata;sr=word(sr);dr=word(dr)
   costs.append(f'{k}*n')
   if side=='L':lp,rp,L,R=sp,dp,sr,dr
   else:lp,rp,L,R=dp,sp,dr,sr
   out.append(f'  have {h} : run0 ctr ({k}*n) {zexpr(a)} = some {zexpr(b)} := by')
   out.append(f'    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweep{side} ctr {q} {bits(lp)} {bits(rp)} {bits(P)} {bits(O)} {k} (by intro L R; rfl) n ({expr(L)}) ({expr(R)})')
 if len(hs)==1:out.append(f'  have H := {hs[0]}')
 else:
  out.append(f'  have H := join0 {hs[0]} {hs[1]}')
  for h in hs[2:]:out.append(f'  have H := join0 H {h}')
 out.append(f'  have hcost : {"+".join(costs)} = {cost1}*n+{cost0} := by omega')
 out.append('  rw [hcost] at H')
 out.append(f'  have hlast : ({zexpr(cend)} : Z0) = {zexpr(target)} := by')
 out.append('    congr 1')
 for w,v in zip(cend[1:],target[1:]):
  if w!=v:
   out.extend(['  '+line for line in ['  ·']]+['  '+line for line in equality(w,v,'    ')])
 out.append('  rw [hlast] at H')
 out.append('  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H')
 out.append(f'#print axioms growth\nend H{i}')
 return '\n'.join(out)
