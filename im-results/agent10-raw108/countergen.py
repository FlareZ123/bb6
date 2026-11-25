"""Untrusted symbolic macro generator; every emitted phase is kernel checked."""
from parametric_engine import C,clean,lit,rep,opaque,prefix,rest,normalization
import parametric_engine as engine
from pathlib import Path
from itertools import product

def bits(w):return '['+','.join('true' if x=='1' else 'false' for x in w)+']'
def app(*args):return ' ++ '.join(x for x in args if x!='[]') or '[]'
def word(w):return app(*[bits(s) if b==0 else f'rep {bits(s)} n' if b==1 else s for s,b in w])
def cf(q,l,r):return f'⟨{q},{l},{r}⟩'
def cfg(c):return cf(c.q,word(c.l),word(c.r))
SIMP='List.nil_append,List.append_nil,List.append_assoc,List.cons_append'

def wordeq(name,a,b):
 lhs=word(a) if a else '([] : List Bool)';ls=[f'theorem {name} (n : Nat) (R : List Bool) : {lhs} = {word(b)} := by']
 if a==b:return '\n'.join(ls+['  rfl'])
 x,xs=normalization(a);y,ys=normalization(b);assert x==y,(name,a,b,x,y)
 while xs and ys and xs[-1]==ys[-1]:xs.pop();ys.pop()
 ls.append('  calc')
 for _,v,pre,suf,k,z in xs:ls.append(f'    _ = {word(v)} := by simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
 for v,_,pre,suf,k,z in reversed(ys):ls.append(f'    _ = {word(v)} := by symm; simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
 return '\n'.join(ls)

def macro(name,st,tg,src=None,dst=None):
 hist,last=engine.pump(st,tg,500);assert hist is not None,(name,st,tg,last)
 src=src or st;dst=dst or tg
 ls=[];seg=[];i=0
 while i<len(hist):
  x=hist[i]
  if x[0]=='step':
   j=i+1
   while j<len(hist) and hist[j][0]=='step':j+=1
   seg.append(('fixed',x[1],hist[j-1][2],j-i));i=j
  else:seg.append(x);i+=1
 costs=[]
 for j,x in enumerate(seg):
  typ,c,d,k=x[:4]
  if typ=='fixed':
   ls.append(f'theorem {name}P{j} (n : Nat) (R : List Bool) : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
  _,_,_,k,side,I,O,cut=x
  if side=='L':
   lp,rp=prefix(c.l),prefix(c.r)[:cut];L,R=rest(c.l)[1:],clean(lit(prefix(c.r)[cut:])+rest(c.r));s=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));d0=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
  else:
   lp,rp=prefix(c.l)[:cut],prefix(c.r);L,R=clean(lit(prefix(c.l)[cut:])+rest(c.l)),rest(c.r)[1:];s=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));d0=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
  ls.append(f'theorem {name}L{j} (L R : List Bool) : run0 table {k} {s} = some {d0} := by rfl')
  ls.append(f'theorem {name}P{j} (n : Nat) (R : List Bool) : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} {name}L{j} n ({word(L)}) ({word(R)})')
  costs.append(f'{k}*n')
 a=sum(x[3] for x in seg if x[0]=='fixed');b=sum(x[3] for x in seg if x[0]=='loop');join=f'({name}P0 n R)'
 for j in range(1,len(seg)):join=f'(join0 {join} ({name}P{j} n R))'
 for nm,c,d in [(name+'Src',st,src),(name+'Dst',last,dst)]:
  if c==d:continue
  assert c.q==d.q
  ls.extend([wordeq(nm+'L',c.l,d.l),wordeq(nm+'R',c.r,d.r)])
  ls.append(f'theorem {nm} (n : Nat) (R : List Bool) : ({cfg(c)} : Z0) = {cfg(d)} := by rw [{nm}L n R, {nm}R n R]')
 proof=f'theorem {name} (n : Nat) (R : List Bool) : run0 table ({a}+{b}*n) {cfg(src)} = some {cfg(dst)} := by\n  have H := {join}\n'
 if st!=src:proof+=f'  rw [{name}Src n R] at H\n'
 if last!=dst:proof+=f'  rw [{name}Dst n R] at H\n'
 proof+=f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H\n  exact H"
 ls.append(proof)
 return '\n\n'.join(ls),a,b

def table(code):
 p=code.replace('_','');p=tuple(p[i:i+3] for i in range(0,36,3));engine.p=p
 return 'def table : PartialMachine := fun s =>\n  match s.1.val,s.2 with\n'+'\n'.join(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)' for i,a in enumerate(p) if a!='---')+'\n  | _,_ => none'

def d(pre,block,suf,tail=False):return C(3,clean(lit(pre)+rep(block)+lit(suf)+(opaque('R') if tail else ())),())

def gen1279(f,ns):
 code=f'1RB0RF_1RC0LE_0RD1RB_1LD1RE_0RA1LB_{f}---'
 ls=['import SweepPumping',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump','set_option maxRecDepth 100000','set_option maxHeartbeats 0',table(code)]
 specs=[('startRaw',d('001','1111','11111'),d('00','1111','1100010111'),d('00','1111','111111'),None),('decRaw',d('001','1111','1111100010111',True),d('00','1111','1100010111010111',True),d('00','1111','11111100010111',True),None),('incRaw',d('001','11','1010111',True),d('00','11','1111111111',True),d('00','11','11010111',True),None),('exitRaw',d('001100010111','010111',''),d('0011010111010111','010111',''),None,None)]
 for nm,s,t,s0,t0 in specs:
  text,a,b=macro(nm,s,t,s0,t0);ls.append(text);print(f,nm,a,b)
 K=44 if f=='0RB' else 42
 ls.append(f'''
abbrev T : List Bool := [true,true]
abbrev U : List Bool := [false,true,false,true,true,true]
abbrev P : List Bool := [false,false]

theorem repAppend (w : List Bool) (a b : Nat) : rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep]; simp only [List.append_assoc]

theorem repFour (n : Nat) : rep [true,true,true,true] n = rep T (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,repAppend T (2*n) 2]
    have h : rep [true,true,true,true] (n+1) = rep [true,true,true,true] n ++ [true,true,true,true] := (rep_snoc _ n).symm
    rw [h,ih]
    rfl

def X (n b : Nat) : Z0 := ⟨3,P ++ rep [true,true,true,true] n ++ T ++ P ++ rep U (b+1),[]⟩
def Y (n b : Nat) : Z0 := ⟨3,P ++ rep T n ++ T ++ rep U b,[]⟩

theorem start (n : Nat) : run0 table ({K}+16*n) (Y (2*n+2) 0) = some (X n 0) := by
  have H := startRaw n []
  unfold Y X
  rw [repAppend T (2*n) 2, ← repFour]
  simpa only [rep,T,U,P,{SIMP}] using H

theorem dec (n b : Nat) : run0 table ({K}+16*n) (X (n+1) b) = some (X n (b+1)) := by
  have H := decRaw n (rep U b)
  unfold X
  have he : rep [true,true,true,true] (n+1) = rep [true,true,true,true] n ++ [true,true,true,true] := (rep_snoc _ n).symm
  rw [he]
  simpa only [rep,T,U,P,{SIMP}] using H

theorem inc (n b : Nat) : run0 table (24+8*n) (Y n (b+1)) = some (Y (n+4) b) := by
  have H := incRaw n (rep U b)
  unfold Y
  rw [repAppend T n 4]
  simpa only [rep,T,U,P,{SIMP}] using H

theorem exitX (b : Nat) : run0 table 28 (X 0 b) = some (Y 0 (b+2)) := by
  have H := exitRaw b []
  simpa only [X,Y,repAppend,rep,T,U,P,{SIMP},Nat.zero_mul,Nat.mul_zero,Nat.add_zero] using H

def decCost : Nat → Nat
  | 0 => 0
  | n+1 => {K}+16*n+decCost n

theorem decAll (n b : Nat) : run0 table (decCost n) (X n b) = some (X 0 (b+n)) := by
  induction n generalizing b with
  | zero => simp [decCost,run0]
  | succ n ih => simpa only [decCost,show b+1+n=b+(n+1) by omega] using join0 (dec n b) (ih (b+1))

def incCost (n : Nat) : Nat → Nat
  | 0 => 0
  | b+1 => 24+8*n+incCost (n+4) b

theorem incAll (n b : Nat) : run0 table (incCost n b) (Y n b) = some (Y (n+4*b) 0) := by
  induction b generalizing n with
  | zero => simp [incCost,run0]
  | succ b ih => simpa only [incCost,show n+4+4*b=n+4*(b+1) by omega] using join0 (inc n b) (ih (n+4))

def epochCost (m : Nat) : Nat := let n := 2*m+1; {K}+16*n+decCost n+28+incCost 0 (n+2)
theorem epoch (m : Nat) : run0 table (epochCost m) (Y (4*m+4) 0) = some (Y (4*(2*m+2)+4) 0) := by
  let n := 2*m+1
  have D := decAll n 0
  rw [Nat.zero_add] at D
  have H := join0 (join0 (join0 (start n) D) (exitX n)) (incAll 0 (n+2))
  simpa only [epochCost,n,Nat.zero_add,show 2*(2*m+1)+2=4*m+4 by omega,show 4*(2*m+1+2)=4*(2*m+2)+4 by omega] using H

def index : Nat → Nat
  | 0 => 0
  | k+1 => 2*index k+2

def family (k : Nat) : Z0 := Y (4*index k+4) 0

theorem entry : run0 table 55 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (epochCost (index k)) (family k) = some (family (k+1)) := by
  simpa only [family,index] using epoch (index k)

theorem positive (m : Nat) : 0 < epochCost m := by simp only [epochCost]; omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 55 (fun k => epochCost (index k)) entry (fun k => positive (index k)) growth m hm

#print axioms epoch
#print axioms growth
#print axioms never
end {ns}
''')
 return '\n\n'.join(ls)+'\n'
def main():
 for f,i in [('0RB',1279),('0RC',1280)]:
  n=f'Raw108LE{i}';Path(__file__).with_name(n+'.lean').write_text(gen1279(f,'BB6.Agent10'+n))
if __name__=='__main__':main()
