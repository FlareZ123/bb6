"""Generate parametric anchor transitions for the two-alphabet counter."""
from symbolsweep46 import *
from pathlib import Path
D='010010'; A='010101'; B='101010'
TABLE='1RB1LD1RC0LD1LA1RE0RF0LA1RB0RC---0RB'
CASES=[('a1','010001X','010111X',A),('a2','010111X','010011X',A),('a3','0100110X','1010100X',B),('b0','101010X','001010X',B),('b1','001010X','111010X',B),('b2','111010X','011010X',B),('b3','011010X',D+'X',A),('a0',A+'X','010001X',A),('t011','011','0100',A),('t0100','0100','01011',A),('t01011','01011','01001',A),('t01001','01001',B+'11',B),('t11','11','01',B),('t01','01','01011',A)]

def bits(s):
    if 'X' in s:
        assert s.endswith('X') and s.count('X')==1
        return '('+bits(s[:-1])+' ++ R)' if s[:-1] else 'R'
    return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def wexpr(w):
    if not w.block:return bits(w.pre)
    p=[]
    if w.pre:p.append(bits(w.pre))
    p.append(f'rep {bits(w.block)} k')
    if w.suf:p.append(bits(w.suf))
    return '('+' ++ '.join(p)+')'
def zexpr(z):return f'⟨{z[0]},{wexpr(z[1])},{wexpr(z[2])}⟩'
def normeq(a,b):return a==b or (a.block==b.block and a.pull()==b.pull())
SIMP='List.append_assoc,List.nil_append,List.append_nil,List.cons_append'

def generate(name,x,y,v):
    stop=lambda z,n:n>0 and z[0]==0 and z[1].value(0)=='000' and z[2].value(0)==D+y and z[2].value(1)==D+v+y
    z,ops=symrun(TABLE,W('000'),W(D,D,x),stop,5000)
    assert stop(z,len(ops))
    transformed=[]
    for op in ops:
        kind,a,b,*rest=op
        if kind=='raw':
            def expose(w):
                if not w.pre and w.block and w.suf.startswith(w.block):return W(w.block,w.block,w.suf[len(w.block):])
                return w
            q,l,r=a;l1=expose(l);d=tab(TABLE)[2*q+int(l1.pre[0] if l1.pre else '0')][1];r1=expose(r) if d else r
            a1=(q,l1,r1)
            if a!=a1:assert normeq(l,l1) and normeq(r,r1);transformed.append(('eq',a,a1))
            assert primitive(tab(TABLE),a1)==b
            transformed.append(('raw',a1,b))
        else:
            t,d,rp,lp,C,O,inp,out=rest[0];a1=(a[0],out,inp) if d else (a[0],inp,out)
            if a1!=a:transformed.append(('eq',a,a1))
            transformed.append(('sweep',a1,b,rest[0]))
    seg=[];j=0
    while j<len(transformed):
        op=transformed[j];kind,a,b,*rest=op
        if kind=='raw':
            end=j+1
            while end<len(transformed) and transformed[end][0]=='raw':end+=1
            seg.append(('raw',a,transformed[end-1][2],end-j));j=end
        else:seg.append(op);j+=1
    args='(k : Nat)'+(' (R : List Bool)' if x.endswith('X') else '')
    rarg=' R' if x.endswith('X') else ''
    lines=[f'namespace {name}'];emit=lines.append
    def eqProof(a,b):
        assert normeq(a,b)
        if a==b:return 'rfl'
        c=a.pull();C=a.block;x=(len(a.pre)-len(c.pre))//len(C);y=(len(b.pre)-len(c.pre))//len(C);d=abs(x-y)
        smaller,larger=(a,b) if x<y else (b,a)
        assert smaller.suf.startswith(C*d) and larger.pre==smaller.pre+C*d and larger.suf==smaller.suf[len(C)*d:]
        body=(bits(smaller.pre)+' ++ ' if smaller.pre else '')+'w'+(' ++ '+bits(larger.suf) if larger.suf else '')
        base=f'congrArg (fun w : List Bool => {body}) (commute {bits(C)} {d} k)'
        return f'by simpa only [{SIMP},rep] using {"("+base+").symm" if x<y else base}'
    cost=[]
    for i,op in enumerate(seg):
        kind,a,b,*rest=op
        emit(f'def z{i} {args} : Z0 := {zexpr(a)}')
        c=rest[0] if kind=='raw' else 0 if kind=='eq' else f'{rest[0][0]}*k';cost.append(str(c))
        if kind=='raw':emit(f'theorem seg{i} {args} : run0 p {c} (z{i} k{rarg}) = some ({zexpr(b)} : Z0) := by rfl')
        elif kind=='eq':emit(f'theorem seg{i} {args} : run0 p 0 (z{i} k{rarg}) = some ({zexpr(b)} : Z0) := by\n  have hL : {wexpr(a[1])} = {wexpr(b[1])} := {eqProof(a[1],b[1])}\n  have hR : {wexpr(a[2])} = {wexpr(b[2])} := {eqProof(a[2],b[2])}\n  simp only [run0,z{i},hL,hR]')
        else:
            t,d,rp,lp,C,O,inp,out=rest[0]
            if d:lemma=f'sweepR p {a[0]} {bits(lp)} {bits(rp)} {bits(C)} {bits(O)} {t}';param=f'k {bits(out.pre[len(lp):])} {bits(inp.suf)}'
            else:lemma=f'sweepL p {a[0]} {bits(rp)} {bits(lp)} {bits(C)} {bits(O)} {t}';param=f'k {bits(inp.suf)} {bits(out.pre[len(lp):])}'
            emit(f'theorem seg{i} {args} : run0 p ({c}) (z{i} k{rarg}) = some ({zexpr(b)} : Z0) := by\n  simpa only [z{i},{SIMP}] using {lemma} (by intro L R; rfl) {param}')
    emit(f'def z{len(seg)} {args} : Z0 := {zexpr(z)}')
    ex=z[2].pre[len(D):];copies=len(ex)//len(v);part=ex[copies*len(v):];rem=v[len(part):]
    assert ex==v*copies+part and v.startswith(part) and z[2].block==rem+part and ex+z[2].suf==y
    emit(f'theorem endpoint {args} : z{len(seg)} k{rarg} = (⟨0,[false,false,false],{bits(D)} ++ rep {bits(v)} k ++ {bits(y)}⟩ : Z0) := by')
    if part:
        body=f'{bits(D+v*copies)} ++ w ++ {bits(z[2].suf)}'
        emit(f'  have h := congrArg (fun w : List Bool => {body}) (rotateList {bits(part)} {bits(rem)} k)')
        emit(f'  have h1 : {wexpr(z[2])} = ({bits(D+v*copies)} ++ rep {bits(v)} k ++ {bits(part+z[2].suf)}) := by simpa only [{SIMP}] using h')
    else:emit(f'  have h1 : {wexpr(z[2])} = ({bits(D+v*copies)} ++ rep {bits(v)} k ++ {bits(z[2].suf)}) := rfl')
    if copies:
        emit(f'  have h2 := congrArg (fun w : List Bool => {bits(D)} ++ w ++ {bits(part+z[2].suf)}) (commute {bits(v)} {copies} k)')
        emit(f'  have h3 : ({bits(D+v*copies)} ++ rep {bits(v)} k ++ {bits(part+z[2].suf)}) = ({bits(D)} ++ rep {bits(v)} k ++ {bits(y)}) := by simpa only [{SIMP},rep] using h2')
        emit(f'  simp only [z{len(seg)},h1,h3]')
    else:emit(f'  simp only [z{len(seg)},h1]')
    c0=sum(int(c) for c in cost if '*' not in c);c1=sum(int(c.split('*')[0]) for c in cost if '*' in c)
    emit(f'theorem step {args} : run0 p ({c0}+{c1}*k) (⟨0,[false,false,false],{bits(D)} ++ rep {bits(D)} k ++ {bits(x)}⟩ : Z0) = some (⟨0,[false,false,false],{bits(D)} ++ rep {bits(v)} k ++ {bits(y)}⟩ : Z0) := by')
    expr=f'(seg0 k{rarg})'
    for i in range(1,len(seg)):expr=f'(join0 {expr} (seg{i} k{rarg}))'
    emit(f'  have h : run0 p ({"+" .join(cost)}) (z0 k{rarg}) = some (z{len(seg)} k{rarg}) := {expr}')
    emit(f'  rw [endpoint] at h\n  rw [show ({"+" .join(cost)})={c0}+{c1}*k by omega] at h\n  exact h')
    emit(f'end {name}');return '\n'.join(lines)

head='''import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent46Raw13RCCounter
open BB6Coverage BB6Coverage.Agent31Pump
abbrev p : PartialMachine := FAR.fromCodes [7,14,11,12,2,19,21,0,7,9,24,5]
theorem rep_add2 (B : List Bool) (n m : Nat) : rep B (n+m) = rep B n ++ rep B m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [Nat.succ_add,rep,ih]; simp [rep,List.append_assoc]
theorem commute (B : List Bool) (n k : Nat) : rep B n ++ rep B k = rep B k ++ rep B n := by
  rw [← rep_add2, ← rep_add2, Nat.add_comm n k]
theorem rotateList (a b : List Bool) (k : Nat) : a ++ rep (b++a) k = rep (a++b) k ++ a := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp only [rep,List.append_assoc,←ih]
'''
if __name__=='__main__':
    src=head+'\n'.join(generate(*c) for c in CASES)+'\nend BB6.Agent46Raw13RCCounter\n'
    Path(__file__).with_name('Raw13RCCounterMacro.lean').write_text(src)
