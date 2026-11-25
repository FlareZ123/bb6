"""Exact candidate macro emitter for the two nested-sweep residuals.
Each local equation is checked on arbitrary untouched tails; X is an
arbitrary right-hand suffix, never read by the macro.
"""
import multi as m
from generate_sweeps import bits, app, tab, show
from pathlib import Path
SIMP="List.append_assoc,List.cons_append,List.nil_append,List.append_nil"

def word(w):
    return app(*[("R" if s=="X" else f"rep {bits(s)} n") if b else bits(s) for s,b in w])
def cfg(c):
    return f"⟨{c.q},{word(c.l)},{word(c.r)}⟩"
def cf(q,l,r):
    return f"⟨{q},{l},{r}⟩"
def generate_macro(p, name, st, tg):
    h=m.pump(p,st,tg,3000)
    assert h,(name,st,tg)
    hist,last=h;seg=[];i=0
    while i<len(hist):
        x=hist[i]
        if x[0]=="step":
            j=i+1
            while j<len(hist) and hist[j][0]=="step":j+=1
            seg.append(("fixed",x[1],hist[j-1][2],j-i));i=j
        else:seg.append(x);i+=1
    ls=[f"namespace {name}"];costs=[]
    opaque=("X",True) in st.r
    binders="(n : Nat)"+(" (R : List Bool)" if opaque else "")
    args="n"+(" R" if opaque else "")
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4]
        if typ=="fixed":
            ls.append(f"theorem phase{j} {binders} : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl")
            costs.append(str(k));continue
        _,_,_,k,side,I,O,cut=x
        if side=="L":
            lp,rp=m.prefix(c.l),m.prefix(c.r)[:cut]
            L,R=m.rest(c.l)[1:],m.clean(m.lit(m.prefix(c.r)[cut:])+m.rest(c.r))
            src=cf(c.q,app(bits(lp),bits(I),"L"),app(bits(rp),"R"))
            dst=cf(c.q,app(bits(lp),"L"),app(bits(rp),bits(O),"R"))
        else:
            lp,rp=m.prefix(c.l)[:cut],m.prefix(c.r)
            L,R=m.clean(m.lit(m.prefix(c.l)[cut:])+m.rest(c.l)),m.rest(c.r)[1:]
            src=cf(c.q,app(bits(lp),"L"),app(bits(rp),bits(I),"R"))
            dst=cf(c.q,app(bits(lp),bits(O),"L"),app(bits(rp),"R"))
        assert I not in ("X","Y") and O not in ("X","Y")
        ls.append(f"theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl")
        ls.append(f"theorem phase{j} {binders} : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} n ({word(L)}) ({word(R)})")
        costs.append(f"{k}*n")
    for side in ["l","r"]:
        a,b=getattr(last,side),getattr(tg,side)
        if a==b:continue
        x,xs=m.normalization(a);y,ys=m.normalization(b)
        assert x==y
        while xs and ys and xs[-1]==ys[-1]:xs.pop();ys.pop()
        ls.append(f'theorem final{side} {binders} : {word(a) if a else "([] : List Bool)"} = {word(b)} := by\n  calc')
        for _,v,pre,suf,k,z in xs:
            ls.append(f'    _ = {word(v)} := by simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
        for v,_,pre,suf,k,z in reversed(ys):
            ls.append(f'    _ = {word(v)} := by symm; simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
    a=sum(x[3] for x in seg if x[0]=="fixed")
    b=sum(x[3] for x in seg if x[0]=="loop")
    proof=f"theorem equation {binders} : run0 table ({a}+{b}*n) {cfg(st)} = some {cfg(tg)} := by\n"
    join=f"(phase0 {args})"
    for j in range(1,len(seg)):join=f"(join0 {join} (phase{j} {args}))"
    proof+=f"  have H := {join}\n"
    for side in ["l","r"]:
        if getattr(last,side)!=getattr(tg,side):proof+=f"  rw [final{side} {args}] at H\n"
    proof+=f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H\n  exact H"
    ls.extend([proof,f"end {name}"])
    return "\n\n".join(ls),a,b

def generate_nested(idx,p):
    L=m.lit;R=m.rep;C=m.C;clean=m.clean
    out=[f"namespace M{idx}",f"-- {show(p)}",tab(p)]
    if idx==2140:
        for j in range(5):
            st=C(0,(),clean(L("001010")+R("10")+L("1"*j)+(R("X") if j==4 else ())))
            if j==4:tg=C(0,(),clean(L("001010101010")+R("10")+R("X")))
            elif j>=2:tg=C(4,(),clean(L("1"*(7+2*j))+R("11")))
            else:tg=C(0,(),clean(L("001010"+"1"*(4+2*j))+R("11")))
            code,a,b=generate_macro(p,"Case"+str(j),st,tg)
            assert (a,b)==[(28,4),(32,4),(37,8),(41,8),(36,8)][j]
            out.append(code)
    elif idx==2146:
        for j in range(7):
            st=C(0,(),clean(L("10"*3)+R("10")+L("1"*j)+(R("X") if j==6 else ())))
            if j==6:tg=C(0,(),clean(L("10"*8)+R("10")+R("X")))
            elif j<=1:tg=C(0,(),clean(L("10"*5+"1"*(2+2*j))+R("11")))
            else:tg=C(4,(),clean(L("1"*({2:12,3:14,4:15,5:17}[j]))+R("11")))
            code,a,b=generate_macro(p,"Case"+str(j),st,tg)
            assert (a,b)==[(50,4),(54,4),(42,8),(46,8),(71,12),(75,12),(70,12)][j]
            out.append(code)
    else:raise ValueError(idx)
    out.append((Path(__file__).resolve().parent/f"M{idx}Invariant.inc").read_text())
    out.append(f"end M{idx}")
    return "\n\n".join(out)
