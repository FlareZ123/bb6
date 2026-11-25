"""Reproduce eight arbitrary-tail counter certificates and their E/F swaps."""
from itertools import product
import re
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import multi as m

# id, table, outer state, fresh side, base word, inserted block, entry,
# inner state, variable side, fixed frame, fixed prefix, one and zero digits.
CASES=[
(38,'1RB0RC1RC---0RD0LE1LD0RA1LE0LF0LA0RF',3,'R','0000011','000',18,1,'R','01','','011','111'),
(39,'1RB0RC1RC---0RD0LE1LD0RA1LE0LF0LA1RB',3,'R','0000011','000',18,1,'R','01','','011','111'),
(107,'1RB0RC1RC1LE0RD0LF1LD0RA1LA0LB0LE---',4,'L','1010000','101',38,2,'L','10000','','010','000'),
(383,'1RB0RC1RC---0RD0RE1LD0RA1LF1RC0LF1RB',4,'R','00001','000',8,1,'R','01','','001','000'),
(508,'1RB0RC1RC0LE0RD0RF1LD0RA1LB---0RC1LE',1,'L','1011111','10',27,1,'L','11111','','10','00'),
(809,'1RB0RC1RC1LE0RD1LB1LD0RA1LF---0LB0LF',5,'L','110111111','110',38,1,'L','1111','','100','000'),
(1089,'1RB0RC1RC1LE0RD1LE1LD0RA1LF0LE0LB---',4,'L','101101101011111','101',116,1,'L','01011111','','100','000'),
(1108,'1RB0RC1RC---0RD1LE1LD0RA1LF0RE0LF1RB',4,'R','00001','0',16,1,'R','01','00','1','0'),
]
PAIRS={38:176,39:177,107:1,383:589,508:270,809:850,1089:1399,1108:1412}

def swap(s):
    s=s.replace("_","").translate(str.maketrans("EF","FE"))
    return s[:24]+s[30:36]+s[24:30]

def nextword(w):
    return m.clean(tuple(x for word,b in w for x in (((word,False),(word,True)) if b else ((word,False),))))

def options(base,rep):
    pos=base.find(rep)
    return [m.clean(m.lit(base[:i])+m.rep(rep)+m.lit(base[i:]))
            for i in range(len(base)+1)
            if base[:i]+rep+base[i:]==base[:pos]+rep+base[pos:]]

def side(q,sd,w,f=()):
    return m.C(q,w,f) if sd=="L" else m.C(q,f,w)

def Q(c,w):
    return side(c[7],c[8],m.clean(m.lit(c[10])+w),m.lit(c[9]))

def F(c,w):
    return side(c[2],"L" if c[3]=="R" else "R",w)

def solve(c,src,dst):
    p=m.parse(c[1])
    for st,tg in product(src,dst):
        h=m.pump(p,st,tg,500)
        if h:
            a=sum(x[3] for x in h[0] if x[0]=="step")
            b=sum(x[3] for x in h[0] if x[0]=="loop")
            return st,tg,h,a,b

def emit_epoch(name,p,res,canon,tail=False):
    st,tg,h,a,b=res
    oldword=m.word
    try:
        if tail:
            m.word=lambda w,n="n":m.app(*["R" if s=="X" else f"rep {m.bits(s)} ({n})" if v else m.bits(s) for s,v in w])
        code,info=m.generate(name,p,(0,st,tg,h),epoch=True)
        assert info==(0,a,b)
        code=code.rsplit("\nend M"+name,1)[0]
        if tail:
            code=code.replace("(n : Nat) :","(n : Nat) (R : List Bool) :")
            code=re.sub(r"(phase\d+|final[LR]) n\b",r"\1 n R",code)
        rules=[]
        for ix,(x,y) in enumerate(zip((st,tg),canon)):
            for sd in ["l","r"]:
                a0,b0=getattr(x,sd),getattr(y,sd)
                if a0!=b0:
                    nm=f"eq{ix}{sd}"
                    eq=m.wordeq(nm,a0,b0)
                    if tail:eq=eq.replace("(n : Nat) :","(n : Nat) (R : List Bool) :")
                    code+="\n"+eq+"\n"
                    rules.append(nm+" n"+(" R" if tail else ""))
        arg=" (R : List Bool)" if tail else ""
        ext=" R" if tail else ""
        code+=f"\ntheorem canon (n : Nat){arg} : run0 table ({a}+{b}*n) {m.cfg(canon[0])} = some {m.cfg(canon[1])} := by\n"
        if rules:code+=f'  simpa only [{", ".join(rules)}] using epoch n{ext}\n'
        else:code+=f"  exact epoch n{ext}\n"
        return code+"\nend M"+name+"\n"
    finally:
        m.word=oldword

def build(c,outid):
    i,s,q,sd,a,b,t,cq,csd,frame,pre,A,Z=c
    p=m.parse(s);X=m.rep("X");specs={}
    k,suffix={107:(1,"01"),383:(0,"001"),508:(1,"1"),809:(2,"1"),1089:(3,"1"),1108:(0,"1"),38:(2,"1"),39:(2,"1")}[i]
    base2=a[:a.find(b)]+b+a[a.find(b):]
    st=[F(c,w) for w in options(a,b)];tg=[F(c,w) for w in options(base2,b)]
    special=i in [38,39]
    if special:
        initopts=[Q(c,m.lit(A*2)+m.rep(Z)+m.lit("1"))]
        finopts=[Q(c,w) for w in options(A*2+"0",A)]
    else:
        initopts=[Q(c,w) for w in options(Z*k+suffix,Z)] if k else [Q(c,m.rep(Z)+m.lit(suffix))]
        finopts=[Q(c,w) for w in options(A*k+suffix,A)] if A in A*k+suffix else [Q(c,m.rep(A)+m.lit(suffix))]
        if i==1108:finopts=[Q(c,m.rep(A)+m.lit(suffix))]
    specs["Init"]=solve(c,st,initopts)
    specs["Finish"]=solve(c,finopts,tg)
    if special:
        specs["Reset"]=solve(c,[Q(c,w) for w in options(A*2+"1",A)],[Q(c,w) for w in options(Z*2+"0",Z)])
    specs["Carry"]=solve(c,[Q(c,m.rep(A)+m.lit(A+Z)+X),Q(c,m.lit(A)+m.rep(A)+m.lit(Z)+X)],[Q(c,m.rep(Z)+m.lit(Z+A)+X),Q(c,m.lit(Z)+m.rep(Z)+m.lit(A)+X)])
    assert all(specs.values()),(outid,[name for name,v in specs.items() if not v])
    canon={}
    canon["Init"]=(specs["Init"][0],Q(c,m.lit(A*2)+m.rep(Z)+m.lit("1")) if special else Q(c,m.rep(Z)+m.lit(Z*k+suffix)))
    old=specs["Init"][0]
    new=F(c,nextword(old.l if sd=="R" else old.r))
    canon["Finish"]=(Q(c,m.rep(A)+m.lit(A*k+("0" if special else suffix))),new)
    canon["Carry"]=(Q(c,m.rep(A)+m.lit(A+Z)+X),Q(c,m.rep(Z)+m.lit(Z+A)+X))
    if special:canon["Reset"]=(Q(c,m.rep(A)+m.lit(A*2+"1")),Q(c,m.rep(Z)+m.lit(Z*2+"0")))
    code=["namespace M"+str(outid)]
    for name,res in specs.items():code.append(emit_epoch(name,p,res,canon[name],name=="Carry"))
    c0=specs["Carry"][-2]-specs["Carry"][-1];cd=specs["Carry"][-1]
    ia,ib=specs["Init"][-2:];fa,fb=specs["Finish"][-2:]
    Qstr=m.cf(cq,m.app(m.bits(pre),"R") if csd=="L" else m.bits(frame),m.app(m.bits(pre),"R") if csd=="R" else m.bits(frame))
    fs=m.cfg(specs["Init"][0])
    code.append(f"""abbrev table := MInit.table
abbrev A : List Bool := {m.bits(A)}
abbrev Z : List Bool := {m.bits(Z)}
def Q (R : List Bool) : Z0 := {Qstr}
def family (n : Nat) : Z0 := {fs}
def carryCost (n : Nat) : Nat := {c0}+{cd}*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show {c0}+{cd}*n.succ = {c0+cd}+{cd}*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl
""")
    if special:
        ra,rb=specs["Reset"][-2:]
        code.append(f"""def cost (n : Nat) : Nat := ({ia}+{ib}*n) + partialCost carryCost 2 n + ({ra}+{rb}*n) + fillCost carryCost (n+2) + ({fa}+{fb}*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fillFrom table Q A Z carryCost carry 2 n [true]
  have h3 := MReset.canon n
  have h4 := fill table Q A Z carryCost carry (n+2) [false]
  have h5 := MFinish.canon n
  rw [Nat.add_comm 2 n,rep_add A n 2] at h2
  rw [rep_add Z n 2,rep_add A n 2] at h4
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2 h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h
""")
    else:
        code.append(f"""def cost (n : Nat) : Nat := ({ia}+{ib}*n) + fillCost carryCost (n+{k}) + ({fa}+{fb}*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+{k}) {m.bits(suffix)}
  have h3 := MFinish.canon n
  rw [rep_add Z n {k},rep_add A n {k}] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h
""")
    code.append(f"""theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {t} cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M{outid}
""")
    return "\n\n".join(code)

def generate(roots,opens):
    result={};modules=[]
    header="""import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
"""
    for c in CASES:
        i=c[0];j=PAIRS[i]
        cc=list(c);cc[1]=swap(cc[1])
        cc[2]=9-cc[2] if cc[2]>=4 else cc[2]
        cc[7]=9-cc[7] if cc[7]>=4 else cc[7]
        for idx,table in [(i,c[1]),(j,cc[1])]:
            assert opens[idx].replace("_","")==table,(idx,opens[idx],table)
        mod=f"Raw39RCCounter{i}"
        ns=f"BB6.Agent11Raw39RCCounter{i}"
        (roots/(mod+".lean")).write_text(header+f"namespace {ns}\n"+build(c,i)+build(tuple(cc),j)+f"\nend {ns}\n")
        for idx in [i,j]:result[idx]=(f"{ns}.M{idx}.table",f"{ns}.M{idx}.never")
        modules.append(mod)
    return result,modules
