"""Generate exact arbitrary-tail binary-carry certificates from pinned specs."""
from itertools import product
from gen_rc_counters import m, emit_epoch, nextword

def opts(pre,digit,k,suf):
    return [m.clean(m.lit(pre+digit*j)+m.rep(digit)+m.lit(digit*(k-j)+suf)) for j in range(k+1)]

def cfg(q,sd,frame,w):
    return m.C(q,w,m.lit(frame)) if sd=="L" else m.C(q,m.lit(frame),w)

def solve(p,src,dst):
    for st,tg in product(src,dst):
        h=m.pump(p,st,tg,2500)
        if h:
            a=sum(x[3] for x in h[0] if x[0]=="step")
            b=sum(x[3] for x in h[0] if x[0]=="loop")
            return st,tg,h,a,b
    raise ValueError((src,dst))

def build(spec):
    i,s,t,osd,oq,ow,ob,cut,q,sd,frame,pre,A,Z,k,suffix,ca,cd,suffix2=spec
    i,t,oq,cut,q,k,ca,cd=map(int,(i,t,oq,cut,q,k,ca,cd))
    pre="" if pre=="_" else pre
    p=m.parse(s)
    def Q(w):return cfg(q,sd,frame,w)
    def F(w):return m.C(oq,w if osd=="R" else (),w if osd=="L" else ())
    def Qopts(dig,k,suf):return [Q(w) for w in opts(pre,dig,k,suf)]
    fo=opts(ow[:cut],ob,0,ow[cut:])
    fo1=opts(ow[:cut],ob,1,ow[cut:])
    X=m.rep("X")
    src,dst=F(fo[0]),F(nextword(fo[0]))
    epochs={};can={}
    epochs["Init"]=solve(p,[src],Qopts(Z,k,suffix))
    can["Init"]=(src,Qopts(Z,k,suffix)[0])
    double=suffix2!="-"
    if double:
        epochs["Reset"]=solve(p,Qopts(A,k,suffix),Qopts(Z,k,suffix2))
        can["Reset"]=(Qopts(A,k,suffix)[0],Qopts(Z,k,suffix2)[0])
    else:suffix2=suffix
    epochs["Finish"]=solve(p,Qopts(A,k,suffix2),[F(w) for w in fo1])
    can["Finish"]=(Qopts(A,k,suffix2)[0],dst)
    epochs["Carry"]=solve(p,[Q(w+X) for w in opts(pre,A,1,Z)],[Q(w+X) for w in opts(pre,Z,1,A)])
    can["Carry"]=(Q(m.clean(m.lit(pre)+m.rep(A)+m.lit(A+Z)+X)),Q(m.clean(m.lit(pre)+m.rep(Z)+m.lit(Z+A)+X)))
    ia,ib=epochs["Init"][-2:];fa,fb=epochs["Finish"][-2:]
    assert epochs["Carry"][-2:]==(ca+cd,cd)
    code=[f"namespace M{i}"]
    for name,res in epochs.items():
        code.append(emit_epoch(name,p,res,can[name],name=="Carry"))
    qs=m.cf(q,m.app(m.bits(pre),"R") if sd=="L" else m.bits(frame),m.app(m.bits(pre),"R") if sd=="R" else m.bits(frame))
    code.append(f"""abbrev table := MInit.table
abbrev A : List Bool := {m.bits(A)}
abbrev Z : List Bool := {m.bits(Z)}
def Q (R : List Bool) : Z0 := {qs}
def family (n : Nat) : Z0 := {m.cfg(src)}
def carryCost (n : Nat) : Nat := {ca}+{cd}*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show {ca}+{cd}*n.succ = {ca+cd}+{cd}*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl
""")
    count=f"fillCost carryCost (n+{k})"
    cost=f"({ia}+{ib}*n) + {count}"
    extra="";h="join0 h1 h2"
    if double:
        ra,rb=epochs["Reset"][-2:]
        cost+=f" + ({ra}+{rb}*n) + {count}"
        extra=f"""  have hr := MReset.canon n
  have h4 := fill table Q A Z carryCost carry (n+{k}) {m.bits(suffix2)}
  rw [rep_add Z n {k},rep_add A n {k}] at h4
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h4
"""
        h="join0 (join0 (join0 h1 h2) hr) h4"
    code.append(f"""def cost (n : Nat) : Nat := {cost} + ({fa}+{fb}*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+{k}) {m.bits(suffix)}
  have h3 := MFinish.canon n
  rw [rep_add Z n {k},rep_add A n {k}] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
{extra}  have h := join0 ({h}) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {t} cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M{i}
""")
    return "\n\n".join(code)

def generate(root,opens,branch,data):
    result={};modules=[]
    header="""import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
"""
    for spec in data:
        i=int(spec[0])
        assert opens[i].replace("_","")==spec[1],(i,opens[i],spec[1])
        mod=f"Raw39B{branch}Counter{i}"
        ns=f"BB6.Agent11{mod}"
        (root/(mod+".lean")).write_text(header+f"namespace {ns}\n"+build(spec)+f"\nend {ns}\n")
        result[i]=(f"{ns}.M{i}.table",f"{ns}.M{i}.never")
        modules.append(mod)
    return result,modules
