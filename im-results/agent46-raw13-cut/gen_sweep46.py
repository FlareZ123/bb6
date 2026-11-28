"""Generate the exact four-phase nonhalting proof from symbolic sweeps."""
from symbolsweep46 import *
from pathlib import Path

def bits(s): return "["+",".join("true" if x=="1" else "false" for x in s)+"]"
def wexpr(w):
    if not w.block: return bits(w.pre)
    p=[]
    if w.pre: p.append(bits(w.pre))
    p.append(f"rep {bits(w.block)} k")
    if w.suf: p.append(bits(w.suf))
    return "("+" ++ ".join(p)+")"
def zexpr(z): return f"⟨{z[0]},{wexpr(z[1])},{wexpr(z[2])}⟩"
def normeq(a,b): return a==b or (a.block==b.block and a.pull()==b.pull())

def make():
    n=22
    pref="01"*4+"111"+"01"*n
    R=W(pref,"01"*16,"")
    want="01"*4+"111"+"01"*(n+16)
    stop=lambda z,n: n>0 and z[0]==0 and not z[1].value(0).strip("0") and not z[1].block and z[2].value(0)==want and z[2].value(1)==want+"01"*16
    z,ops=symrun(TABLE,W(),R,stop)
    transformed=[]
    for op in ops:
        kind,a,b,*rest=op
        if kind=="raw":
            def expose(w):
                if not w.pre and w.block and w.suf.startswith(w.block):
                    return W(w.block,w.block,w.suf[len(w.block):])
                return w
            q,l,r=a
            l1=expose(l)
            d=tab(TABLE)[2*q+int(l1.pre[0] if l1.pre else "0")][1]
            r1=expose(r) if d else r
            a1=(q,l1,r1)
            if a!=a1:
                assert normeq(l,l1) and normeq(r,r1)
                transformed.append(("eq",a,a1))
            assert primitive(tab(TABLE),a1)==b
            transformed.append(("raw",a1,b))
        else:
            t,d,rp,lp,B,O,inp,out=rest[0]
            a1=(a[0],out,inp) if d else (a[0],inp,out)
            if a1!=a: transformed.append(("eq",a,a1))
            transformed.append(("sweep",a1,b,rest[0]))
    seg=[]
    j=0
    while j<len(transformed):
        op=transformed[j]
        kind,a,b,*rest=op
        if kind=="raw":
            end=j+1
            while end<len(transformed) and transformed[end][0]=="raw" and end-j<200: end+=1
            seg.append(("raw",a,transformed[end-1][2],end-j))
            j=end
        else:
            seg.append(op)
            j+=1
    assert len(seg)==133
    lines=[
        "import SweepPumping","import FastFAR","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
        "namespace BB6.Agent46Raw13RECycle","open BB6Coverage BB6Coverage.Agent31Pump",
        "abbrev p : PartialMachine := FAR.fromCodes [7,14,11,2,2,19,23,0,6,17,24,15]",
        "def Reach (a b : Z0) : Prop := ∃ t, run0 p t a = some b",
        "theorem reach {t : Nat} {a b : Z0} (h : run0 p t a = some b) : Reach a b := ⟨t,h⟩",
        "theorem chain {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by\n  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,join0 ht hu⟩",
        "theorem rep_add2 (B : List Bool) (n m : Nat) : rep B (n+m) = rep B n ++ rep B m := by\n  induction n with\n  | zero => simp [rep]\n  | succ n ih => rw [Nat.succ_add,rep,ih]; simp [rep,List.append_assoc]",
        "theorem commute (B : List Bool) (n k : Nat) : rep B n ++ rep B k = rep B k ++ rep B n := by\n  rw [← rep_add2, ← rep_add2, Nat.add_comm n k]"
    ]
    emit=lines.append
    def eqProof(a,b):
        assert normeq(a,b)
        if a==b: return "rfl"
        c=a.pull()
        B=a.block
        x=(len(a.pre)-len(c.pre))//len(B)
        y=(len(b.pre)-len(c.pre))//len(B)
        d=abs(x-y)
        assert d>0
        smaller,larger=(a,b) if x<y else (b,a)
        assert smaller.suf.startswith(B*d) and larger.pre==smaller.pre+B*d and larger.suf==smaller.suf[len(B)*d:]
        funbody=(bits(smaller.pre)+" ++ " if smaller.pre else "")+"w"+(" ++ "+bits(larger.suf) if larger.suf else "")
        base=f"congrArg (fun w : List Bool => {funbody}) (commute {bits(B)} {d} k)"
        return f'by simpa only [List.append_assoc,List.nil_append,List.append_nil,List.cons_append,rep] using {"("+base+").symm" if x<y else base}'
    for i,op in enumerate(seg):
        kind,a,b,*rest=op
        emit(f"def z{i} (k : Nat) : Z0 := {zexpr(a)}")
        if kind=="raw":
            emit(f"theorem seg{i} (k : Nat) : run0 p {rest[0]} (z{i} k) = some ({zexpr(b)} : Z0) := by rfl")
        elif kind=="eq":
            emit(f"theorem seg{i} (k : Nat) : run0 p 0 (z{i} k) = some ({zexpr(b)} : Z0) := by\n  have hL : {wexpr(a[1])} = {wexpr(b[1])} := {eqProof(a[1],b[1])}\n  have hR : {wexpr(a[2])} = {wexpr(b[2])} := {eqProof(a[2],b[2])}\n  simp only [run0,z{i},hL,hR]")
        else:
            t,d,rp,lp,B,O,inp,out=rest[0]
            if d:
                lemma=f"sweepR p {a[0]} {bits(lp)} {bits(rp)} {bits(B)} {bits(O)} {t}"
                args=f"k {bits(out.pre[len(lp):])} {bits(inp.suf)}"
            else:
                lemma=f"sweepL p {a[0]} {bits(rp)} {bits(lp)} {bits(B)} {bits(O)} {t}"
                args=f"k {bits(inp.suf)} {bits(out.pre[len(lp):])}"
            emit(f"theorem seg{i} (k : Nat) : run0 p ({t}*k) (z{i} k) = some ({zexpr(b)} : Z0) := by\n  simpa only [z{i},List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using {lemma} (by intro L R; rfl) {args}")
    emit(f"def z{len(seg)} (k : Nat) : Z0 := {zexpr(z)}")
    emit(f"theorem allSegments (k : Nat) : ∃ t, 0<t ∧ run0 p t (z0 k) = some (z{len(seg)} k) := by")
    for i in range(1,len(seg)):
        emit(f"  have H{i} : Reach (z{i} k) (z{i+1} k) := reach (seg{i} k)")
    expr="(H1)"
    for i in range(2,len(seg)): expr=f"(chain {expr} H{i})"
    emit(f"  obtain ⟨t,ht⟩ := {expr}")
    emit(f"  exact ⟨{seg[0][3]}+t,by omega,join0 (seg0 k) ht⟩")
    emit(f"theorem endpoint (k : Nat) : z{len(seg)} k = z0 (k+1) := by")
    emit(f"  have h := congrArg (fun w : List Bool => {bits(z[2].pre)} ++ w) (rotate true {bits(z[2].block[1:])} k).symm")
    emit(f"  have hr : ({wexpr(z[2])}) = ({bits(pref)} ++ rep {bits(R.block)} (k+1)) := by simpa only [rep,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,List.append_nil] using h")
    emit(f"  simp only [z{len(seg)},z0,hr]")
    emit("theorem seed : run0 p 2274 (⟨0,[],[]⟩ : Z0) = some (z0 0) := by rfl")
    emit("theorem growth (k : Nat) : ∃ t, 0<t ∧ run0 p t (z0 k) = some (z0 (k+1)) := by\n  obtain ⟨t,ht,h⟩ := allSegments k; exact ⟨t,ht,by rw [←endpoint]; exact h⟩")
    emit("theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by\n  let cost := fun k => Classical.choose (growth k)\n  exact never_of_growth p z0 2274 cost seed (fun k => (Classical.choose_spec (growth k)).1) (fun k => (Classical.choose_spec (growth k)).2) m hm\n#print axioms never")
    emit("end BB6.Agent46Raw13RECycle")
    Path(__file__).with_name("Raw13RECycle.lean").write_text("\n".join(lines)+"\n")
    print("generated",len(seg),"segments,",sum(x[3][0] for x in seg if x[0]=="sweep"),"* k +",sum(x[3] for x in seg if x[0]=="raw"),"steps")

if __name__=="__main__": make()
