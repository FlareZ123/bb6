"""Untrusted finite macro synthesis for the five raw114 paired-word counters.
The generated Lean proof covers every finite word of paired bits, not merely
the observed run. No opaque list tail can be read during witness discovery.
"""
from pathlib import Path
import re, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
import generate_sweeps as pump
TABLES=[
 "1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LD_1RA1LC",
 "1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LD_1RA1RA",
 "1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LD_1RA1RD",
 "1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LD_1RA1RE",
 "1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LD_1RC1RA",
]

def find(p,fr,bits,opaque=True,limit=100):
    left="01" if fr=="a" else "10111"
    right=("0" if fr=="a" else "")+"".join(x*2 for x in bits)
    c=pump.C({"a":0,"d":3,"f":5}[fr],0,0,pump.W(left,"L",""),pump.W(right,"R" if opaque else "",""))
    for t in range(1,limit+1):
        try:c=pump.step(p,c)
        except ValueError:return None
        if c.q==0 and (not c.l.pre or c.l.pre.startswith("0")) and c.r.pre.startswith("000") and len(c.r.pre)%2==1 and all(c.r.pre[j]==c.r.pre[j+1] for j in range(3,len(c.r.pre)-1,2)):
            return ("left",t,c)
        if c.q==0 and c.l.pre.startswith("01") and c.r.pre=="0" and c.h0>0:
            return ("a",t,c)
        if c.q in ([3,5] if p[11]=="1RE" else [3]) and c.l.pre.startswith("10111") and not c.r.pre and c.h0>0:
            return ("d" if c.q==3 else "f",t,c)
    return None

def tree(p,fr,bits="",maxdepth=5):
    r=find(p,fr,bits)
    if r:return ("rule",bits,True,r)
    r=find(p,fr,bits,False)
    assert r is not None and len(bits)<maxdepth,(p,fr,bits)
    return ("split",("rule",bits,False,r),tree(p,fr,bits+"0"),tree(p,fr,bits+"1"))

def bools(s):return "["+",".join("true" if c=="1" else "false" for c in s)+"]"
def list_expr(s,tail):return " ++ ".join(x for x in (bools(s) if s else "",tail) if x) or "[]"
def add(m,k):return f"(m+{k})" if m and k else "m" if m else str(k)

def newleft(s,source):
    groups=re.findall(r"0(1+)",s)
    assert "".join("0"+g for g in groups)==s and all(len(g)%2==1 for g in groups),s
    assert not source or groups,s
    expr="L";proof="h"
    for j in range(len(groups)-1,-1,-1):
        n=add(source and j==len(groups)-1,(len(groups[j])-1)//2)
        expr=f"(block {n} {expr})"
        proof=f"(Good.more {n} {proof})"
    return expr,proof

TEMPLATE='''import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw114Pair{idx}
open BB6Coverage
{table}

def pairs : List Bool → List Bool
  | [] => []
  | b::xs => b::b::pairs xs

def block (n : Nat) (L : List Bool) : List Bool := false::true::rep [true,true] n ++ L
inductive Good : List Bool → Prop
  | base : Good {base}
  | more (n : Nat) {{L : List Bool}} : Good L → Good (block n L)

def baseConf (xs : List Bool) : Z0 := ⟨0,[],{zeros} ++ pairs xs⟩
def leftConf (L : List Bool) (xs : List Bool) : Z0 := ⟨0,L,[false,false,false] ++ pairs xs⟩
inductive Frame where
  | a
  | d (n : Nat)
  | f (n : Nat)
def frameConf (f : Frame) (L : List Bool) (xs : List Bool) : Z0 :=
  match f with
  | .a => ⟨0,[false,true] ++ L,false::pairs xs⟩
  | .d n => ⟨3,[true,false,true,true,true] ++ rep [true,true] n ++ L,pairs xs⟩
  | .f n => ⟨5,[true,false,true,true,true] ++ rep [true,true] n ++ L,pairs xs⟩

def Returns (z : Z0) : Prop := ∃ k ys, 0 < k ∧ run0 table k z = some (baseConf ys)

theorem prepend {{z z' : Z0}} {{k : Nat}} (hr : run0 table k z = some z') (h : Returns z') : Returns z := by
  obtain ⟨t,ys,ht,h'⟩ := h
  exact ⟨k+t,ys,by omega,join0 hr h'⟩

theorem leftGadget (L R : List Bool) : run0 table 9 ⟨0,false::L,[false,false,false]++R⟩ = some ⟨0,true::true::L,[true,true]++R⟩ := by rfl
theorem left3 (L R : List Bool) : run0 table 3 ⟨0,[true,true,true]++L,[true,true]++R⟩ = some ⟨0,L,[false,false,false,true,true]++R⟩ := by rfl
theorem erasePair (L R : List Bool) : run0 table 2 ⟨0,[true,true]++L,R⟩ = some ⟨0,L,[false,false]++R⟩ := by rfl

theorem zeros_shift (n : Nat) (xs : List Bool) :
    rep [false,false] n ++ [false,false,false,true,true] ++ pairs xs =
      [false,false,false] ++ pairs (List.replicate n false ++ true::xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [rep,List.replicate_succ,List.cons_append,List.nil_append,pairs,List.append_assoc] using congrArg (fun l => false::false::l) ih

theorem leftMore (n : Nat) (L : List Bool) (xs : List Bool) :
    run0 table (12+2*n) (leftConf (block n L) xs) = some (leftConf L (List.replicate n false ++ true::xs)) := by
  have h1 := leftGadget (true::rep [true,true] n ++ L) (pairs xs)
  have h2 := left3 (rep [true,true] n ++ L) (pairs xs)
  have h3 := sweepL table 0 [] [] [true,true] [false,false] 2 erasePair n L ([false,false,false,true,true] ++ pairs xs)
  have H := join0 (join0 h1 h2) (by simpa only [List.nil_append,List.append_assoc] using h3)
  rw [show 9+3+2*n=12+2*n by omega] at H
  have H2 : run0 table (12+2*n) (leftConf (block n L) xs) = some ⟨0,L,rep [false,false] n ++ [false,false,false,true,true] ++ pairs xs⟩ := by
    simpa only [leftConf,block,List.nil_append,List.cons_append,List.append_assoc] using H
  rw [zeros_shift] at H2
  exact H2

theorem leftBase (xs : List Bool) : run0 table {basecost} (leftConf {base} xs) = some (baseConf (true::xs)) := by rfl

theorem leftReturn (L : List Bool) (h : Good L) (xs : List Bool) : Returns (leftConf L xs) := by
  induction h generalizing xs with
  | base => exact ⟨{basecost},true::xs,by omega,leftBase xs⟩
  | more n h ih => exact prepend (leftMore n _ xs) (ih _)

'''

def emit(idx,p):
    base="0"+"1"*(6 if idx==4 else 4)
    zeros="0"*(8 if idx==4 else 6)
    code=TEMPLATE.format(idx=idx,table=pump.tab(p),base=bools(base),zeros=bools(zeros),basecost=9+len(zeros))
    frs=["a","d"]+(["f"] if idx==3 else [])
    counter=0;rules=[]
    def emit_node(fr,tr,depth,lines):
        nonlocal counter
        indent="  "*depth
        if tr[0]=="split":
            _,nil,zero,one=tr
            lines.append(indent+"cases xs with")
            lines.append(indent+"| nil =>")
            emit_node(fr,nil,depth+1,lines)
            lines.append(indent+"| cons b xs =>")
            lines.append(indent+"  cases b with")
            lines.append(indent+"  | false =>")
            emit_node(fr,zero,depth+2,lines)
            lines.append(indent+"  | true =>")
            emit_node(fr,one,depth+2,lines)
            return
        _,prefix,opaque,(target,t,c)=tr
        name=f"rule{counter}";counter+=1
        sm=fr!="a";srcf=f"(.{fr} m)" if sm else ".a"
        source=f"frameConf {srcf} L ({list_expr(prefix,'xs' if opaque else '')})"
        r=c.r.pre;newl=c.l.pre
        tail="xs" if opaque else "[]"
        if target=="left":
            left,proof=newleft(newl,sm) if newl else ("L","h")
            assert not sm or newl
            right=list_expr(r[3::2],tail)
            dst=f"leftConf {left} ({right})"
            go=f"leftReturn {left} {proof} ({right})"
        elif target=="a":
            assert opaque
            left,proof=newleft(newl[2:],sm)
            dst=f"frameConf .a {left} xs";go=f"scan xs .a {left} {proof}"
        else:
            assert opaque
            rem=newl[5:]
            extra=len(rem)-len(rem.lstrip("1"))
            assert extra%2==0
            rest=rem[extra:]
            left,proof=newleft(rest,sm) if rest else ("L","h")
            n=add(sm and not rest,extra//2)
            dst=f"frameConf (.{target} {n}) {left} xs"
            go=f"scan xs (.{target} {n}) {left} {proof}"
        args=("(m : Nat) " if sm else "")+"(L : List Bool)"+(" (xs : List Bool)" if opaque else "")
        rules.append(f"theorem {name} {args} : run0 table {t} ({source}) = some ({dst}) := by rfl")
        rule=f"{name} "+("m " if sm else "")+"L"+(" xs" if opaque else "")
        lines.append(indent+f"exact prepend ({rule}) ({go})")
    lines=["theorem scan (xs : List Bool) (f : Frame) (L : List Bool) (h : Good L) : Returns (frameConf f L xs) := by","  cases f with"]
    for fr in frs:
        lines.append("  | "+fr+(" m" if fr!="a" else "")+" =>")
        emit_node(fr,tree(p,fr),2,lines)
    if "f" not in frs:
        code=code.replace("  | f (n : Nat)\n","").replace("  | .f n => ⟨5,[true,false,true,true,true] ++ rep [true,true] n ++ L,pairs xs⟩\n","")
    lines+=["termination_by xs.length","decreasing_by all_goals (simp_wf; try omega)"]
    code+="\n\n".join(rules)+"\n\n"+"\n".join(lines)+"\n\n"
    entry=35 if idx==4 else 23
    start=64 if idx==4 else 50
    code+=f'''theorem enterFrame (xs : List Bool) : run0 table {entry} (baseConf xs) = some (frameConf .a {bools(base)} xs) := by rfl

theorem returnBase (xs : List Bool) : Returns (baseConf xs) := prepend (enterFrame xs) (scan xs .a _ Good.base)

-- Iteration through the proven, positive-cost return relation.
noncomputable def next (xs : List Bool) : List Bool := Classical.choose (Classical.choose_spec (returnBase xs))
noncomputable def cost (xs : List Bool) : Nat := Classical.choose (returnBase xs)
theorem cost_pos (xs : List Bool) : 0 < cost xs := (Classical.choose_spec (Classical.choose_spec (returnBase xs))).1
theorem ret (xs : List Bool) : run0 table (cost xs) (baseConf xs) = some (baseConf (next xs)) := (Classical.choose_spec (Classical.choose_spec (returnBase xs))).2
noncomputable def words : Nat → List Bool
  | 0 => [true,true]
  | n+1 => next (words n)

theorem entry : run0 table {start} ⟨0,[],[]⟩ = some (baseConf (words 0)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => baseConf (words n)) {start} (fun n => cost (words n)) entry
    (fun n => cost_pos (words n)) (fun n => ret (words n)) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw114Pair{idx}
'''
    return code

if __name__=="__main__":
    for idx,s in enumerate(TABLES):
        (ROOT/f"Raw114Pair{idx}.lean").write_text(emit(idx,pump.parse(s)),encoding="utf-8")
