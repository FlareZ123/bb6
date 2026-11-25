"""Inductive binary width-growth certificates for Raw39 A1=1LB."""
from pathlib import Path
from gen_rc_counters import m, emit_epoch
from gen_auto_counters import solve

CASES=[
(4769,"1RB1LB1RC---0RD1RE1LD0RA1LF0RE0RA0LF",22,2),
(5156,"1RB1LB1RC---0RD1RE1LD0RA1LF1RD0RA0LF",22,2),
(5157,"1RB1LB1RC---0RD1RE1LD0RA1LF1RD1LC0LF",24,3),
(5455,"1RB1LB1RC---0RD1RF1LD0RA0RA0LE1LE0RF",22,2),
(5793,"1RB1LB1RC---0RD1RF1LD0RA0RA0LE1LE1RD",22,2),
(5794,"1RB1LB1RC---0RD1RF1LD0RA1LC0LE1LE1RD",24,3),
]

def build(i,s,t,k):
    p=m.parse(s)
    def Q(w):return m.C(0,m.lit("0"*k),m.clean(m.lit("0000")+w))
    X=m.rep("X")
    c=(Q(m.rep("10")+m.lit("00")+X),Q(m.rep("00")+m.lit("10")+X))
    o=(Q(m.rep("10")+m.lit("1")),Q(m.rep("00")+m.lit("001")))
    carry=solve(p,[c[0]],[c[1]])
    overflow=solve(p,[o[0]],[o[1]])
    assert carry[-2:]==(t,8),(i,carry[-2:])
    assert overflow[-2:]==(t+8,8),(i,overflow[-2:])
    return "\n".join([f"namespace M{i}",emit_epoch("Carry",p,carry,c,True),emit_epoch("Overflow",p,overflow,o),f"""abbrev table := MCarry.table
abbrev A : List Bool := [true,false]
abbrev Z : List Bool := [false,false]
def Q (R : List Bool) : Z0 := ⟨0,{m.bits("0"*k)},[false,false,false,false] ++ R⟩
def family (n : Nat) : Z0 := Q (rep Z n ++ [true])
def carryCost (n : Nat) : Nat := {t}+8*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  simpa only [table,Q,A,Z,carryCost,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using MCarry.canon n R

theorem overflow (n : Nat) : run0 table ({t+8}+8*n) (Q (rep A n ++ [true])) = some (family (n+1)) := by
  have h := MOverflow.canon n
  rw [show MOverflow.table = table from rfl] at h
  simpa only [table,Q,A,Z,family,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl

def cost (n : Nat) : Nat := fillCost carryCost n + ({t+8}+8*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  join0 (fill table Q A Z carryCost carry n [true]) (overflow n)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {t} cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M{i}
"""])

def generate(root,opens=None):
    root=Path(root)
    name="Raw39LBWidthCounters"
    ns="BB6.Agent11Raw39LBWidthCounters"
    if opens is not None:
        for i,s,_,_ in CASES:assert opens[i].replace("_","")==s
    (root/(name+".lean")).write_text("import Raw39CounterCarry\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace "+ns+"\n"+"\n".join(build(*c) for c in CASES)+"\nend "+ns+"\n")
    return {i:(f"{ns}.M{i}.table",f"{ns}.M{i}.never") for i,_,_,_ in CASES},[name]

if __name__=="__main__":
    generate(Path(__file__).resolve().parent)
