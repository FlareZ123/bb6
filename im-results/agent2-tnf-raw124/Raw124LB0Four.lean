import Raw58Live
namespace BB6Coverage.Agent4Raw124LB0Four
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- B1 selects A or C; C1 selects E or B. These are leaves 935,936,1046,1047. -/
def table (u v : Bool) : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,if u then 2 else 0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => if v then some (some ⟨true,true,1⟩) else some (some ⟨false,true,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,false,0⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => none
  | (5,true) => some (some ⟨false,false,1⟩)
  | _ => none

def I : List Bool := [false,true,false,true]
def O : List Bool := [true,true,true,true]
def Cframe : List Bool := [true,true,true,true,true]
def tail (u : Bool) : List Bool := if u then [false] else []
def enter (u : Bool) : Nat := if u then 21 else 15
def startCost (v : Bool) : Nat := if v then 4 else 6
def scanCost (v : Bool) : Nat := if v then 4 else 8
def turnCost (u v : Bool) : Nat := (if u then 23 else 17) - (if v then 2 else 0)
def backCost (u : Bool) : Nat := if u then 16 else 10

def family (u : Bool) (n : Nat) : Z0 := ⟨0,[],rep I (n+1) ++ tail u⟩
def cost (u v : Bool) (n : Nat) : Nat := startCost v + scanCost v * n + turnCost u v + backCost u * (n+1)

theorem entry (u v : Bool) : run0 (table u v) (enter u) ⟨0,[],[]⟩ = some (family u 0) := by
  cases u <;> cases v <;> rfl

theorem start (u v : Bool) (R : List Bool) :
    run0 (table u v) (startCost v) ⟨0,[],I++R⟩ = some ⟨2,Cframe,R⟩ := by
  cases u <;> cases v <;> rfl

theorem scanOne (u v : Bool) (L R : List Bool) :
    run0 (table u v) (scanCost v) ⟨2,Cframe++L,I++R⟩ = some ⟨2,Cframe++O++L,R⟩ := by
  cases u <;> cases v <;> rfl

theorem turn (u v : Bool) (L : List Bool) :
    run0 (table u v) (turnCost u v) ⟨2,Cframe++L,tail u⟩ = some ⟨0,O++L,I++tail u⟩ := by
  cases u <;> cases v <;> rfl

theorem backOne (u v : Bool) (L R : List Bool) :
    run0 (table u v) (backCost u) ⟨0,O++L,I++R⟩ = some ⟨0,L,I++I++R⟩ := by
  cases u <;> cases v <;> rfl

theorem growth (u v : Bool) (n : Nat) :
    run0 (table u v) (cost u v n) (family u n) = some (family u (n+1)) := by
  have h0 := start u v (rep I n++tail u)
  have h1 := sweepR (table u v) 2 Cframe [] I O (scanCost v) (by simpa using scanOne u v) n [] (tail u)
  have h2 := turn u v (rep O n)
  have h3 := sweepL (table u v) 0 [] I O I (backCost u) (by simpa using backOne u v) (n+1) [] (tail u)
  simp only [List.nil_append,List.append_nil] at h1 h3
  have h01 := join0 h0 h1
  have h012 := join0 h01 h2
  have h012' : run0 (table u v) (startCost v + scanCost v*n + turnCost u v) (family u n) = some ⟨0,rep O (n+1),I++tail u⟩ := by
    simpa only [family,rep,List.append_assoc] using h012
  have h := join0 h012' h3
  simpa only [cost,family,rep,List.append_assoc] using h

theorem never (u v : Bool) (m : Machine) (hm : compatible (table u v) m) : NeverHalts m := by
  apply never_of_growth (table u v) (family u) (enter u) (cost u v) (entry u v) _ (growth u v) m hm
  intro n; cases u <;> cases v <;> simp [cost,startCost,scanCost,turnCost,backCost] <;> omega

namespace M935
def table := Agent4Raw124LB0Four.table false false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent4Raw124LB0Four.never false false m hm
end M935
namespace M936
def table := Agent4Raw124LB0Four.table false true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent4Raw124LB0Four.never false true m hm
end M936
namespace M1046
def table := Agent4Raw124LB0Four.table true false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent4Raw124LB0Four.never true false m hm
end M1046
namespace M1047
def table := Agent4Raw124LB0Four.table true true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent4Raw124LB0Four.never true true m hm
end M1047
#print axioms M935.never
#print axioms M936.never
#print axioms M1046.never
#print axioms M1047.never
end BB6Coverage.Agent4Raw124LB0Four
