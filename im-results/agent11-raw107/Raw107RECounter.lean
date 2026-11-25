import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107RECounter
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev Z := [false,false]
abbrev O := [true,false]
abbrev P := [true,true]
abbrev base := [true,false,true,true,false]
abbrev tail := [false,true,true,false]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def family (n : Nat) : Z0 := A [] (rep P n++base)

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem carryOne (L R : List Bool) : run0 table 2 (A (O++L) R) = some (A L (P++R)) := by rfl

theorem carry (n : Nat) (L : List Bool) :
    run0 table (2*n) (A (rep O n++L) base) = some (A L (rep P n++base)) := by
  simpa only [List.nil_append] using sweepL table 0 [] [] O P 2 carryOne n L base

theorem pairRotate (n : Nat) : rep P n ++ base = true::(rep P n++tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun l => true::true::l) ih

theorem enter (n : Nat) (L : List Bool) :
    run0 table 1 (A (false::L) (rep P n++base)) = some (B (true::true::L) (rep P n++tail)) := by
  rw [pairRotate]; rfl

theorem enterBlank (n : Nat) :
    run0 table 1 (family n) = some (B [true,true] (rep P n++tail)) := by
  unfold family; rw [pairRotate]; rfl

theorem pair (L R : List Bool) :
    run0 table 2 (B ([true]++L) (P++R)) = some (B ([true]++Z++L) R) := by rfl

theorem sweep (n : Nat) (L : List Bool) :
    run0 table (2*n) (B (true::true::L) (rep P n++tail)) = some (B (true::(rep Z n++true::L)) tail) := by
  simpa only [List.cons_append,List.nil_append,List.append_nil,List.append_assoc] using sweepR table 1 [true] [] P Z 2 pair n (true::L) tail

theorem finish (L : List Bool) : run0 table 3 (B (true::L) tail) = some (A L base) := by rfl

theorem setWithCarry (n : Nat) (L : List Bool) :
    run0 table (2*n+4) (A (false::L) (rep P n++base)) = some (A (rep Z n++true::L) base) := by
  have h := join0 (join0 (enter n L) (sweep n L)) (finish (rep Z n++true::L))
  simpa only [show 1+2*n+3=2*n+4 by omega] using h

def fillCost : Nat → Nat
  | 0 => 0
  | n+1 => fillCost n + 2*n + (2*n+4) + fillCost n

theorem fill (n : Nat) (L : List Bool) :
    run0 table (fillCost n) (A (rep Z n++L) base) = some (A (rep O n++L) base) := by
  induction n generalizing L with
  | zero => simp [rep,fillCost,run0]
  | succ n ih =>
    have h1 := ih (Z++L)
    have h2 := carry n (Z++L)
    have h3 := setWithCarry n (false::L)
    have h4 := ih (O++L)
    have h3' : run0 table (2*n+4) (A (Z++L) (rep P n++base)) = some (A (rep Z n++(O++L)) base) := h3
    have h := join0 (join0 (join0 h1 h2) h3') h4
    rw [← List.append_assoc,rep_snoc Z n,← List.append_assoc,rep_snoc O n] at h
    simpa only [fillCost,rep] using h

theorem start (n : Nat) : run0 table (2*n+4) (family n) = some (A (rep Z n++[true]) base) := by
  have h := join0 (join0 (enterBlank n) (sweep n [])) (finish (rep Z n++[true]))
  simpa only [show 1+2*n+3=2*n+4 by omega] using h

theorem overflow (n : Nat) : run0 table 2 (A [true] (rep P n++base)) = some (family (n+1)) := by rfl

def cost (n : Nat) := 2*n+4+fillCost n+2*n+2

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  exact join0 (join0 (join0 (start n) (fill n [true])) (carry n [true])) (overflow n)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms entry
#print axioms growth
#print axioms never
end BB6.Agent11Raw107RECounter
