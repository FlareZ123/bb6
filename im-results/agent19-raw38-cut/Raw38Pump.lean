import SweepPumping

namespace BB6Coverage.Agent19Raw38Pump
open BB6Coverage BB6Coverage.Agent31Pump

/-- Raw38, A1=0RC, C1=0RC; five entries remain unspecified. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | _,_ => none

abbrev zeros (n : Nat) := rep [false] n
abbrev ones (n : Nat) := rep [true] n

def family (n : Nat) : Z0 := ⟨0,true :: zeros n,false :: ones (n+2)⟩

theorem enterPhase (n : Nat) : run0 table 5 (family n) =
    some ⟨2,[true,true,true] ++ zeros (n+1), ones n⟩ := by
  rfl

theorem unary_snoc (b : Bool) (n : Nat) (L : List Bool) :
    rep [b] n ++ b :: L = rep [b] (n+1) ++ L := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [rep,List.singleton_append,List.cons_append,List.nil_append] using congrArg (List.cons b) ih

theorem clear (n : Nat) (L : List Bool) :
    run0 table n ⟨2,true :: L,ones n⟩ = some ⟨2,true :: (zeros n ++ L),[]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    change run0 table n ⟨2,true :: false :: L,ones n⟩ = _
    rw [ih]
    rw [unary_snoc false n L]

theorem turn (L : List Bool) :
    run0 table 2 ⟨2,true :: L,[]⟩ = some ⟨3,false :: false :: false :: L,[]⟩ := by rfl

theorem fill (n : Nat) (L R : List Bool) :
    run0 table n ⟨3,zeros n ++ L,R⟩ = some ⟨3,L,ones n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    change run0 table n ⟨3,zeros n ++ L,true :: R⟩ = _
    rw [ih]
    rw [unary_snoc true n R]

theorem growth (n : Nat) : run0 table (5+n+2+(n+3)+1) (family n) = some (family (n+1)) := by
  have h1 := enterPhase n
  have h2 := clear n ([true,true] ++ zeros (n+1))
  have h3 := turn (zeros n ++ ([true,true] ++ zeros (n+1)))
  have h4 := fill (n+3) ([true,true] ++ zeros (n+1)) []
  have h5 : run0 table 1 ⟨3,[true,true] ++ zeros (n+1),ones (n+3)⟩ = some (family (n+1)) := by rfl
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) (by simpa only [List.append_nil] using h5)
  exact H

theorem entry : run0 table 6 ⟨0,[],[]⟩ = some (family 0) := by rfl

/-- Every renewal has its exact primitive-step count. -/
theorem renewalTime (n : Nat) :
    run0 table (n*n+10*n+6) ⟨0,[],[]⟩ = some (family n) := by
  induction n with
  | zero => exact entry
  | succ n ih =>
    have h := join0 ih (growth n)
    rw [show (n+1)*(n+1)+10*(n+1)+6 = (n*n+10*n+6)+(5+n+2+(n+3)+1) by
      simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]; omega]
    exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 6 (fun n => 5+n+2+(n+3)+1) entry
    (by intro n; omega) growth m hm

#print axioms growth
#print axioms renewalTime
#print axioms never
end BB6Coverage.Agent19Raw38Pump
