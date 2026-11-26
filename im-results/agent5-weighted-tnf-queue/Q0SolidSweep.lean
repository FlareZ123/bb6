import BlockPump

namespace BB6Coverage.Agent5SolidSweep
open Agent50Pump Agent50Zipper

/-- q_i(0,100) checkpoint active row 26, first stubborn extension.
    Only F0 remains unassigned. -/
def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true  => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true  => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true  => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨true,false,0⟩)
  | _,_ => none

def ones : Nat → List Bool
  | 0 => []
  | n+1 => true :: ones n

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones]
  | succ a ih => simpa [Nat.succ_add,ones] using congrArg (true :: ·) ih

def family (n : Nat) : HZ := ⟨3,[true],ones (3*n+2)⟩

theorem entry : hrun table 8 ⟨0,[],[]⟩ = some (family 0) := rfl

theorem prelude (r : List Bool) : hrun table 3 ⟨3,[true],r⟩ = some ⟨1,[true,true],true::r⟩ := rfl

theorem rightBlock (l r : List Bool) :
    hrun table 7 ⟨1,true::l,true::true::true::r⟩ =
    some ⟨1,true::true::true::true::l,r⟩ := rfl

theorem rightSweep (n a : Nat) (r : List Bool) :
    hrun table (7*n) ⟨1,true::ones a,ones (3*n)++r⟩ =
    some ⟨1,true::ones (3*n+a),r⟩ := by
  induction n generalizing a with
  | zero => simp [hrun,ones]
  | succ n ih =>
    rw [show 7*(n+1)=7+7*n by omega, hrun_add]
    rw [show 3*(n+1)=3+3*n by omega, ones_add]
    simp only [List.append_assoc]
    change (hrun table 7 ⟨1,true::ones a,true::true::true::(ones (3*n)++r)⟩).bind (hrun table (7*n)) = _
    rw [rightBlock]
    change hrun table (7*n) ⟨1,true::ones (a+3),ones (3*n)++r⟩ = _
    rw [ih]
    rw [show 3*n+(a+3)=3+3*n+a by omega]

theorem turn (l : List Bool) : hrun table 7 ⟨1,true::true::true::l,[]⟩ =
    some ⟨3,true::true::l,[true,true]⟩ := rfl

theorem leftSweep (n : Nat) (l r : List Bool) :
    hrun table n ⟨3,ones n++l,r⟩ = some ⟨3,l,ones n++r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    change hrun table n ⟨3,ones n++l,true::r⟩ = _
    rw [ih]
    congr 2
    rw [ones_add n 1]
    simp [ones,List.append_assoc]

theorem growth (n : Nat) : hrun table (10*n+20) (family n) = some (family (n+1)) := by
  have h₁ := prelude (ones (3*n+2))
  change hrun table 3 (family n) = some ⟨1,true::ones 1,ones (3*(n+1))⟩ at h₁
  have h₂ := rightSweep (n+1) 1 []
  rw [List.append_nil] at h₂
  have h₃ := turn (ones (3*n+2))
  have h₃' : hrun table 7 ⟨1,true::ones (3*(n+1)+1),[]⟩ =
      some ⟨3,ones (3*(n+1))++[true],[true,true]⟩ := by
    have e : ones (3*(n+1)) ++ [true] = ones (3*(n+1)+1) := (ones_add _ 1).symm
    rw [e]
    exact h₃
  have h₄ := leftSweep (3*(n+1)) [true] [true,true]
  have e : ones (3*(n+1)) ++ [true,true] = ones (3*(n+1)+2) := (ones_add _ 2).symm
  rw [e] at h₄
  have h := hjoin (hjoin (hjoin h₁ h₂) h₃') h₄
  rw [show 10*n+20 = 3+7*(n+1)+7+3*(n+1) by omega]
  exact h

theorem exactReturns (n : Nat) :
    hrun table (5*n*n+15*n+8) ⟨0,[],[]⟩ = some (family n) := by
  induction n with
  | zero => exact entry
  | succ n ih =>
    have h := hjoin ih (growth n)
    rw [show 5*(n+1)*(n+1)+15*(n+1)+8 = 5*n*n+15*n+8+(10*n+20) by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega]
    exact h

/-- Every completion is live, even when F0 is an actual halting row. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  let k := 5*n*n+15*n+8
  have hk : n ≤ k := by
    dsimp [k]
    have h : n ≤ 15*n := by omega
    omega
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 (exactReturns n)
  have H := zrun_sound table m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

#print axioms exactReturns
#print axioms never

end BB6Coverage.Agent5SolidSweep

namespace BB6Coverage.Agent5SolidSweep28
open Agent50Pump Agent50Zipper
open Agent5SolidSweep (ones ones_add family)

/-- q0 active row 28, F1=0RE and E0=1LE; F0 unassigned. -/
def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 2,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => Agent5SolidSweep.table (q,b)

theorem entry : hrun table 8 ⟨0,[],[]⟩ = some (family 0) := rfl

theorem prelude (r : List Bool) : hrun table 3 ⟨3,[true],r⟩ = some ⟨1,[true,true],true::r⟩ := rfl

theorem firstBlock (l r : List Bool) :
    hrun table 6 ⟨1,true::l,true::true::true::r⟩ =
      some ⟨4,r.headD false::false::true::true::true::l,r.tail⟩ := by
  cases r <;> rfl

theorem eBlock (l r : List Bool) :
    hrun table 5 ⟨4,true::false::l,true::true::r⟩ =
      some ⟨4,r.headD false::false::true::true::true::l,r.tail⟩ := by
  cases r <;> rfl

theorem eSweep (n a : Nat) :
    hrun table (5*n) ⟨4,(ones (3*n)).headD false::false::ones a,(ones (3*n)).tail⟩ =
      some ⟨4,false::false::ones (3*n+a),[]⟩ := by
  induction n generalizing a with
  | zero => simp [hrun,ones]
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,hrun_add]
    rw [show 3*(n+1)=3+3*n by omega,ones_add 3 (3*n)]
    change (hrun table 5 ⟨4,true::false::ones a,true::true::ones (3*n)⟩).bind (hrun table (5*n)) = _
    rw [eBlock]
    change hrun table (5*n) ⟨4,(ones (3*n)).headD false::false::ones (a+3),(ones (3*n)).tail⟩ = _
    rw [ih,show 3*n+(a+3)=3+3*n+a by omega]

theorem turn (l : List Bool) : hrun table 6 ⟨4,false::false::true::true::l,[]⟩ =
    some ⟨3,true::true::l,[true,true]⟩ := rfl

theorem leftSweep (n : Nat) (l r : List Bool) :
    hrun table n ⟨3,ones n++l,r⟩ = some ⟨3,l,ones n++r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    change hrun table n ⟨3,ones n++l,true::r⟩ = _
    rw [ih]
    congr 2
    rw [ones_add n 1]
    simp [ones,List.append_assoc]

theorem growth (n : Nat) : hrun table (8*n+18) (family n) = some (family (n+1)) := by
  have h₁ := prelude (ones (3*n+2))
  change hrun table 3 (family n) = some ⟨1,[true,true],ones (3*(n+1))⟩ at h₁
  have h₂ := firstBlock [true] (ones (3*n))
  have hh : ones (3*(n+1)) = true::true::true::ones (3*n) := by
    rw [show 3*(n+1)=3+3*n by omega]
    exact ones_add 3 (3*n)
  rw [← hh] at h₂
  have h₃ := eSweep n 4
  have h₄ := turn (ones (3*n+2))
  have h₄' : hrun table 6 ⟨4,false::false::ones (3*n+4),[]⟩ =
      some ⟨3,ones (3*(n+1))++[true],[true,true]⟩ := by
    have e : ones (3*(n+1)) ++ [true] = ones (3*(n+1)+1) := (ones_add _ 1).symm
    rw [e]
    exact h₄
  have h₅ := leftSweep (3*(n+1)) [true] [true,true]
  have e : ones (3*(n+1)) ++ [true,true] = ones (3*(n+1)+2) := (ones_add _ 2).symm
  rw [e] at h₅
  have h := hjoin (hjoin (hjoin (hjoin h₁ h₂) h₃) h₄') h₅
  rw [show 8*n+18 = 3+6+5*n+6+3*(n+1) by omega]
  exact h

theorem exactReturns (n : Nat) :
    hrun table (4*n*n+14*n+8) ⟨0,[],[]⟩ = some (family n) := by
  induction n with
  | zero => exact entry
  | succ n ih =>
    have h := hjoin ih (growth n)
    rw [show 4*(n+1)*(n+1)+14*(n+1)+8 = 4*n*n+14*n+8+(8*n+18) by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega]
    exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  let k := 4*n*n+14*n+8
  have hk : n ≤ k := by
    dsimp [k]
    have h : n ≤ 14*n := by omega
    omega
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 (exactReturns n)
  have H := zrun_sound table m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

#print axioms exactReturns
#print axioms never
end BB6Coverage.Agent5SolidSweep28
