import LagReverse

namespace BB6.Agent43PackedRecover
open BB6.Agent45.DelayedCarry

/-- Work with the fixed low product directly, rather than recomputing it
    or forming a huge quotient at each bit. -/
def targetBit (n i P : Nat) : Nat := if i<n then 0 else if P.testBit (i-n) then 1 else 0

theorem targetBit_eq (n i B : Nat) : targetBit n i (7*B)=target n i B := by
  unfold targetBit target
  split
  · simp_all
  · rw [Nat.testBit_eq_decide_div_mod_eq]
    split <;> simp_all <;> omega

/-- Reverse a small block of k selected digits, accumulating only its local
    word. This can be evaluated with a machine-size word for k<=32. -/
def smallCode (n P s : Nat) : Nat → Nat → Nat × Nat
  | 0,c => (0,c)
  | k+1,c =>
    let q := n+(s+k)+3
    let z := 2*c+targetBit n (s+k) P
    let r := smallCode n P s k (z%q)
    (r.1+((z/q) <<< k),r.2)

theorem smallCode_recover (n B s k c : Nat) :
    recover n B s k c = (B+2^s*(smallCode n (7*B) s k c).1,(smallCode n (7*B) s k c).2) := by
  induction k generalizing c with
  | zero => simp [recover,smallCode]
  | succ k ih =>
    simp only [recover,smallCode,targetBit_eq,predecessor,reverseDigit]
    rw [ih]
    apply Prod.ext
    · simp only [Nat.shiftLeft_eq,Nat.mul_add,Nat.pow_add]
      ac_rfl
    · rfl

/-- Split local code into a lower and upper segment. Fixed target product
    is unchanged even when the reverse start clock changes. -/
theorem smallCode_add (n P s k j c : Nat) :
    smallCode n P s (k+j) c =
      let hi := smallCode n P (s+k) j c
      let lo := smallCode n P s k hi.2
      (lo.1+2^k*hi.1,lo.2) := by
  induction j generalizing c with
  | zero => simp [smallCode]
  | succ j ih =>
    rw [Nat.add_succ,smallCode,smallCode]
    simp only [show s+(k+j)=s+k+j by omega]
    rw [ih]
    simp only [Nat.mul_add,Nat.shiftLeft_eq,Nat.pow_add]
    apply Prod.ext
    · ac_rfl
    · rfl

/-- Balanced recovery: recursion depth logarithmic, with a small scalar
    leaf block. Each large-word concatenation uses only a shift and add. -/
def balancedCode (n P s k c : Nat) : Nat × Nat :=
  if _h : k≤32 then smallCode n P s k c else
    let j := k/2
    let hi := balancedCode n P (s+j) (k-j) c
    let lo := balancedCode n P s j hi.2
    (lo.1+(hi.1 <<< j),lo.2)
termination_by k
decreasing_by all_goals omega

theorem balancedCode_eq (n P s k c : Nat) :
    balancedCode n P s k c = smallCode n P s k c := by
  induction k using Nat.strongRecOn generalizing s c with
  | ind k ih =>
    rw [balancedCode]
    split
    · rfl
    · rename_i hk
      simp only [ih (k-k/2) (by omega),ih (k/2) (by omega)]
      have he := smallCode_add n P s (k/2) (k-k/2) c
      rw [show k/2+(k-k/2)=k by omega] at he
      rw [he]
      simp only [Nat.shiftLeft_eq,Nat.mul_comm]

def recoverFast (n B s k c : Nat) : Nat × Nat :=
  let r := balancedCode n (7*B) s k c
  (B+(r.1 <<< s),r.2)

theorem recoverFast_eq (n B s k c : Nat) :
    recoverFast n B s k c=recover n B s k c := by
  rw [smallCode_recover]
  simp only [recoverFast,balancedCode_eq,Nat.shiftLeft_eq,Nat.mul_comm]

theorem recoverFast_exact (n s B a k C c : Nat) (ht : Trace n s B a)
    (he : Extend n s B a k C c) (hk : k≤n) : recoverFast n B s k c=(C,a) := by
  rw [recoverFast_eq]
  exact recover_exact n s B a k C c ht he hk

#print axioms recoverFast_eq
#print axioms recoverFast_exact
end BB6.Agent43PackedRecover
