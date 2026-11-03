import PosEvenForm
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6.Fast
open BB6.Agent1

def Gfuel : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0,0)
  | fuel+1, k, c =>
      if c < 2*k then Gfuel fuel (k-(c/2+1)) (2*c+3)
      else if c ≤ 2*k+1 then (0,2*c+3)
      else (4*k+4,c-(2*k+2))

theorem Gfuel_eq (fuel k c : Nat) (hk : k < fuel) :
    Gfuel fuel k c = G k c := by
  induction fuel generalizing k c with
  | zero => omega
  | succ fuel ih =>
      rw [Gfuel, G]
      by_cases hlow : c < 2*k
      · simp only [hlow, ite_true, dite_true]
        apply ih
        omega
      · simp only [hlow, ite_false, dite_false]

def Gfast (k c : Nat) : Nat × Nat := Gfuel (k+1) k c

theorem Gfast_eq (k c : Nat) : Gfast k c = G k c :=
  Gfuel_eq (k+1) k c (by omega)

def Tfast (a c : Nat) : Option (Nat × Nat) :=
  if c=0 then some (2,a+1)
  else if c=1 then some (a+2,0)
  else if a%2=0 then some (a+3,c-2)
  else if c=2 then none
  else if c=3 then some (Gfast (a/2) 1)
  else some (Gfast (a/2+1) (c-2))

theorem Tfast_eq (a c : Nat) : Tfast a c = T a c := by
  unfold Tfast T
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> simp [Gfast_eq]

def trace : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, p => some p
  | n+1, p => (Tfast p.1 p.2).bind (trace n)

#print axioms Tfast_eq
end BB6.Fast
