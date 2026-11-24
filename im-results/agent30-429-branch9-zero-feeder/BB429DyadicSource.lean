import BB429DyadicTransport
import BB429NewResidue

namespace BB429DyadicSource
open BB429NewResidue BB429DyadicTransport

/-- The signed version of the unchanged source's basic mod-eight invariant. -/
def basicTest (a b : Int) : Bool := decide (
  (a%8=0 ∧ (b%4=0 ∨ b%4=2)) ∨
  (a%8=1 ∧ (b%4=0 ∨ b%4=1 ∨ b%4=2)) ∨
  (a%8=2 ∧ b%4=2) ∨
  (a%8=3 ∧ (b%4=1 ∨ b%4=2 ∨ b%4=3)) ∨
  (a%8=4 ∧ b%4=2) ∨
  a%8=5 ∨
  (a%8=6 ∧ b%4=2) ∨
  (a%8=7 ∧ (b%4=2 ∨ b%4=3)))

theorem grammar : InverseGrammar Reach := by
  constructor
  · intro a b ha ho hr
    rcases odd_back a b ha ho hr with ⟨x,y,hp,hx,hy⟩ | h
    · exact Or.inl ⟨x,y,hp,hx,by omega⟩
    · exact Or.inr h
  · intro a b ha he hr
    exact even_back a b (by omega) he hr

theorem basicTest_sound (a b : Int) (x y : Nat) (_ : 33 ≤ x)
    (hr : Reach x y) (h : Near 64 a b x y) : basicTest a b = true := by
  obtain ⟨i,j,hi,hj⟩ := h
  have ha : a%8 = (x:Int)%8 := by omega
  have hb : b%4 = (y:Int)%4 := by omega
  have hallowed := reach_allowed x y hr
  unfold BB429Mod8.Allowed at hallowed
  unfold basicTest
  apply decide_eq_true
  rw [ha,hb]
  exact_mod_cast hallowed

theorem exclude (d : Nat) (a b : Int) (x y : Nat)
    (high : 36*2^d ≤ x+3) (h : Near (scale d) a b x y)
    (hfalse : search basicTest d a b = false) : ¬ Reach x y := by
  intro hr
  have htrue := search_sound Reach grammar basicTest basicTest_sound d a b x y high hr h
  rw [hfalse] at htrue
  contradiction

#print axioms exclude
end BB429DyadicSource
