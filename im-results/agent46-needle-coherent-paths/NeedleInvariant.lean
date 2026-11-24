import NeedleCoherent

namespace NeedleInvariant
open NeedleWord NeedleCoherent

def Closed (I : Nat → Prop) : Prop :=
  ∀ p b v q : Nat, p=2^v*(2*q+3) → b=p+v+3*(q+1) → I p → I b

def EventuallyPeriodic (I : Nat → Prop) (P T : Nat) : Prop :=
  ∀ x y : Nat, T≤x → T≤y → x%P=y%P → (I x ↔ I y)

theorem path_closed (I : Nat → Prop) (hI : Closed I) {w : List Nat} {p c : Nat}
    (hp : Path w p c) (h : I p) : I c := by
  induction hp with
  | nil => exact h
  | cons v q hp hb rest ih => exact ih (hI _ _ v q hp hb h)

/-- Any eventually periodic inductive set with even one member in its
periodic tail is cofinite. This uses coherent paths, not relaxed edges. -/
theorem cofinite (I : Nat → Prop) (M h T a : Nat) (hodd : M%2=1)
    (hper : EventuallyPeriodic I (2^h*M) T) (hclosed : Closed I)
    (haT : T≤a) (ha : I a) : ∀ b, T≤b → I b := by
  intro b hbT
  obtain ⟨w,p,c,_,hpT,hpa,hcb,hpath⟩ := coherent_classes M h a b T hodd
  have hpI := (hper p a hpT haT hpa).mpr ha
  have hcI := path_closed I hclosed hpath hpI
  have hpc := path_nondecreasing hpath
  exact (hper c b (by omega) hbT hcb).mp hcI

/-- General positive moduli factor into a dyadic part and an odd part. -/
theorem factor_modulus (P : Nat) (hP : 0<P) :
    ∃ h M : Nat, M%2=1 ∧ P=2^h*M := by
  induction P using Nat.strongRecOn with
  | ind P ih =>
    by_cases hodd : P%2=1
    · exact ⟨0,P,hodd,by simp⟩
    have hp : 0<P/2 := by omega
    have hlt : P/2<P := by omega
    obtain ⟨h,M,hm,he⟩ := ih (P/2) hlt hp
    refine ⟨h+1,M,hm,?_⟩
    rw [Nat.pow_succ]
    grind

/-- Closure and ultimate periodicity of a power-free set cannot coexist
with any admissible positive starting counter in the set. -/
theorem no_periodic_power_free (I : Nat → Prop) (P T a : Nat) (hP : 0<P)
    (hper : EventuallyPeriodic I P T) (hclosed : Closed I)
    (hfree : ∀ k : Nat, ¬ I (2^k)) (ha : I a) (haPos : 0<a) : False := by
  have climb : ∀ n x : Nat, 0<x → I x → ∃ y : Nat, n≤y ∧ I y := by
    intro n
    induction n with
    | zero => intro x hx hxI; exact ⟨x,by omega,hxI⟩
    | succ n ih =>
      intro x hx hxI
      obtain ⟨y,hy,hyI⟩ := ih x hx hxI
      by_cases hbig : n+1≤y
      · exact ⟨y,hbig,hyI⟩
      by_cases hy0 : y=0
      · rcases factor_or_power x hx with ⟨k,hk⟩ | ⟨v,q,hvq⟩
        · exact False.elim (hfree k (hk ▸ hxI))
        · refine ⟨x+v+3*(q+1),?_,hclosed _ _ v q hvq rfl hxI⟩
          omega
      · rcases factor_or_power y (Nat.pos_of_ne_zero hy0) with ⟨k,hk⟩ | ⟨v,q,hvq⟩
        · exact False.elim (hfree k (hk ▸ hyI))
        · exact ⟨y+v+3*(q+1),by omega,hclosed _ _ v q hvq rfl hyI⟩
  obtain ⟨b,hb,hbI⟩ := climb T a haPos ha
  obtain ⟨h,M,hm,he⟩ := factor_modulus P hP
  rw [he] at hper
  have htail := cofinite I M h T b hm hper hclosed hb hbI
  have hp := pow_two_gt T
  exact hfree T (htail (2^T) (by omega))

#print axioms cofinite
#print axioms factor_modulus
#print axioms no_periodic_power_free
end NeedleInvariant
