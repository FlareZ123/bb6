import IndependentSweepCore
namespace BB6Coverage.Agent40Recursive
open BB6Coverage Agent31Pump Agent40Independent

def PositiveRun (p : PartialMachine) (a b : Z0) : Prop :=
  ∃ k, 0 < k ∧ run0 p k a = some b

theorem PositiveRun.trans {p : PartialMachine} {a b c : Z0}
    (h : PositiveRun p a b) (j : PositiveRun p b c) : PositiveRun p a c := by
  obtain ⟨k,hk,hr⟩ := h
  obtain ⟨l,hl,hs⟩ := j
  exact ⟨k+l,by omega,join0 hr hs⟩

def D (g : Nat) (b : Bool) (n : Nat) (R : List Bool) : Z0 :=
  ⟨3,b::false::List.replicate (g*n+2) true ++ [false,false],R⟩

def A (R : List Bool) : Z0 := ⟨0,[true,false],R⟩

def Z (n : Nat) : List Bool := List.replicate n false

theorem Z_add (a b : Nat) : Z (a+b) = Z a ++ Z b := by
  exact List.replicate_append_replicate.symm

theorem zero_chunk (g k : Nat) (hg : 0 < g) (R : List Bool) :
    Z (g*(k+1)+(g-1)) ++ true::R =
    Z (g-1) ++ false::(Z (g*k+(g-1)) ++ true::R) := by
  have h : g*(k+1)+(g-1) = (g-1)+(1+(g*k+(g-1))) := by rw [Nat.mul_succ]; omega
  rw [h,Z_add, Z_add]
  simp [Z,List.append_assoc]

/-- Nested counter restoration: the n-th restore calls only restores at
    strictly smaller counter indices. All tail words are arbitrary. -/
theorem restore (p : PartialMachine) (g : Nat) (hg : 0 < g)
    (reset : ∀ n R, PositiveRun p (D g false n R) (A (Z (g*n+3) ++ true::R)))
    (seed : ∀ R, PositiveRun p (A (Z 3 ++ true::R)) (D g true 0 R))
    (pref : ∀ R, PositiveRun p (A (Z 4 ++ R)) (D g true 0 R))
    (advance : ∀ b n R, PositiveRun p (D g true n (Z (g-1) ++ b::R)) (D g b (n+1) R)) :
    ∀ n R, PositiveRun p (D g false n R) (D g true n R) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro R
    cases n with
    | zero => exact (reset 0 R).trans (seed R)
    | succ n =>
      have walk : ∀ k j, j+k=n → ∀ T,
          PositiveRun p (D g true j (Z (g*k+(g-1)) ++ true::T)) (D g true (n+1) T) := by
        intro k
        induction k with
        | zero =>
          intro j hj T
          have h : j=n := by omega
          subst j
          simpa using advance true n T
        | succ k ihk =>
          intro j hj T
          let tail := Z (g*k+(g-1)) ++ true::T
          have ha := advance false j tail
          have hb := ih (j+1) (by omega) tail
          have hc := ihk (j+1) (by omega) T
          have eq := zero_chunk g k hg T
          rw [← eq] at ha
          exact ha.trans (hb.trans hc)
      have hsplit : g*(n+1)+3 = 4 + (g*n+(g-1)) := by rw [Nat.mul_succ]; omega
      have h0 := reset (n+1) R
      rw [hsplit,Z_add,List.append_assoc] at h0
      exact h0.trans ((pref (Z (g*n+(g-1)) ++ true::R)).trans (walk n 0 (by omega) R))

theorem growing (p : PartialMachine) (g : Nat) (hg : 0 < g)
    (reset : ∀ n R, PositiveRun p (D g false n R) (A (Z (g*n+3) ++ true::R)))
    (seed : ∀ R, PositiveRun p (A (Z 3 ++ true::R)) (D g true 0 R))
    (pref : ∀ R, PositiveRun p (A (Z 4 ++ R)) (D g true 0 R))
    (advance : ∀ b n R, PositiveRun p (D g true n (Z (g-1) ++ b::R)) (D g b (n+1) R))
    (blank : ∀ n, PositiveRun p (D g true n []) (D g false (n+1) [])) :
    ∀ n, PositiveRun p (D g false n []) (D g false (n+1) []) := by
  intro n
  exact (restore p g hg reset seed pref advance n []).trans (blank n)
#print axioms restore
#print axioms growing
end BB6Coverage.Agent40Recursive
