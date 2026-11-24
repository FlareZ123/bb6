import Lean
namespace BB6.Agent43CarryCert

def step (Q j : Nat) (cs : List Nat) : List Nat :=
  cs.flatMap fun c =>
    (if c % 2 = 0 then [c/2] else []) ++
    (if (c+(Q-j)) % 2 = 0 then [(c+(Q-j))/2] else [])

def states (Q j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k+1 => states Q (j+1) (step Q j cs) k

def checkTo (Q j : Nat) (cs : List Nat) (ds : List Nat) : Nat → Bool
  | 0 => cs == ds
  | k+1 => !cs.contains 2 && checkTo Q (j+1) (step Q j cs) ds k

def Safe (Q j : Nat) (cs : List Nat) (k : Nat) (ds : List Nat) : Prop :=
  states Q j cs k = ds ∧ ∀ i<k, 2 ∉ states Q j cs i

theorem check_sound (Q j : Nat) (cs ds : List Nat) (K : Nat)
    (h : checkTo Q j cs ds K = true) : Safe Q j cs K ds := by
  induction K generalizing j cs with
  | zero =>
      simp [checkTo, Safe, states] at h ⊢
      exact h
  | succ k ih =>
      simp only [checkTo, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hno, htail⟩ := h
      obtain ⟨he, hall⟩ := ih (j+1) (step Q j cs) htail
      refine ⟨he, ?_⟩
      intro i hi
      cases i with
      | zero =>
          intro hm
          change 2 ∈ cs at hm
          have hh : cs.contains 2 = true := List.contains_iff_mem.mpr hm
          rw [hh] at hno
          contradiction
      | succ i => exact hall i (by omega)

theorem states_add (Q j a b : Nat) (cs : List Nat) :
    states Q j cs (a+b) = states Q (j+a) (states Q j cs a) b := by
  induction a generalizing j cs with
  | zero => simp [states]
  | succ a ih =>
      rw [Nat.succ_add, states, ih, states]
      congr 1
      omega

theorem Safe.append {Q j a b : Nat} {cs ds es : List Nat}
    (h : Safe Q j cs a ds) (h' : Safe Q (j+a) ds b es) : Safe Q j cs (a+b) es := by
  obtain ⟨he, hn⟩ := h
  obtain ⟨he', hn'⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [states_add, he, he']
  · intro i hi
    by_cases hlt : i<a
    · exact hn i hlt
    · have hi' : i=a+(i-a) := by omega
      rw [hi', states_add, he]
      exact hn' (i-a) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem safe30 : Safe (7*2^30-(30+3)) 0 [1] 82 [] :=
  check_sound (7*2^30-(30+3)) 0 [1] [] 82 (by decide)

#print axioms check_sound
#print axioms Safe.append
#print axioms safe30
end BB6.Agent43CarryCert
