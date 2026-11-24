import Lean

namespace BB6.Agent23FullCone

-- Exact copy of Agent28's full-carry recurrence.
def step (Q j : Nat) (cs : List Nat) : List Nat :=
  cs.flatMap fun c =>
    (if c % 2 = 0 then [c/2] else []) ++
    (if (c+(Q-j)) % 2 = 0 then [(c+(Q-j))/2] else [])

def states (Q j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k+1 => states Q (j+1) (step Q j cs) k

-- P = 2^n. The bound simultaneously provides the left-counter margin
-- and excludes the only possible adjacent power of fourteen for an even exit.
def safe (P n j v : Nat) : Bool :=
  (v != 2) && decide (v+2*j+2*n+3 < 7*P)

def cert (P n Q j : Nat) (cs : List Nat) : Nat → Bool
  | 0 => cs.isEmpty
  | k+1 => cs.all (safe P n j) && cert P n Q (j+1) (step Q j cs) k

theorem cert_sound (P n Q j : Nat) (cs : List Nat) (k : Nat)
    (h : cert P n Q j cs k = true) :
    states Q j cs k = [] ∧
    ∀ i < k, ∀ v ∈ states Q j cs i, v ≠ 2 ∧ v+2*(j+i)+2*n+3 < 7*P := by
  induction k generalizing j cs with
  | zero =>
    have he : cs = [] := List.isEmpty_iff.mp (by simpa [cert] using h)
    exact ⟨by simpa [states] using he, by omega⟩
  | succ k ih =>
    simp only [cert, Bool.and_eq_true] at h
    obtain ⟨he, hs⟩ := ih (j+1) (step Q j cs) h.2
    constructor
    · simpa [states] using he
    · intro i hi v hv
      cases i with
      | zero =>
        have hh := List.all_eq_true.mp h.1 v (by simpa [states] using hv)
        simpa [safe] using hh
      | succ i =>
        have hh := hs i (by omega) v (by simpa [states] using hv)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem safe_left (P n j b d v : Nat)
    (hn : 14 ≤ n) (hd : d = 2*v+1)
    (hm : b+d+2*j+2*n+13=14*P)
    (hs : v+2*j+2*n+3 < 7*P) : 12 ≤ b := by omega

theorem safe_even_gap (P n l k c y : Nat)
    (hy : y=c+3) (hm : 2*k+c+2*l+2*n+14=14*P)
    (hs : y+2*l+2*n+3 < 7*P) (hn : 14 ≤ n) :
    7*P < 2*k+8 ∧ 2*k+8 < 14*P := by omega

theorem previous_odd_carry (t c c0 : Nat)
    (h : 2^(t+1)*(c+3)=2^t*(c0+3)) :
    (c0+4-1)/2=c+3 := by
  rw [Nat.pow_succ, Nat.mul_assoc] at h
  have he := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos t) h
  omega

theorem no_power (n a x : Nat) (hn : 1 ≤ n)
    (hl : 7*2^n < x) (hu : x < 14*2^n) : x ≠ 14*2^a := by
  intro he
  by_cases h : n ≤ a
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) h
    omega
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show a≤n-1 by omega)
    have hs : 2^n = 2^(n-1)*2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    omega

#print axioms cert_sound
#print axioms safe_left
#print axioms safe_even_gap
#print axioms previous_odd_carry
#print axioms no_power

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem cert30 : cert (2^30) 30 (7*2^30-33) 0 [1] 82 = true := by decide
#print axioms cert30

end BB6.Agent23FullCone
