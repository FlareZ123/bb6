import Std
set_option maxHeartbeats 0
namespace CascadeFastReturn

def failed (h k : Nat) : Prop := h+k+5 < 8*2^k

def scan (h : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel+1, k => if h+k+5 < 8*2^k then k else scan h fuel (k+1)

theorem pow_ge_linear (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

theorem eventual_fail (h : Nat) : failed h (h+10) := by
  have hp := pow_ge_linear (h+10)
  dsimp [failed]
  omega

/-- If some failure occurs inside the scanned interval, scan returns its
    least such index, preserving guards at every earlier index. -/
theorem scan_spec (h f k : Nat)
    (hex : ∃ j, k≤j ∧ j≤k+f ∧ failed h j) :
    failed h (scan h (f+1) k) ∧
      ∀j, k≤j → j<scan h (f+1) k → ¬failed h j := by
  induction f generalizing k with
  | zero =>
    obtain ⟨j,hlo,hhi,hj⟩ := hex
    have hk : j=k := by omega
    subst j
    have hs : scan h (0+1) k = k := by
      simp [scan, show h+k+5<8*2^k from hj]
    rw [hs]
    constructor
    · exact hj
    · intro j hlo hlt; omega
  | succ f ih =>
    by_cases hk : failed h k
    · have hk' : h+k+5 < 8*2^k := hk
      simp only [scan, if_pos hk']
      constructor
      · exact hk
      · intro j hlo hlt
        omega
    · have hex' : ∃j, k+1≤j ∧ j≤(k+1)+f ∧ failed h j := by
        obtain ⟨j,hlo,hhi,hj⟩ := hex
        have hne : j≠k := by
          intro he; subst j; exact hk hj
        refine ⟨j,?_,?_,hj⟩ <;> omega
      have hh := ih (k+1) hex'
      have he : scan h ((f+1)+1) k = scan h (f+1) (k+1) := by
        have hk' : ¬(h+k+5 < 8*2^k) := hk
        simp [scan, hk']
      rw [he]
      constructor
      · exact hh.1
      · intro j hlo hlt
        by_cases hjk : j=k
        · subst j
          exact hk
        · exact hh.2 j (by omega) hlt

def firstFailedK (h : Nat) : Nat := scan h (h+11) 0

/-- The computable search finds the first failed sweep index; it performs
    only as many recursive tests as are necessary, independently of fuel. -/
theorem firstFailedK_spec (h : Nat) :
    failed h (firstFailedK h) ∧ ∀j, j<firstFailedK h → ¬failed h j := by
  have hi : ∃j, 0≤j ∧ j≤0+(h+10) ∧ failed h j :=
    ⟨h+10,by omega,by omega,eventual_fail h⟩
  simpa [firstFailedK] using scan_spec h (h+10) 0 hi

#print axioms firstFailedK_spec
end CascadeFastReturn
