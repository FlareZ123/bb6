import Agent49FastFailureSpectrumSource

/-!
A sharp universal cardinality bound for the complete first-counter failure
spectrum of the actual Cryptids #623 B-drain. All lemmas are quantified over
arbitrary block counts, and inherit original-source semantics through the
exact source-verified flat-drain equivalence.
-/

namespace BB6.Agent49Capacity
open BB6.Agent49FullSpectrum BB6.Agent49FastSpectrum

def cap (b : Nat) : Nat := 3 ^ (fastSpectrum b).length

theorem cap_odd (b : Nat) : cap b % 2 = 1 := by
  unfold cap
  induction (fastSpectrum b).length with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- The cardinality bound and the exact-rigidity property at saturation.
The latter eliminates the dangerous carry in the residue-two case. -/
theorem cap_and_saturation (b : Nat) :
    cap b ≤ 2*b+1 ∧ (cap b = 2*b+1 → fastSpectrum (b-1) = []) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hz : b=0
    · subst b
      simp [cap,fastSpectrum]
    · let q := b/3
      have hdiv : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hrep : b=3*q := by omega
        have hq : 0<q := by omega
        have hsmall : q-1<b := by omega
        have hprior := (ih (q-1) hsmall).1
        have hlen : (fastSpectrum b).length ≤ (fastSpectrum (q-1)).length := by
          conv => lhs; rw [fastSpectrum]
          simp only [hz,hr0, if_neg, if_pos]
          exact List.length_filterMap_le _ _
        have hpow : cap b ≤ cap (q-1) := by
          unfold cap
          exact Nat.pow_le_pow_right (by omega) hlen
        have hstrict : cap b < 2*b+1 := by
          omega
        exact ⟨by omega, by intro hc; omega⟩
      · by_cases hr1 : b%3=1
        · have hrep : b=3*q+1 := by omega
          have hsmall : q<b := by omega
          obtain ⟨hprior,hsat⟩ := ih q hsmall
          have hcap : cap b = 3*cap q := by
            unfold cap
            conv => lhs; rw [fastSpectrum]
            simp only [hz,hr0,hr1,ite_false,ite_true, List.length_cons,List.length_map]
            rw [show b / 3 = q by rfl]
            simp only [Nat.one_ne_zero, ite_false, List.length_cons, List.length_map]
            rw [Nat.pow_succ]
            omega
          constructor
          · omega
          · intro hsame
            have heq : cap q=2*q+1 := by omega
            have heqsmall := hsat heq
            have hq0 : q=0 ∨ 0<q := by omega
            rcases hq0 with hzero | hpos
            · have hb1 : b=1 := by omega
              simp [hb1,fastSpectrum]
            · have hbm : b-1 = 3*q := by omega
              rw [hbm, fastSpectrum]
              have hne : 3*q≠0 := by omega
              have hm : (3*q)%3=0 := by omega
              simp only [if_neg hne,if_pos hm]
              simpa [heqsmall, down]
        · have hr2 : b%3=2 := by omega
          have hrep : b=3*q+2 := by omega
          have hsmall : q+1<b := by omega
          obtain ⟨hprior,hsat⟩ := ih (q+1) hsmall
          by_cases hzero : badAll 0 q = true
          · have hcap : cap b = 3*cap (q+1) := by
              unfold cap
              conv => lhs; rw [fastSpectrum]
              simp only [hz,hr0,hr1,hr2,ite_false,ite_true,List.length_append,List.length_map]
              rw [show b / 3 = q by rfl]
              simp only [show (2:Nat)≠0 from by omega, show (2:Nat)≠1 from by omega, ite_false, hzero, ite_true, List.length_cons, List.length_append, List.length_map, List.length_nil, Nat.zero_add]
              rw [show 1 + (fastSpectrum (q+1)).length = (fastSpectrum (q+1)).length + 1 by omega, Nat.pow_succ]
              omega
            have hnempty : fastSpectrum q ≠ [] := by
              intro hempty
              have hmem : 0∈fastSpectrum q := (fastSpectrum_correct q 0).2 hzero
              simp [hempty] at hmem
            have hneq : cap (q+1) ≠ 2*(q+1)+1 := by
              intro hc
              exact hnempty (hsat hc)
            have hodd := cap_odd (q+1)
            have hstrict : cap b < 2*b+1 := by omega
            exact ⟨by omega,by intro hc;omega⟩
          · have hcap : cap b = cap (q+1) := by
              unfold cap
              conv => lhs; rw [fastSpectrum]
              have hf : badAll 0 q = false := by
                cases hh : badAll 0 q with
                | false => rfl
                | true => exact False.elim (hzero hh)
              simp only [hz,hr0,hr1,ite_false,ite_true,List.length_append,List.length_map]
              rw [show b / 3 = q by rfl]
              simp only [show (2:Nat)≠0 from by omega, show (2:Nat)≠1 from by omega, ite_false, hf, Bool.false_eq_true, List.length_nil, List.length_append, List.length_map, Nat.zero_add]
            have hstrict : cap b < 2*b+1 := by omega
            exact ⟨by omega,by intro hc;omega⟩

/-- Smallest feasible block count for n distinct fatal first counters. -/
def boundary : Nat → Nat
  | 0 => 0
  | n+1 => 3*boundary n+1

theorem boundary_power (n : Nat) : 2*boundary n+1=3^n := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
    simp only [boundary, Nat.pow_succ]
    omega

theorem boundary_spectrum (n : Nat) : fastSpectrum (boundary n) = List.range n := by
  induction n with
  | zero => simp [boundary,fastSpectrum]
  | succ n ih =>
    have hp : boundary (n+1)=3*boundary n+1 := rfl
    rw [hp,fastSpectrum]
    have hnz : 3*boundary n+1≠0 := by omega
    have h0 : (3*boundary n+1)%3≠0 := by omega
    have h1 : (3*boundary n+1)%3=1 := by omega
    have hdiv : (3*boundary n+1)/3=boundary n := by omega
    simp only [if_neg hnz, if_neg h0, if_pos h1, hdiv, ih]
    exact (List.range_succ_eq_map).symm

/-- n distinct failures in a B-drain require b ≥ (3^n-1)/2. -/
theorem minimum_blocks_for_n_failures (n b : Nat)
    (hn : n ≤ (fastSpectrum b).length) : boundary n ≤ b := by
  have hpower := (cap_and_saturation b).1
  have hpow : 3^n ≤ cap b := by
    unfold cap
    exact Nat.pow_le_pow_right (by omega) hn
  have heq := boundary_power n
  omega

/-- Every lower bound is attained, simultaneously at fatal counters 0..n-1. -/
theorem boundary_is_sharp (n : Nat) :
    (fastSpectrum (boundary n)).length = n := by
  rw [boundary_spectrum]
  simp


/-- Injective successor transport preserves distinct fatal first counters. -/
theorem nodup_succ (xs : List Nat) (h : xs.Nodup) : (xs.map Nat.succ).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hp := (List.nodup_cons.mp h)
    apply List.nodup_cons.mpr
    constructor
    · intro hh
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hh
      have hx : x=y := by omega
      exact hp.1 (hx ▸ hy)
    · exact ih hp.2

theorem nodup_down (xs : List Nat) (h : xs.Nodup) : (down xs).Nodup := by
  induction xs with
  | nil => simp [down]
  | cons x xs ih =>
    have hp := List.nodup_cons.mp h
    cases x with
    | zero =>
      simpa only [down, List.filterMap_cons, ↓reduceIte] using ih hp.2
    | succ x =>
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        have hx : x+1 ∈ xs := (mem_down xs x).1 hm
        exact hp.1 hx
      · exact ih hp.2

/-- The fast fatal spectrum contains no duplicate counters. -/
theorem spectrum_nodup (b : Nat) : (fastSpectrum b).Nodup := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    rw [fastSpectrum]
    by_cases hz : b=0
    · simp [hz]
    · simp only [if_neg hz]
      by_cases h0 : b%3=0
      · simp only [if_pos h0]
        exact nodup_down _ (ih (b/3-1) (by omega))
      · simp only [if_neg h0]
        by_cases h1 : b%3=1
        · simp only [if_pos h1]
          apply List.nodup_cons.mpr
          constructor
          · intro hh
            obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
            omega
          · exact nodup_succ _ (ih (b/3) (by omega))
        · simp only [if_neg h1]
          by_cases h2 : badAll 0 (b/3)=true
          · simp only [h2, if_pos, List.singleton_append]
            apply List.nodup_cons.mpr
            constructor
            · intro hh
              obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
              omega
            · exact nodup_succ _ (ih (b/3+1) (by omega))
          · have hf : badAll 0 (b/3)=false := by
              cases he : badAll 0 (b/3) with
              | false => rfl
              | true => exact False.elim (h2 he)
            simp only [hf, Bool.false_eq_true, if_false, List.nil_append]
            exact nodup_succ _ (ih (b/3+1) (by omega))


/-- The exact first block fatal for a given initial first counter. -/
def tight (a : Nat) : Nat := boundary a + 1

/-- At the first fatal block for counter n+1, the complete set of fatal
counters is the initial interval [0,n) together with n+1; n itself is safe. -/
theorem tight_spectrum (n : Nat) :
    fastSpectrum (tight (n+1)) = (List.range n) ++ [n+1] := by
  induction n with
  | zero =>
    simp [tight,boundary,fastSpectrum,badAll]
  | succ n ih =>
    have hrep : tight (n+1+1) = 3 * boundary (n+1) + 2 := by
      simp only [tight,boundary]
    rw [hrep,fastSpectrum]
    have hnz : 3*boundary (n+1)+2 ≠ 0 := by omega
    have hm0 : (3*boundary (n+1)+2)%3 ≠ 0 := by omega
    have hm1 : (3*boundary (n+1)+2)%3 ≠ 1 := by omega
    have hdiv : (3*boundary (n+1)+2)/3 = boundary (n+1) := by omega
    have hbad : badAll 0 (boundary (n+1)) = true := by
      apply (fastSpectrum_correct (boundary (n+1)) 0).1
      rw [boundary_spectrum]
      simp
    simp only [if_neg hnz, if_neg hm0, if_neg hm1, hdiv, hbad, if_pos]
    have hplus : boundary (n+1)+1 = tight (n+1) := rfl
    rw [hplus,ih]
    simp only [List.singleton_append, List.map_append, List.map_cons, List.map_nil]
    rw [List.range_succ_eq_map (n:=n)]
    simp only [List.cons_append]

#print axioms tight_spectrum

#print axioms spectrum_nodup

#print axioms minimum_blocks_for_n_failures
#print axioms boundary_spectrum
#print axioms cap_and_saturation

end BB6.Agent49Capacity
