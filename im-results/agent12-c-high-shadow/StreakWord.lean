import WordBlock

namespace BB6.Agent12StreakWord
open BB6.Agent12WordBlock

/-- The direct streak ending at the current vertex. A bounce resets it. -/
def advance (d r : Nat) : Nat := if r=1 then d+1 else 0

def endStreak (d : Nat) : List Nat → Nat
  | [] => d
  | r::rs => endStreak (advance d r) rs

/-- Every shift lies in [1,R], and every prefix direct streak is at most D.
    An arbitrary incoming streak d permits compositional use. -/
def boundedWord (R D : Nat) (d : Nat) : List Nat → Bool
  | [] => decide (d≤D)
  | r::rs => decide (d≤D ∧ 1≤r ∧ r≤R) && boundedWord R D (advance d r) rs

theorem direct_gap (s : State) : gap (step 1 s)+4=2*(gap s+4) := by
  simp [gap,step,parity]
  omega

private theorem gap_at_least (d : Nat) (g : Int)
    (h : 20*(2:Int)^d≤g+4) : 16≤g := by
  have hp : 0<(2:Int)^d := Int.pow_pos (by decide)
  omega

/-- Unlike word_certificate, these endpoint guards depend only on the maximum
    single shift and maximum consecutive direct streak, not total shift.
    Backward bounces restore the gap to more than half the current mass. -/
theorem long_word_certificate (next : Nat × Nat → Option (Nat × Nat))
    (law : EdgeLaw next) (R D d : Nat) (rs : List Nat) (s : State)
    (hb : boundedWord R D d rs = true)
    (hm : 8*2^R≤s.m) (hd : 40*2^D≤s.m) (hp : consistent s)
    (hx : 0≤(run rs s).a)
    (hg : 20*(2:Int)^endStreak d rs≤gap (run rs s)+4) :
    valid s ∧ 20*(2:Int)^d≤gap s+4 ∧
      runNext next rs.length (some (decode s))=some (decode (run rs s)) := by
  induction rs generalizing d s with
  | nil =>
    simp only [run,endStreak] at hx hg
    exact ⟨⟨hx,by have := gap_at_least d (gap s) hg; omega,hp⟩,hg,rfl⟩
  | cons r rs ih =>
    have hcheck : (d≤D ∧ 1≤r ∧ r≤R) ∧ boundedWord R D (advance d r) rs = true := by
      simpa [boundedWord] using hb
    obtain ⟨⟨hdD,hr,hrR⟩,htail⟩ := hcheck
    have hm' : 8*2^R≤(step r s).m := by simp [step]; omega
    have hd' : 40*2^D≤(step r s).m := by simp [step]; omega
    have hp' := step_consistent r s hr
    have hx' : 0≤(run rs (step r s)).a := hx
    have hg' : 20*(2:Int)^endStreak (advance d r) rs≤gap (run rs (step r s))+4 := hg
    obtain ⟨hv',hbudget,hrun⟩ := ih (advance d r) (step r s) htail hm' hd' hp' hx' hg'
    have hm0 : 8*2^r≤s.m := Nat.le_trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right (by decide) hrR)) hm
    have hgap := gap_at_least (advance d r) (gap (step r s)) hbudget
    obtain ⟨hv,_,_,hbranch,_⟩ := reverse_step r s hr hm0 hp hv'.1 hgap
    have hnew : 20*(2:Int)^d≤gap s+4 := by
      by_cases h : r=1
      · subst r
        simp only [advance,ite_true] at hbudget
        rw [Int.pow_succ,direct_gap] at hbudget
        omega
      · have hbranch' : 2*s.a<(s.m:Int) := by simpa [h] using hbranch
        have hmass : 40*2^d≤s.m := Nat.le_trans (Nat.mul_le_mul_left 40 (Nat.pow_le_pow_right (by decide) hdD)) hd
        have hmass' : (40:Int)*(2:Int)^d≤(s.m:Int) := by exact_mod_cast hmass
        unfold gap
        omega
    have he := source_step_of_law next law r s hr hm0 hp hv'.1 hgap
    refine ⟨hv,hnew,?_⟩
    simp only [List.length_cons,runNext,Option.bind_some,he,run]
    exact hrun

/-- The endpoint is evaluated from cached coefficients, without inspecting
    intermediate states. Starting streak zero is the common use case. -/
theorem long_block_certificate (next : Nat × Nat → Option (Nat × Nat))
    (law : EdgeLaw next) (R D : Nat) (rs : List Nat) (s t : State)
    (hb : boundedWord R D 0 rs = true)
    (hm : 8*2^R≤s.m) (hd : 40*2^D≤s.m) (hp : consistent s)
    (he : applyCoeff (coeff rs (s.m%2)) s=t)
    (hx : 0≤t.a) (hg : 20*(2:Int)^endStreak 0 rs≤gap t+4) :
    runNext next rs.length (some (decode s))=some (decode t) := by
  rw [←run_eq_coeff] at he
  rw [←he] at hx hg ⊢
  exact (long_word_certificate next law R D 0 rs s hb hm hd hp hx hg).2.2

#print axioms direct_gap
#print axioms long_word_certificate
#print axioms long_block_certificate
end BB6.Agent12StreakWord
