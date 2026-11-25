import WordBlock

namespace BB6.Agent12LongWord
open BB6.Agent12WordBlock

/-- Number of consecutive direct shifts at the beginning of a word. -/
def leadOnes : List Nat → Nat
  | [] => 0
  | r::rs => if r=1 then 1+leadOnes rs else 0

/-- Maximum number of consecutive direct shifts anywhere in a word. -/
def maxOnes : List Nat → Nat
  | [] => 0
  | r::rs => max (leadOnes (r::rs)) (maxOnes rs)

theorem lead_le_max (rs : List Nat) : leadOnes rs ≤ maxOnes rs := by
  cases rs with
  | nil => simp [leadOnes,maxOnes]
  | cons r rs => exact Nat.le_max_left _ _

theorem max_tail (r : Nat) (rs : List Nat) : maxOnes rs ≤ maxOnes (r::rs) := by
  exact Nat.le_max_right _ _

/-- Only individual shift depth and consecutive direct runs consume the
    mass margin. A regular bounce resets the reverse gap to > M/2. -/
theorem bounded_word_certificate (next : Nat × Nat → Option (Nat × Nat))
    (law : EdgeLaw next) (L H : Nat) (rs : List Nat) (s : State)
    (hr : ∀ r ∈ rs, 1≤r ∧ r≤H)
    (hl : maxOnes rs≤L)
    (hm : 8*2^H≤s.m) (hmL : 40*2^L≤s.m)
    (hp : consistent s)
    (hx : 0≤(run rs s).a)
    (hg : 20*(2:Int)^L≤gap (run rs s)+4) :
    valid s ∧ 20*(2:Int)^(L-leadOnes rs)≤gap s+4 ∧
      runNext next rs.length (some (decode s))=some (decode (run rs s)) := by
  induction rs generalizing s with
  | nil =>
    simp only [run,leadOnes,Nat.sub_zero,List.length_nil,runNext] at hx hg ⊢
    have hP : 1≤(2:Int)^L := Int.pow_pos (by decide)
    have hmul := Int.mul_le_mul_of_nonneg_left hP (show (0:Int)≤20 by decide)
    exact ⟨⟨hx,by omega,hp⟩,hg,trivial⟩
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have hrs : ∀ t ∈ rs, 1≤t ∧ t≤H := by intro t ht; exact hr t (by simp [ht])
    have hls : maxOnes rs≤L := Nat.le_trans (max_tail r rs) hl
    have hm' : 8*2^H≤(step r s).m := by simp [step]; omega
    have hmL' : 40*2^L≤(step r s).m := by simp [step]; omega
    have hp' := step_consistent r s hr0.1
    obtain ⟨hv',hbudget,hrun⟩ := ih (step r s) hrs hls hm' hmL' hp' hx hg
    have hP : 1≤(2:Int)^(L-leadOnes rs) := Int.pow_pos (by decide)
    have hmul := Int.mul_le_mul_of_nonneg_left hP (show (0:Int)≤20 by decide)
    have hg' : 16≤gap (step r s) := by omega
    have hpow : 2^r≤2^H := Nat.pow_le_pow_right (by decide : 0<2) hr0.2
    have hm0 : 8*2^r≤s.m := Nat.le_trans (Nat.mul_le_mul_left 8 hpow) hm
    obtain ⟨hv,_,_,hb,hrel⟩ := reverse_step r s hr0.1 hm0 hp hv'.1 hg'
    have he := source_step_of_law next law r s hr0.1 hm0 hp hv'.1 hg'
    refine ⟨hv,?_,?_⟩
    · by_cases h1 : r=1
      · have hlead : leadOnes (r::rs)=1+leadOnes rs := by simp [leadOnes,h1]
        have hle := Nat.le_trans (lead_le_max (r::rs)) hl
        have hsub : L-leadOnes rs=(L-leadOnes (r::rs))+1 := by rw [hlead] at hle ⊢; omega
        rw [show (2:Int)^r=2 from by simp [h1]] at hrel
        rw [hsub,Int.pow_succ] at hbudget
        have hh : 20*(2:Int)^(L-leadOnes (r::rs))*2≤2*(gap s+4) := by omega
        omega
      · have hlead : leadOnes (r::rs)=0 := by simp [leadOnes,h1]
        rw [hlead,Nat.sub_zero]
        simp only [h1,ite_false] at hb
        have hmI : 40*(2:Int)^L≤(s.m:Int) := by exact_mod_cast hmL
        unfold gap
        omega
    · simp only [List.length_cons,runNext,Option.bind_some,he,run]
      exact hrun

theorem bounded_block_certificate (next : Nat × Nat → Option (Nat × Nat))
    (law : EdgeLaw next) (L H : Nat) (rs : List Nat) (s t : State)
    (hr : ∀ r ∈ rs, 1≤r ∧ r≤H) (hl : maxOnes rs≤L)
    (hm : 8*2^H≤s.m) (hmL : 40*2^L≤s.m) (hp : consistent s)
    (he : applyCoeff (coeff rs (s.m%2)) s=t)
    (hx : 0≤t.a) (hg : 20*(2:Int)^L≤gap t+4) :
    runNext next rs.length (some (decode s))=some (decode t) := by
  rw [←run_eq_coeff] at he
  rw [←he] at hx hg ⊢
  exact (bounded_word_certificate next law L H rs s hr hl hm hmL hp hx hg).2.2

#print axioms bounded_word_certificate
#print axioms bounded_block_certificate
end BB6.Agent12LongWord
