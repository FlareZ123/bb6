import S4AllDepthGrowth
import Lean.Elab.Tactic.Omega

namespace S4PrefixGrowth
open S4Power S4Octet S4PrefixExact
set_option maxHeartbeats 0

/-- Every finite positive-offset odd-drain chain has a remarkably simple
all-suffix safety test: run the chain once on the bare prefix and check
that the surviving output grew by at most one digit. -/
theorem chain_survival_iff_short (cs T : List Nat)
    (hpos : ∀ c, c∈cs → 0<c)
    (hgate : ∀ c xs, 0<c → (G c xs=none ↔ ∃n,W xs+c=2^n)) :
    (∀ S : List Nat, chain cs (T++S)≠none) ↔
      ∃ U : List Nat, chain cs T=some U ∧ U.length≤T.length+1 := by
  constructor
  · intro hall
    have hsrc : chain cs T≠none := by
      simpa using hall []
    cases hs : chain cs T with
    | none => contradiction
    | some U =>
        refine ⟨U,rfl,?_⟩
        apply (chain_sharp_growth cs T U hpos hs).mp
        exact (chain_exact_prefix cs T hpos hgate).mp hall
  · rintro ⟨U,hs,hshort⟩
    apply (chain_exact_prefix cs T hpos hgate).mpr
    exact (chain_sharp_growth cs T U hpos hs).mpr hshort

/-- Single-step, source-exact S4 universal suffix-safety decision using
nothing beyond a successful bare-stack P evaluation and its output length. -/
theorem s4_survival_iff_short (T : List Nat) :
    (∀ S : List Nat, S4Toggle.P (T++S)≠none) ↔
      ∃ U : List Nat, S4Toggle.P T=some U ∧ U.length≤T.length+1 := by
  have hpos : ∀ c, c∈([509,290,219] : List Nat) → 0<c := by
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with h | h | h <;> omega
  have hgate : ∀ c xs, 0<c → (G c xs=none ↔ ∃n,W xs+c=2^n) := by
    intro c xs hc
    simpa [S4Power.Pow2] using S4Octet.G_none_iff_power c xs hc
  have hbase := chain_survival_iff_short [509,290,219] T hpos hgate
  have hmap : ∀ xs, chain [509,290,219] xs = S4Toggle.P xs := by
    intro xs
    simp [chain,S4Toggle.P]
  simpa only [hmap] using hbase

/-- On a surviving stack, an immediately halting synthetic completion
exists exactly at a large growth event. This is distinct from actual
blank-root halting and is valid at every stack depth. -/
theorem s4_synthetic_halt_iff_growth (T U : List Nat)
    (hP : S4Toggle.P T=some U) :
    (∃ S : List Nat, S4Toggle.P (T++S)=none) ↔
      T.length+2 ≤ U.length := by
  classical
  have hsafe := s4_survival_iff_short T
  constructor
  · rintro ⟨S,hS⟩
    by_cases hbig : T.length+2≤U.length
    · exact hbig
    · have hl : U.length≤T.length+1 := by omega
      exact False.elim ((hsafe.mpr ⟨U,hP,hl⟩) S hS)
  · intro hbig
    have hnot : ¬(∀ S, S4Toggle.P (T++S)≠none) := by
      intro hall
      obtain ⟨V,hV,hl⟩ := hsafe.mp hall
      have heq : U=V := Option.some.inj (hP.symm.trans hV)
      subst V
      omega
    have ⟨S,hS⟩ := Classical.not_forall.mp hnot
    cases hcase : S4Toggle.P (T++S) with
    | none => exact ⟨S,hcase⟩
    | some V =>
        have hn : S4Toggle.P (T++S)≠none := by simp [hcase]
        exact False.elim (hS hn)


/-- A single appended natural-number digit always realizes any failed
finite guard. This strengthens bare existential unsafe-suffix statements. -/
theorem chain_bad_one_digit (cs T : List Nat)
    (hpos : ∀ c, c∈cs → 0<c)
    (hgate : ∀ c xs, 0<c → (G c xs=none ↔ ∃n,W xs+c=2^n))
    (hbad : ¬good cs T.length T) :
    ∃ t : Nat, chain cs (T++[t])=none := by
  obtain ⟨t,ht,hall⟩ :=
    chain_bad_weight cs T.length T hpos hgate (by omega) hbad
  refine ⟨t-1,?_⟩
  have hpre : (T++[t-1]).take T.length = T.take T.length := by simp
  have hweight : W (T++[t-1]) = W T+2^T.length*t := by
    rw [W_append]
    have hsub : t-1+1=t := Nat.sub_add_cancel ht
    simpa [W,hsub]
  exact hall _ ⟨by omega,by simp,hpre.symm,hweight⟩

/-- Strong sharpness: when S4 survives on the bare stack, adding *one*
digit can cause a halt precisely at a two-or-more-digit length increase. -/
theorem s4_one_digit_halt_iff_growth (T U : List Nat)
    (hP : S4Toggle.P T = some U) :
    (∃ t : Nat, S4Toggle.P (T++[t])=none) ↔
       T.length+2≤U.length := by
  constructor
  · rintro ⟨t,ht⟩
    exact (s4_synthetic_halt_iff_growth T U hP).mp ⟨[t],ht⟩
  · intro hbig
    have hbad : ¬ good [509,290,219] T.length T := by
      intro hg
      have hshort := (s4_P_growth T U hP).mp hg
      omega
    have hpos : ∀ c, c∈([509,290,219] : List Nat) → 0<c := by
      intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with h | h | h <;> omega
    have hgate : ∀ c xs, 0<c → (G c xs=none ↔ ∃n,W xs+c=2^n) := by
      intro c xs hc
      simpa [S4Power.Pow2] using S4Octet.G_none_iff_power c xs hc
    obtain ⟨t,ht⟩ := chain_bad_one_digit [509,290,219] T hpos hgate hbad
    refine ⟨t,?_⟩
    simpa [chain,S4Toggle.P] using ht

#print axioms chain_bad_one_digit
#print axioms s4_one_digit_halt_iff_growth

#print axioms chain_survival_iff_short
#print axioms s4_survival_iff_short
#print axioms s4_synthetic_halt_iff_growth
end S4PrefixGrowth
