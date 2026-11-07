import S4AllDepthSharp
import Lean.Elab.Tactic.Omega

namespace S4PrefixExact
open S4Power S4Octet
set_option maxRecDepth 10000

/-- Executable sharp prefix guard, with exactly the all-suffix meaning
proved for `good` in the prior module. -/
def guardB : List Nat → Nat → List Nat → Bool
  | [], _, _ => true
  | c::cs, k, xs =>
      if (W xs+c)%2^k=0 then false
      else match G c xs with
           | none => false
           | some ys => guardB cs k ys

set_option maxHeartbeats 0

theorem guardB_spec (cs : List Nat) (k : Nat) (xs : List Nat) :
    guardB cs k xs = true ↔ good cs k xs := by
  induction cs generalizing xs with
  | nil => simp [guardB, good]
  | cons c cs ih =>
      by_cases hm : (W xs+c)%2^k=0
      · simp [guardB,good,hm]
      · cases hg : G c xs with
        | none => simp [guardB,good,hm,hg]
        | some ys => simp [guardB,good,hm,hg,ih]

/-- One Boolean evaluation decides an arbitrary-prefix universal
suffix-safety question for the actual source-defined S4 map. -/
theorem s4_triple_sharp_bool (xs : List Nat) :
    (∀ S : List Nat, S4Toggle.P (xs++S) ≠ none) ↔
      guardB [509,290,219] xs.length xs = true := by
  exact (s4_triple_sharp xs).trans (guardB_spec [509,290,219] xs.length xs).symm

-- This six-digit exceptional prefix was previously handled by a special
-- literal witness. The general sharp theorem now covers it uniformly.
theorem phase279_unsafe :
    guardB [509,290,219] 6 [282,967,2129,1857,9553,13781] = false := by
  simp [guardB, G, H, W]

theorem phase279_synthetic_completion :
    ∃ t : Nat, S4Toggle.P ([282,967,2129,1857,9553,13781]++[t])=none := by
  have hb : ¬ good [509,290,219] 6 [282,967,2129,1857,9553,13781] := by
    intro hgood
    have he := (guardB_spec [509,290,219] 6 [282,967,2129,1857,9553,13781]).mpr hgood
    rw [phase279_unsafe] at he
    contradiction
  have hpos : ∀ c, c∈([509,290,219] : List Nat) → 0<c := by
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with h | h | h <;> omega
  have hgate : ∀ c ys, 0<c →
      (G c ys=none ↔ ∃n, W ys+c=2^n) := by
    intro c ys hc
    simpa [S4Power.Pow2] using S4Octet.G_none_iff_power c ys hc
  obtain ⟨t, ht, hall⟩ := chain_bad_weight [509,290,219] 6
      [282,967,2129,1857,9553,13781] hpos hgate (by decide) hb
  have hpre : ([282,967,2129,1857,9553,13781]++[t-1]).take 6 =
       ([282,967,2129,1857,9553,13781] : List Nat).take 6 := by simp
  have hwt : W ([282,967,2129,1857,9553,13781]++[t-1]) =
       W [282,967,2129,1857,9553,13781]+2^6*t := by
    rw [W_append]
    have hsub : t-1+1=t := Nat.sub_add_cancel ht
    simpa [W,hsub]
  have hcoupled : coupled 6 t [282,967,2129,1857,9553,13781]
                     ([282,967,2129,1857,9553,13781]++[t-1]) :=
    ⟨by decide,by simp,hpre.symm,hwt⟩
  have hnone := hall _ hcoupled
  refine ⟨t-1,?_⟩
  simpa [chain,S4Toggle.P] using hnone

#print axioms guardB_spec
#print axioms s4_triple_sharp_bool
#print axioms phase279_unsafe
#print axioms phase279_synthetic_completion
end S4PrefixExact
