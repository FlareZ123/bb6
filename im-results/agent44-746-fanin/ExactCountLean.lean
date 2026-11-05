import GeomBand
set_option maxHeartbeats 0
namespace CascadeAgent44

noncomputable def bandBool (q : Nat) : Bool := by
  classical
  exact decide (BandOdd q)

private theorem bandBool_iff (q : Nat) : bandBool q = true ↔ BandOdd q := by
  classical
  simp [bandBool]

noncomputable def geometricBandCount (n d : Nat) : Nat :=
  (List.range n).countP (fun t => bandBool (geometricOddQ n d t))

private theorem final_plateau_when_one (m : Nat) :
    Nat.log2 (geometricOddQ (m+1) 1 m) =
    Nat.log2 (geometricOddQ (m+1) 1 (m+1)) := by
  have hq : geometricOddQ (m+1) 1 m = 3*2^m := by
    simp [geometricOddQ]
    omega
  have hq' : geometricOddQ (m+1) 1 (m+1) = 2^(m+1) := by
    simp [geometricOddQ]
  rw [hq,hq',log2_exact_power]
  apply (Nat.log2_eq_iff (by
    have hp : 0 < 2^m := Nat.one_le_pow m 2 (by decide)
    omega)).mpr
  constructor
  · rw [Nat.pow_succ]
    have hp : 0 < 2^m := Nat.one_le_pow m 2 (by decide)
    omega
  · have hp : 2^(m+1+1)=4*2^m := by
      rw [show m+1+1=m+2 by omega]
      have he : 2^(m+2)=4*2^m := by
        rw [Nat.pow_add]
        simp [Nat.mul_comm]
      exact he
    rw [hp]
    have hp' : 0 < 2^m := Nat.one_le_pow m 2 (by decide)
    omega

private theorem geometric_prefix_count_equal (m d : Nat) (hd : d%2=1) :
    (List.range m).countP (fun t => bandBool (geometricOddQ (m+1) d t)) =
    (List.range m).countP (fun t =>
      decide (Nat.log2 (geometricOddQ (m+1) d t) =
       Nat.log2 (geometricOddQ (m+1) d (t+1)))) := by
  classical
  apply List.countP_congr
  intro t hmem
  have ht : t<m := (List.mem_range.mp hmem)
  have hb := geometric_band_iff (m+1) d t hd (by omega)
  have hneq : ¬(t+1=m+1 ∧ d=1) := by omega
  change (bandBool (geometricOddQ (m+1) d t) = true ↔
      decide (Nat.log2 (geometricOddQ (m+1) d t) =
      Nat.log2 (geometricOddQ (m+1) d (t+1))) = true)
  rw [bandBool_iff]
  simpa only [decide_eq_true_eq] using
    (show BandOdd (geometricOddQ (m+1) d t) ↔
       Nat.log2 (geometricOddQ (m+1) d t) =
       Nat.log2 (geometricOddQ (m+1) d (t+1)) from
      ⟨fun h => (hb.mp h).1,fun h => hb.mpr ⟨h,hneq⟩⟩)

/-- Exact finite count of admissible *nonterminal* odd reset inverse bands
    from a 3-adic factorization. The only correction is the last lower
    endpoint, when d=1. -/
theorem geometric_band_count_identity (n d : Nat) (hd : d%2=1) :
    geometricBandCount n d + Nat.log2 (3^n*d) +
      (if 0<n ∧ d=1 then 1 else 0) = 2*n+Nat.log2 d := by
  have hpos : 0<d := by omega
  have htelescope := geometric_log_plateau_count n d hpos
  have hcount : geometricBandCount n d +
      (if 0<n ∧ d=1 then 1 else 0) =
      sameLogCount (fun t => Nat.log2 (geometricOddQ n d t)) n := by
    cases n with
    | zero => simp [geometricBandCount,sameLogCount]
    | succ m =>
      classical
      have hpref := geometric_prefix_count_equal m d hd
      have hbandlast := geometric_band_iff (m+1) d m hd (by omega)
      have hsource : geometricBandCount (m+1) d =
        (List.range m).countP (fun t =>
            bandBool (geometricOddQ (m+1) d t)) +
          (if bandBool (geometricOddQ (m+1) d m) then 1 else 0) := by
        simp [geometricBandCount,List.range_succ,List.countP_append]
      have hplateau : sameLogCount
          (fun t => Nat.log2 (geometricOddQ (m+1) d t)) (m+1) =
        (List.range m).countP (fun t =>
          decide (Nat.log2 (geometricOddQ (m+1) d t) =
                 Nat.log2 (geometricOddQ (m+1) d (t+1)))) +
        (if decide (Nat.log2 (geometricOddQ (m+1) d m) =
                 Nat.log2 (geometricOddQ (m+1) d (m+1))) then 1 else 0) := by
        simp [sameLogCount,List.range_succ,List.countP_append]
      by_cases hD : d=1
      · subst d
        have hl : Nat.log2 (geometricOddQ (m+1) 1 m) =
            Nat.log2 (geometricOddQ (m+1) 1 (m+1)) :=
          final_plateau_when_one m
        have hb : ¬BandOdd (geometricOddQ (m+1) 1 m) := by
          intro hh
          have hx:=hbandlast.mp hh
          exact hx.2 ⟨by omega,rfl⟩
        simp [hl,hb,bandBool_iff] at hsource hplateau ⊢
        rw [hsource,hplateau]
        omega
      · have hiff : BandOdd (geometricOddQ (m+1) d m) ↔
            Nat.log2 (geometricOddQ (m+1) d m) =
            Nat.log2 (geometricOddQ (m+1) d (m+1)) := by
          simpa [hD] using hbandlast
        simp [hD] at hsource hplateau ⊢
        rw [hsource,hplateau]
        rw [hpref]
        by_cases hdec : BandOdd (geometricOddQ (m+1) d m)
        · have heq := hiff.mp hdec
          simp [bandBool_iff,hdec,heq]
        · have heq : ¬ (Nat.log2 (geometricOddQ (m+1) d m) =
                Nat.log2 (geometricOddQ (m+1) d (m+1))) := by
            intro hh
            exact hdec (hiff.mpr hh)
          simp [bandBool_iff,hdec,heq]
  omega

#print axioms geometric_band_count_identity
end CascadeAgent44
