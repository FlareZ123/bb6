import GeomLog
set_option maxHeartbeats 0
namespace CascadeAgent44

/-- The unique non-band 2/3 plateau is the last step, if its odd
    terminal coefficient is exactly one. -/
theorem geometric_band_iff (n d t : Nat) (hd : d%2=1) (ht : t<n) :
    BandOdd (geometricOddQ n d t) ↔
      Nat.log2 (geometricOddQ n d t) = Nat.log2 (geometricOddQ n d (t+1)) ∧
      ¬(t+1=n ∧ d=1) := by
  have hr : 0 < geometricOddR n d t :=
    pos_geometricOddR n d t (by omega)
  obtain ⟨hqt,hqt1⟩ := geometricOddQ_step n d t ht
  rw [hqt,hqt1]
  rw [bandOdd_log_power_iff _ hr]
  constructor
  · rintro ⟨hlog,hnot⟩
    exact ⟨hlog, fun hex => hnot ((geometric_odd_r_power_iff n d t hd ht).mpr hex)⟩
  · rintro ⟨hlog,hnot⟩
    exact ⟨hlog, fun hex => hnot ((geometric_odd_r_power_iff n d t hd ht).mp hex)⟩

#print axioms geometric_band_iff
end CascadeAgent44
