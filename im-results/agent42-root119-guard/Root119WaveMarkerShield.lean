import Root119WaveNormal

namespace BB6Root119

/-- A 1100 factor is strictly to the left of the head. -/
def noLeft1100 (c : Conf) : Prop :=
  ∀ x : Int, x + 4 ≤ c.h →
    ¬ (c.tape x = true ∧ c.tape (x+1) = true ∧
       c.tape (x+2) = false ∧ c.tape (x+3) = false)

/-- The exact endpoint of the source-certified odd F/1 wave. -/
def waveMarkerOut (n : Nat) (c : Conf) : Conf :=
  ⟨.B, c.h-1, setBit c.tape (c.h+2*(n:Int)+2) true⟩

/-- The packaged exact source-machine return, with no intermediate phase states. -/
theorem wave_marker_run (n : Nat) (c : Conf) (hv : waveValid n c) :
    run (4*n+5) c = some (waveMarkerOut n c) := by
  simpa [waveMarkerOut] using wave_explicit n c hv

/-- The wave restores the F/1 head cell to 1, erasing a temporary 1100
    ending at the old head when the preceding two cells are 11 and the
    left neighbor is 0. -/
theorem wave_marker_restores_suffix (n : Nat) (c : Conf)
    (hv : waveValid n c)
    (h3 : c.tape (c.h-3) = true)
    (h2 : c.tape (c.h-2) = true)
    (h1 : c.tape (c.h-1) = false) :
    (waveMarkerOut n c).tape (c.h-3) = true ∧
    (waveMarkerOut n c).tape (c.h-2) = true ∧
    (waveMarkerOut n c).tape (c.h-1) = false ∧
    (waveMarkerOut n c).tape c.h = true := by
  have hh : c.h ≠ c.h+2*(n:Int)+2 := by omega
  have h3' : c.h-3 ≠ c.h+2*(n:Int)+2 := by omega
  have h2' : c.h-2 ≠ c.h+2*(n:Int)+2 := by omega
  have h1' : c.h-1 ≠ c.h+2*(n:Int)+2 := by omega
  exact ⟨by simpa [waveMarkerOut, setBit, h3'] using h3,
    by simpa [waveMarkerOut, setBit, h2'] using h2,
    by simpa [waveMarkerOut, setBit, h1'] using h1,
    by simpa [waveMarkerOut, setBit, hh] using hv.2.1⟩

/-- Any 1100 factor already strictly left of the F/1 head remains absent
    strictly left of the returned B/0 head. The only cell changed by the
    exact wave normal form is strictly to the right of both heads. -/
theorem wave_marker_preserves_noLeft1100 (n : Nat) (c : Conf)
    (hv : waveValid n c) (hn : noLeft1100 c) :
    noLeft1100 (waveMarkerOut n c) := by
  intro x hx hpat
  have hxold : x+4 ≤ c.h := by
    change x+4 ≤ c.h-1 at hx
    omega
  have h0 : x ≠ c.h+2*(n:Int)+2 := by omega
  have h1 : x+1 ≠ c.h+2*(n:Int)+2 := by omega
  have h2 : x+2 ≠ c.h+2*(n:Int)+2 := by omega
  have h3 : x+3 ≠ c.h+2*(n:Int)+2 := by omega
  have hpat' : c.tape x = true ∧ c.tape (x+1) = true ∧
      c.tape (x+2) = false ∧ c.tape (x+3) = false := by
    simpa [waveMarkerOut, setBit, h0, h1, h2, h3] using hpat
  exact hn x hxold hpat'

#print axioms BB6Root119.wave_marker_run
#print axioms BB6Root119.wave_marker_restores_suffix
#print axioms BB6Root119.wave_marker_preserves_noLeft1100

end BB6Root119
