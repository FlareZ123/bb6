import Root119BShift
namespace BB6Root119
set_option linter.unusedSimpArgs false

def growHyp (t : Int → Bool) (h : Int) : Prop :=
 t (h-0) = false ∧
 t (h-1) = true ∧
 t (h-2) = true ∧
 t (h-3) = true ∧
 t (h-4) = false ∧
 t (h-5) = false ∧
 t (h-6) = false ∧
 t (h-7) = false

def gs0 (t : Int → Bool) (h : Int) : Conf := ⟨.B, h-0, t⟩

def gs1 (t : Int → Bool) (h : Int) : Conf := ⟨.C, h-1, (setBit t (h-0) true)⟩

def gs2 (t : Int → Bool) (h : Int) : Conf := ⟨.C, h-2, (setBit (setBit t (h-0) true) (h-1) false)⟩

def gs3 (t : Int → Bool) (h : Int) : Conf := ⟨.C, h-3, (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false)⟩

def gs4 (t : Int → Bool) (h : Int) : Conf := ⟨.C, h-4, (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false)⟩

def gs5 (t : Int → Bool) (h : Int) : Conf := ⟨.D, h-5, (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true)⟩

def gs6 (t : Int → Bool) (h : Int) : Conf := ⟨.E, h-6, (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false)⟩

def gs7 (t : Int → Bool) (h : Int) : Conf := ⟨.A, h-5, (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true)⟩

def gs8 (t : Int → Bool) (h : Int) : Conf := ⟨.B, h-4, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true)⟩

def gs9 (t : Int → Bool) (h : Int) : Conf := ⟨.F, h-5, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true)⟩

def gs10 (t : Int → Bool) (h : Int) : Conf := ⟨.D, h-4, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false)⟩

def gs11 (t : Int → Bool) (h : Int) : Conf := ⟨.F, h-3, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false) (h-4) true)⟩

def gs12 (t : Int → Bool) (h : Int) : Conf := ⟨.B, h-4, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false) (h-4) true) (h-3) true)⟩

def gs13 (t : Int → Bool) (h : Int) : Conf := ⟨.F, h-5, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false) (h-4) true) (h-3) true) (h-4) true)⟩

def gs14 (t : Int → Bool) (h : Int) : Conf := ⟨.B, h-6, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false) (h-4) true) (h-3) true) (h-4) true) (h-5) true)⟩

def gs15 (t : Int → Bool) (h : Int) : Conf := ⟨.F, h-7, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false) (h-4) true) (h-3) true) (h-4) true) (h-5) true) (h-6) true)⟩

def gs16 (t : Int → Bool) (h : Int) : Conf := ⟨.B, h-8, (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t (h-0) true) (h-1) false) (h-2) false) (h-3) false) (h-4) true) (h-5) false) (h-6) true) (h-5) true) (h-4) true) (h-5) false) (h-4) true) (h-3) true) (h-4) true) (h-5) true) (h-6) true) (h-7) true)⟩

theorem gstep0 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs0 t h) = some (gs1 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  simp (disch := omega) [gs0, gs1, next, setBit, hz,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep1 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs1 t h) = some (gs2 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-1 ≠ h := by omega
  simp (disch := omega) [gs1, gs2, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep2 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs2 t h) = some (gs3 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-2 ≠ h := by omega
  simp (disch := omega) [gs2, gs3, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep3 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs3 t h) = some (gs4 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-3 ≠ h := by omega
  simp (disch := omega) [gs3, gs4, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep4 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs4 t h) = some (gs5 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-4 ≠ h := by omega
  simp (disch := omega) [gs4, gs5, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep5 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs5 t h) = some (gs6 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-5 ≠ h := by omega
  simp (disch := omega) [gs5, gs6, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep6 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs6 t h) = some (gs7 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-6 ≠ h := by omega
  simp (disch := omega) [gs6, gs7, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep7 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs7 t h) = some (gs8 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-5 ≠ h := by omega
  simp (disch := omega) [gs7, gs8, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep8 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs8 t h) = some (gs9 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-4 ≠ h := by omega
  simp (disch := omega) [gs8, gs9, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep9 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs9 t h) = some (gs10 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-5 ≠ h := by omega
  simp (disch := omega) [gs9, gs10, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep10 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs10 t h) = some (gs11 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-4 ≠ h := by omega
  simp (disch := omega) [gs10, gs11, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep11 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs11 t h) = some (gs12 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-3 ≠ h := by omega
  simp (disch := omega) [gs11, gs12, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep12 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs12 t h) = some (gs13 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-4 ≠ h := by omega
  simp (disch := omega) [gs12, gs13, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep13 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs13 t h) = some (gs14 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-5 ≠ h := by omega
  simp (disch := omega) [gs13, gs14, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep14 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs14 t h) = some (gs15 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-6 ≠ h := by omega
  simp (disch := omega) [gs14, gs15, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem gstep15 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    next (gs15 t h) = some (gs16 t h) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hv
  have hz : t h = false := by simpa using h0
  have hn : h-7 ≠ h := by omega
  simp (disch := omega) [gs15, gs16, next, setBit, hz, hn,  h0,h1,h2,h3,h4,h5,h6,h7]

theorem growStage16 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
    run 16 (gs0 t h) = some (gs16 t h) := by
  calc
    run 16 (gs0 t h) = run 15 (gs1 t h) := by simp [run, gstep0 t h hv]
    _ = run 14 (gs2 t h) := by simp [run, gstep1 t h hv]
    _ = run 13 (gs3 t h) := by simp [run, gstep2 t h hv]
    _ = run 12 (gs4 t h) := by simp [run, gstep3 t h hv]
    _ = run 11 (gs5 t h) := by simp [run, gstep4 t h hv]
    _ = run 10 (gs6 t h) := by simp [run, gstep5 t h hv]
    _ = run 9 (gs7 t h) := by simp [run, gstep6 t h hv]
    _ = run 8 (gs8 t h) := by simp [run, gstep7 t h hv]
    _ = run 7 (gs9 t h) := by simp [run, gstep8 t h hv]
    _ = run 6 (gs10 t h) := by simp [run, gstep9 t h hv]
    _ = run 5 (gs11 t h) := by simp [run, gstep10 t h hv]
    _ = run 4 (gs12 t h) := by simp [run, gstep11 t h hv]
    _ = run 3 (gs13 t h) := by simp [run, gstep12 t h hv]
    _ = run 2 (gs14 t h) := by simp [run, gstep13 t h hv]
    _ = run 1 (gs15 t h) := by simp [run, gstep14 t h hv]
    _ = run 0 (gs16 t h) := by simp [run, gstep15 t h hv]
    _ = some (gs16 t h) := by rfl

#print axioms BB6Root119.gstep15
#print axioms BB6Root119.growStage16
end BB6Root119
