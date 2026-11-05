import Root119BShield
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace BB6Root119

/-- B/0 with 111 immediately to the left, followed by five zeros. -/
def expansionValid (c : Conf) : Prop :=
  c.q = .B ∧ c.tape c.h = false ∧
  c.tape (c.h-1) = true ∧ c.tape (c.h-2) = true ∧
  c.tape (c.h-3) = true ∧ c.tape (c.h-4) = false ∧
  c.tape (c.h-5) = false ∧ c.tape (c.h-6) = false ∧
  c.tape (c.h-7) = false ∧ c.tape (c.h-8) = false

def expansionTape (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (setBit (setBit (setBit (setBit (setBit (setBit t
    (h-7) true) (h-6) true) (h-5) true) (h-4) true)
    (h-3) true) (h-2) false) (h-1) false) h true

def expanded (c : Conf) : Conf :=
  ⟨.B, c.h-8, expansionTape c.tape c.h⟩

/-- Exactly 16 original raw transitions, on arbitrary exterior tapes. -/
theorem sixteen_step (c : Conf) (hv : expansionValid c) :
    run 16 c = some (expanded c) := by
  rcases c with ⟨q,h,t⟩
  obtain ⟨hq,h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := hv
  cases q <;> try contradiction
  change t h = false at h0
  change t (h-1) = true at h1
  change t (h-2) = true at h2
  change t (h-3) = true at h3
  change t (h-4) = false at h4
  change t (h-5) = false at h5
  change t (h-6) = false at h6
  change t (h-7) = false at h7
  change t (h-8) = false at h8
  let t0 := t
  let t1 := setBit t0 h true
  let t2 := setBit t1 (h-1) false
  let t3 := setBit t2 (h-2) false
  let t4 := setBit t3 (h-3) false
  let t5 := setBit t4 (h-4) true
  let t6 := setBit t5 (h-5) false
  let t7 := setBit t6 (h-6) true
  let t8 := setBit t7 (h-5) true
  let t9 := setBit t8 (h-4) true
  let t10 := setBit t9 (h-5) false
  let t11 := setBit t10 (h-4) true
  let t12 := setBit t11 (h-3) true
  let t13 := setBit t12 (h-4) true
  let t14 := setBit t13 (h-5) true
  let t15 := setBit t14 (h-6) true
  let t16 := setBit t15 (h-7) true
  let c0 : Conf := ⟨.B, h, t0⟩
  let c1 : Conf := ⟨.C, (h-1), t1⟩
  let c2 : Conf := ⟨.C, (h-2), t2⟩
  let c3 : Conf := ⟨.C, (h-3), t3⟩
  let c4 : Conf := ⟨.C, (h-4), t4⟩
  let c5 : Conf := ⟨.D, (h-5), t5⟩
  let c6 : Conf := ⟨.E, (h-6), t6⟩
  let c7 : Conf := ⟨.A, (h-5), t7⟩
  let c8 : Conf := ⟨.B, (h-4), t8⟩
  let c9 : Conf := ⟨.F, (h-5), t9⟩
  let c10 : Conf := ⟨.D, (h-4), t10⟩
  let c11 : Conf := ⟨.F, (h-3), t11⟩
  let c12 : Conf := ⟨.B, (h-4), t12⟩
  let c13 : Conf := ⟨.F, (h-5), t13⟩
  let c14 : Conf := ⟨.B, (h-6), t14⟩
  let c15 : Conf := ⟨.F, (h-7), t15⟩
  let c16 : Conf := ⟨.B, (h-8), t16⟩
  have s0 : next c0 = some c1 := by
    simp [c0,c1,next, t0,t1,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8]
  have s1 : next c1 = some c2 := by
    simp [c1,c2,next, t0,t1,t2,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-1 ≠ h by omega]
  have s2 : next c2 = some c3 := by
    simp [c2,c3,next, t0,t1,t2,t3,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-2 ≠ h-1 by omega, show h-2 ≠ h by omega]
  have s3 : next c3 = some c4 := by
    simp [c3,c4,next, t0,t1,t2,t3,t4,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-3 ≠ h-2 by omega, show h-3 ≠ h-1 by omega, show h-3 ≠ h by omega]
  have s4 : next c4 = some c5 := by
    simp [c4,c5,next, t0,t1,t2,t3,t4,t5,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-4 ≠ h-3 by omega, show h-4 ≠ h-2 by omega, show h-4 ≠ h-1 by omega, show h-4 ≠ h by omega]
  have s5 : next c5 = some c6 := by
    simp [c5,c6,next, t0,t1,t2,t3,t4,t5,t6,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-5 ≠ h-4 by omega, show h-5 ≠ h-3 by omega, show h-5 ≠ h-2 by omega, show h-5 ≠ h-1 by omega, show h-5 ≠ h by omega]
  have s6 : next c6 = some c7 := by
    simp [c6,c7,next, t0,t1,t2,t3,t4,t5,t6,t7,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-6 ≠ h-5 by omega, show h-6 ≠ h-4 by omega, show h-6 ≠ h-3 by omega, show h-6 ≠ h-2 by omega, show h-6 ≠ h-1 by omega, show h-6 ≠ h by omega]
  have s7 : next c7 = some c8 := by
    simp [c7,c8,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-5 ≠ h-6 by omega, show h-5 ≠ h-4 by omega, show h-5 ≠ h-3 by omega, show h-5 ≠ h-2 by omega, show h-5 ≠ h-1 by omega, show h-5 ≠ h by omega]
  have s8 : next c8 = some c9 := by
    simp [c8,c9,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-4 ≠ h-6 by omega, show h-4 ≠ h-5 by omega, show h-4 ≠ h-3 by omega, show h-4 ≠ h-2 by omega, show h-4 ≠ h-1 by omega, show h-4 ≠ h by omega]
  have s9 : next c9 = some c10 := by
    simp [c9,c10,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-5 ≠ h-6 by omega, show h-5 ≠ h-4 by omega, show h-5 ≠ h-3 by omega, show h-5 ≠ h-2 by omega, show h-5 ≠ h-1 by omega, show h-5 ≠ h by omega]
  have s10 : next c10 = some c11 := by
    simp [c10,c11,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-4 ≠ h-6 by omega, show h-4 ≠ h-5 by omega, show h-4 ≠ h-3 by omega, show h-4 ≠ h-2 by omega, show h-4 ≠ h-1 by omega, show h-4 ≠ h by omega]
  have s11 : next c11 = some c12 := by
    simp [c11,c12,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-3 ≠ h-6 by omega, show h-3 ≠ h-5 by omega, show h-3 ≠ h-4 by omega, show h-3 ≠ h-2 by omega, show h-3 ≠ h-1 by omega, show h-3 ≠ h by omega]
  have s12 : next c12 = some c13 := by
    simp [c12,c13,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-4 ≠ h-6 by omega, show h-4 ≠ h-5 by omega, show h-4 ≠ h-3 by omega, show h-4 ≠ h-2 by omega, show h-4 ≠ h-1 by omega, show h-4 ≠ h by omega]
  have s13 : next c13 = some c14 := by
    simp [c13,c14,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-5 ≠ h-6 by omega, show h-5 ≠ h-4 by omega, show h-5 ≠ h-3 by omega, show h-5 ≠ h-2 by omega, show h-5 ≠ h-1 by omega, show h-5 ≠ h by omega]
  have s14 : next c14 = some c15 := by
    simp [c14,c15,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-6 ≠ h-5 by omega, show h-6 ≠ h-4 by omega, show h-6 ≠ h-3 by omega, show h-6 ≠ h-2 by omega, show h-6 ≠ h-1 by omega, show h-6 ≠ h by omega]
  have s15 : next c15 = some c16 := by
    simp [c15,c16,next, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,setBit,h0,h1,h2,h3,h4,h5,h6,h7,h8, show h-7 ≠ h-6 by omega, show h-7 ≠ h-5 by omega, show h-7 ≠ h-4 by omega, show h-7 ≠ h-3 by omega, show h-7 ≠ h-2 by omega, show h-7 ≠ h-1 by omega, show h-7 ≠ h by omega]
  have hr : run 16 c0 = some c16 := by
    calc
      run 16 c0 = run 15 c1 := by
        change (next c0).bind (run 15) = run 15 c1
        rw [s0]
        rfl
      _ = run 14 c2 := by
        change (next c1).bind (run 14) = run 14 c2
        rw [s1]
        rfl
      _ = run 13 c3 := by
        change (next c2).bind (run 13) = run 13 c3
        rw [s2]
        rfl
      _ = run 12 c4 := by
        change (next c3).bind (run 12) = run 12 c4
        rw [s3]
        rfl
      _ = run 11 c5 := by
        change (next c4).bind (run 11) = run 11 c5
        rw [s4]
        rfl
      _ = run 10 c6 := by
        change (next c5).bind (run 10) = run 10 c6
        rw [s5]
        rfl
      _ = run 9 c7 := by
        change (next c6).bind (run 9) = run 9 c7
        rw [s6]
        rfl
      _ = run 8 c8 := by
        change (next c7).bind (run 8) = run 8 c8
        rw [s7]
        rfl
      _ = run 7 c9 := by
        change (next c8).bind (run 7) = run 7 c9
        rw [s8]
        rfl
      _ = run 6 c10 := by
        change (next c9).bind (run 6) = run 6 c10
        rw [s9]
        rfl
      _ = run 5 c11 := by
        change (next c10).bind (run 5) = run 5 c11
        rw [s10]
        rfl
      _ = run 4 c12 := by
        change (next c11).bind (run 4) = run 4 c12
        rw [s11]
        rfl
      _ = run 3 c13 := by
        change (next c12).bind (run 3) = run 3 c13
        rw [s12]
        rfl
      _ = run 2 c14 := by
        change (next c13).bind (run 2) = run 2 c14
        rw [s13]
        rfl
      _ = run 1 c15 := by
        change (next c14).bind (run 1) = run 1 c15
        rw [s14]
        rfl
      _ = some c16 := by
        change (next c15).bind (run 0) = some c16
        rw [s15]
        rfl
  have hteq : t16 = expansionTape t h := by
    funext x
    simp only [expansionTape, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,setBit]
    by_cases e0 : x=h <;>
      by_cases e1 : x=h-1 <;>
        by_cases e2 : x=h-2 <;>
          by_cases e3 : x=h-3 <;>
            by_cases e4 : x=h-4 <;>
              by_cases e5 : x=h-5 <;>
                by_cases e6 : x=h-6 <;>
                  by_cases e7 : x=h-7 <;>
                    simp_all <;> omega
  have hconf : c16 = expanded c0 := by
    change (⟨.B,h-8,t16⟩ : Conf) = ⟨.B,h-8,expansionTape t h⟩
    rw [hteq]
  change run 16 c0 = some (expanded c0)
  simpa only [hconf] using hr

/-- Writes are confined to the right of the new B head. -/
theorem expansion_preserves_left (t : Int → Bool) (h x : Int)
    (hx : x < h-8) : expansionTape t h x = t x := by
  have h7 : x ≠ h-7 := by omega
  have h6 : x ≠ h-6 := by omega
  have h5 : x ≠ h-5 := by omega
  have h4 : x ≠ h-4 := by omega
  have h3 : x ≠ h-3 := by omega
  have h2 : x ≠ h-2 := by omega
  have h1 : x ≠ h-1 := by omega
  have h0 : x ≠ h := by omega
  simp [expansionTape, setBit, h0,h1,h2,h3,h4,h5,h6,h7]

/-- Uniform factor shield through the 16-step B return. -/
theorem expanded_preserves_noLeft4 (p q r : Bool) (c : Conf)
    (hv : expansionValid c) (hs : NoLeft4 p q r c) :
    NoLeft4 p q r (expanded c) := by
  rcases c with ⟨state,h,t⟩
  intro x hx hw
  change x+3 < h-8 at hx
  change expansionTape t h x = p ∧ expansionTape t h (x+1) = q ∧
    expansionTape t h (x+2) = r ∧ expansionTape t h (x+3) = false at hw
  change ∀ x : Int, x+3 < h → ¬(t x=p ∧ t (x+1)=q ∧ t (x+2)=r ∧ t (x+3)=false) at hs
  apply hs x (by omega)
  constructor
  · rw [expansion_preserves_left t h x (by omega)] at hw
    exact hw.1
  constructor
  · rw [expansion_preserves_left t h (x+1) (by omega)] at hw
    exact hw.2.1
  constructor
  · rw [expansion_preserves_left t h (x+2) (by omega)] at hw
    exact hw.2.2.1
  · rw [expansion_preserves_left t h (x+3) (by omega)] at hw
    exact hw.2.2.2

theorem reached_expansion_preserves_noLeft4 (p q r : Bool) (c : Conf)
    (hc : Reach c) (hv : expansionValid c) (hs : NoLeft4 p q r c) :
    Reach (expanded c) ∧ NoLeft4 p q r (expanded c) := by
  exact ⟨reachable_of_run 16 c (expanded c) hc (sixteen_step c hv),
    expanded_preserves_noLeft4 p q r c hv hs⟩

#print axioms BB6Root119.reached_expansion_preserves_noLeft4
#print axioms BB6Root119.sixteen_step
#print axioms BB6Root119.expanded_preserves_noLeft4
end BB6Root119
