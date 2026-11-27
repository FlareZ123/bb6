import BB429ResonanceTail

namespace BB429.CoarseExit

/-- Convert transformed low-order errors at an exact doubled-scale resonance
    back to the physical low-side deviation.  The leading 16^m terms cancel
    completely in the deviation, while the rotated cycle invariant keeps only
    the V-error q. -/
theorem resonance_error_physical
    (u w X : Nat) (x q : Int)
    (hU : Uc (u,w)=144*(X:Int)+x)
    (hV : Vc (u,w)=216*(X:Int)+3*q)
    (hpos : 48≤-6*x+12*q+12) :
    ∃ d : Nat,
      w=u+12+d ∧
      (3:Int)*(4*(d:Int)+16)=-6*x+12*q+12 ∧
      (3:Int)*((u:Int)-(d:Int)-2)+(4*(d:Int)+16)
        =72*(X:Int)+q-2 := by
  have hid :
      -6*x+12*q+12 =
        12*((w:Int)-(u:Int)-12)+48 := by
    simp only [Uc,Vc] at hU hV
    grind +ring
  have hwu : u+12≤w := by
    rw [hid] at hpos
    push_cast at hpos
    omega
  let d := w-u-12
  have hd : w=u+12+d := by
    dsimp [d]
    omega
  refine ⟨d,hd,?_,?_⟩
  · rw [hid]
    push_cast [hd]
    ring
  · simp only [Vc] at hV
    push_cast [hd] at hV ⊢
    grind +ring

/-- At any odd physical state in phase false, once its low-side deviation d
    is small enough that u-d is a natural subtraction, the rotation residue
    is forced: u-d = 1 (mod 4). -/
theorem false_phase_rotation_mod
    (u w d : Nat)
    (hodd : w%2=1) (hph : phaseOf (u,w)=false)
    (hd : w=u+12+d) (hdu : d≤u) :
    (u-d)%4=1 := by
  unfold phaseOf at hph
  have hr : (2*u+w)%4≠1 := by
    simpa using hph
  have hro : (2*u+w)%2=1 := by omega
  have hr3 : (2*u+w)%4=3 := by
    have hb := Nat.mod_lt (2*u+w) (by decide : 0<4)
    omega
  omega

#print axioms resonance_error_physical
#print axioms false_phase_rotation_mod

end BB429.CoarseExit
