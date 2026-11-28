import PeriodicMacroTransfer
import FinitePowerRigidity

/-! Draft source-independent composition. Requires pinned Lean compile before
    being advertised as source-accepted. -/
namespace PeriodicMacro

/-- For n+2 copies of a typed macro word, the first three safe input
    heights bound the affine second difference. -/
theorem finite_power_word_slope
    (xs : List Letter) (u r : Nat → Nat) (n : Nat)
    (hw : ∀ i : Nat, i≤n+1 →
      Walk xs (u i) (r i) (u (i+1)) (r (i+1)))
    (hsafe0 : 3*u 0≤r 0)
    (hsafe1 : 3*u 1≤r 1)
    (hsafe2 : 3*u 2≤r 2)
    (hbig : 2*((r 0+2*T xs)/3)<(M xs)^n) :
    (u 0:Int)+(u 2:Int)=2*(u 1:Int) ∧
    ((M xs:Int)-1)*((u 1:Int)-(u 0:Int))=
      ((A xs*T xs):Int) := by
  have hr (i : Nat) (hi : i≤n+2) :
      r i=r 0+i*T xs := by
    induction i with
    | zero => simp
    | succ i ih =>
      have ht := (transfer (hw i (by omega))).2
      have hri := ih (by omega)
      rw [ht,hri]
      simp only [Nat.succ_mul]
      omega
  let H : Nat := (r 0+2*T xs)/3
  have hb0 : u 0≤H := by dsimp [H]; omega
  have hb1 : u 1≤H := by
    have hr1 := hr 1 (by omega)
    dsimp [H]
    rw [hr1] at hsafe1
    omega
  have hb2 : u 2≤H := by
    have hr2 := hr 2 (by omega)
    dsimp [H]
    rw [hr2] at hsafe2
    omega
  have htransfer (i : Nat) (hi : i≤n+1) :
      (M xs:Int)*(u (i+1):Int) =
        (u i:Int)+(i:Int)*((A xs*T xs):Int)+
        ((A xs*r 0+B xs):Int) := by
    have hmp := (transfer (hw i hi)).1
    have hr' := hr i (by omega)
    rw [hr'] at hmp
    have hnat : M xs*u (i+1) =
        u i+i*(A xs*T xs)+(A xs*r 0+B xs) := by
      calc
        M xs*u (i+1) =
            u i+A xs*(r 0+i*T xs)+B xs := hmp
        _ = u i+i*(A xs*T xs)+(A xs*r 0+B xs) := by ring
    exact_mod_cast hnat
  exact PeriodicPower.power_forces_affine
    (M xs) H n ((A xs*T xs):Int) ((A xs*r 0+B xs):Int)
    u hbig hb0 hb1 hb2 htransfer

#print axioms finite_power_word_slope
end PeriodicMacro
