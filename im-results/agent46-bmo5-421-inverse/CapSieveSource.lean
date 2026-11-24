import CapRoot
import CapSieveClasses
namespace CapSieve

theorem p_eq (k : Nat) : P k=Cap.c k+4 := (Cap.c_add k).symm

theorem l_eq (k : Nat) : L k=Cap.lo k := by
  have h := l_add k
  have h' := Cap.lo_add k
  unfold P at h
  omega

theorem t_eq (k : Nat) : T k=Cap.halt k := by
  have h := t_add k
  have h' := Cap.halt_formula k
  omega

theorem arc_iff {x y : Nat} : Arc x y ↔ Cap.Edge x y := by
  constructor
  · intro h
    cases h with
    | one => exact .one
    | regular k r hr =>
      have hp := p_eq k
      rw [l_eq,show 3*r+P k+3=3*r+Cap.c k+7 by omega]
      exact .regular k r (by omega)
    | special k =>
      have hp := p_eq k
      rw [l_eq,show Cap.lo k+(P k-2)=Cap.lo k+Cap.c k+2 by omega,show 2*P k=2*Cap.c k+8 by omega]
      exact .special k
  · intro h
    cases h with
    | one => exact .one
    | regular k r hr =>
      have hp := p_eq k
      rw [←l_eq,show 3*r+Cap.c k+7=3*r+P k+3 by omega]
      exact .regular k r (by omega)
    | special k =>
      have hp := p_eq k
      rw [←l_eq,show L k+Cap.c k+2=L k+(P k-2) by omega,show 2*Cap.c k+8=2*P k by omega]
      exact .special k

theorem arc_iff_pred {x y : Nat} : Arc x y ↔ Cap.predecessor y=some x := by
  rw [arc_iff,Cap.predecessor_iff,Cap.edge_iff]

theorem back_root {i t y : Nat} (h : Back i t y) : Cap.rootOf (Cap.halt i)=Cap.rootOf y := by
  induction h with
  | zero => rw [t_eq]
  | step hb ha ih => rw [ih,Cap.root_edge (arc_iff.mp ha)]

theorem back_large {i t y : Nat} (h : Back i t y) (hi : 4*t+10≤i) : 3<y := by
  obtain ⟨w,hw,hv,hr⟩ := back_packet h hi
  have hg := word_good i w (by omega)
  have hs := packet_range hg hr (by omega)
  have hp := p_ge (i-(packetFor i w).d)
  omega

/-- A small root requires an unbroken inverse history through every guarded depth. -/
theorem small_root_survives {i : Nat} (hroot : Cap.rootOf (Cap.halt i)≤3) :
    ∀ t, 4*t+10≤i → ∃ y, Back i t y := by
  intro t hi
  induction t with
  | zero => exact ⟨T i,Back.zero⟩
  | succ t ih =>
    obtain ⟨y,hb⟩ := ih (by omega)
    have hy := back_large hb (by omega)
    have hr := back_root hb
    cases hp : Cap.predecessor y with
    | none =>
      have hh : Cap.rootOf y=y := by rw [Cap.rootOf.eq_def,hp]
      omega
    | some x => exact ⟨x,Back.step hb (arc_iff_pred.mpr hp)⟩

theorem small_root_word {i t : Nat} (hroot : Cap.rootOf (Cap.halt i)≤3) (hi : 4*t+10≤i) :
    ∃ w : List Bool, w.length=t ∧ Valid i w :=
  (back_iff_valid i t hi).mp (small_root_survives hroot t hi)

#print axioms arc_iff_pred
#print axioms back_root
#print axioms small_root_survives
#print axioms small_root_word
end CapSieve
