import MacroFARCheck
import FARBi

namespace BB6Coverage.MacroFARBridge

def project (p : PartialMachine) : MacroFAR.Table (Fin 6) := fun q a =>
  ((p (q,a)).bind id).map fun mv => (mv.write,mv.right,mv.next)

theorem step_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (c : Config) (z z' : MacroFAR.WordConfig (Fin 6))
    (hq : c.state = z.q) (hr : FAR.Represents c z.l z.r)
    (hs : MacroFAR.step (project p) z = some z') :
    ∃ c', rawStep m c = some c' ∧ c'.state = z'.q ∧ FAR.Represents c' z'.l z'.r := by
  rcases z with ⟨q,l,r⟩
  change (((p (q,r.headD false)).bind id).map (fun mv => (mv.write,mv.right,mv.next))).map (fun (w,right,q') => if right then ⟨q',w::l,r.tail⟩ else ⟨q',l.tail,l.headD false::w::r.tail⟩) = some z' at hs
  cases hp : p (q,r.headD false) with
  | none => rw [hp] at hs; contradiction
  | some v =>
    cases v with
    | none => rw [hp] at hs; contradiction
    | some mv =>
      have hstep : rawStep m c = some (applyMove c mv) := by
        unfold rawStep readSlot
        rw [FAR.rep_read hr, hq, hm _ _ hp]
        rfl
      cases hd : mv.right with
      | true =>
        have he : z' = ⟨mv.next,mv.write::l,r.tail⟩ := by
          rw [hp] at hs
          simpa [hd] using hs.symm
        subst z'
        exact ⟨_,hstep,rfl,FAR.rep_right hr mv hd⟩
      | false =>
        have he : z' = ⟨mv.next,l.tail,l.headD false::mv.write::r.tail⟩ := by
          rw [hp] at hs
          simpa [hd] using hs.symm
        subst z'
        exact ⟨_,hstep,rfl,FAR.rep_left hr mv hd⟩

theorem run_front (m : Machine) (n : Nat) (c : Config) :
    run m (n+1) c = (rawStep m c).bind (run m n) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [run,ih]
    cases h : rawStep m c <;> simp [h,run]

theorem run_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (n : Nat) (c : Config) (z z' : MacroFAR.WordConfig (Fin 6))
    (hq : c.state = z.q) (hr : FAR.Represents c z.l z.r)
    (hs : MacroFAR.run (project p) n z = some z') :
    ∃ c', run m n c = some c' ∧ c'.state = z'.q ∧ FAR.Represents c' z'.l z'.r := by
  induction n generalizing c z with
  | zero =>
    have he : z = z' := Option.some.inj hs
    subst z'
    exact ⟨c,rfl,hq,hr⟩
  | succ n ih =>
    cases ht : MacroFAR.step (project p) z with
    | none => simp [MacroFAR.run,ht] at hs
    | some y =>
      have hy : MacroFAR.run (project p) n y = some z' := by
        simpa [MacroFAR.run,ht] using hs
      obtain ⟨d,hd,hqd,hrd⟩ := step_sound p m hm c z y hq hr ht
      obtain ⟨e,he,hqe,hre⟩ := ih d y hqd hrd hy
      refine ⟨e,?_,hqe,hre⟩
      rw [run_front,hd]
      exact he

theorem never_of_live (p : PartialMachine)
    (h : ∀ n, (MacroFAR.run (project p) n ⟨0,[],[]⟩).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have hn := h n
  cases hr : MacroFAR.run (project p) n ⟨0,[],[]⟩ with
  | none => simp [hr] at hn
  | some z =>
    obtain ⟨c,hc,_,_⟩ := run_sound p m hm n blank _ z rfl FAR.rep_blank hr
    simp [hc]

theorem never {d n} (p : PartialMachine) (C : MacroFAR.Data d n)
    (trees : Fin 6 → MacroFAR.Tree (Fin 6))
    (hc : C.check (project p) trees = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_live p (C.sound _ _ hc) m hm

#print axioms never
end BB6Coverage.MacroFARBridge
