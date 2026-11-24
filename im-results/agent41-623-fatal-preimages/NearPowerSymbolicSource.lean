import NearPowerSymbolicTree
import NearPowerTreeSource

namespace BB6.Agent41NearPower
open BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- A finite symbolic certificate excludes an entire infinite near-power
family at every genuine original-machine blank-root return index. -/
theorem symCheck_excludes (c : SymCert) : ∀ (s : SymState) (n x y : Nat),
    Represents (s.atN n) x y → symCheck s c=true → ∀ i : Nat, run i≠some (.D x y) := by
  induction c with
  | stop => intro s n x y hr h; simp [symCheck] at h
  | fork wl wr l r ihl ihr =>
    intro s n x y hr h i hrun
    simp only [symCheck,Bool.and_eq_true] at h
    have hg := symGuard_sound h.1.1.1 hr
    have hs := symSectors_sound hr h.1.1.2
    cases i with
    | zero =>
      simp only [run,Option.some.injEq,HighLevelState.D.injEq] at hrun
      omega
    | succ i =>
      rw [run] at hrun
      cases hh : run i with
      | none => simp [hh] at hrun
      | some st =>
        cases st with
        | D a d =>
          simp only [hh,Option.bind_some] at hrun
          have ha := run_preserves_even i a d hh
          obtain ⟨q,A,b,hyp,hbp,hdp,hi,hj,haf⟩ := large_parent_sector ha hg.2.2.2.1 hg.2.2.2.2 hrun
          rcases target_sector hr q hyp with hq|hq
          · rw [hs.1] at hq; subst q
            obtain ⟨t,hrep,hc⟩ := symBranch_parent hr hg.1 hg.2.2.1 ha hdp hbp hi hj haf h.1.2
            exact ihl t n a d hrep hc i hh
          · rw [hs.2] at hq; subst q
            obtain ⟨t,hrep,hc⟩ := symBranch_parent hr hg.1 hg.2.2.1 ha hdp hbp hi hj haf h.2
            exact ihr t n a d hrep hc i hh

#print axioms symCheck_excludes
end BB6.Agent41NearPower
