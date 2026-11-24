import NearPowerTree
import Agent49InverseWindowSource

/-! Accepted compressed certificates exclude their represented targets from
every blank-origin visit using the original-source inverse envelope.
No assumption of completeness of the certificate generator is required. -/
namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth BB6.Agent49InverseWindowSource BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

private def fullDrain (A b z x y : Nat) : Prop :=
  Window A b z x y ∧ (2*inverseBudget y≤x → y=z+image b ∧ (x:Int)=(A:Int)+drift b)

private theorem fullDrain_sound (A b z x y : Nat) (h : drainB A b z=some (.D x y)) : fullDrain A b z x y := by
  refine ⟨source_drain_window A b z x y h,?_⟩
  intro hx
  obtain ⟨n0,n1,n2,ht⟩ := source_large_first_trace A b z x y h hx
  exact ⟨trace_image ht,trace_drift ht⟩

/-- The whole set of large even-first parents is contained in two sectors. -/
theorem large_parent_sector {a d x y : Nat} (ha : a%2=0) (hx : 2*inverseBudget y≤x) (hy : 14<y)
    (h : highLevelNext (.D a d)=some (.D x y)) :
    ∃ q : Sector, ∃ A b : Nat, y%2=targetParity q ∧ b%2=bp q ∧ d%2=dp q ∧
      y=z q+image b ∧ (x:Int)=(A:Int)+drift b ∧ affine q A b a d := by
  have he := parent_envelope_complete fullDrain fullDrain_sound a d x y h
  unfold ParentEnvelope at he
  rcases he with haxis|hLO|hLE|hdiag|hRO|hRE
  · rcases haxis.2 with h|h <;> omega
  · obtain ⟨A,b,hd,_,haa,hb,hP⟩ := hLO
    have hh := hP.2 hx
    have hip := image_parity b
    exact ⟨.LO,A,b,by simp [targetParity]; omega,by simp [bp]; omega,hd,hh.1,hh.2,haa,hb⟩
  · obtain ⟨A,b,hd,_,haa,hb,hP⟩ := hLE
    have hh := hP.2 hx
    have hip := image_parity b
    exact ⟨.LE,A,b,by simp [targetParity]; omega,by simp [bp]; omega,hd,hh.1,hh.2,haa,hb⟩
  · have hw := hdiag.2.2.1
    unfold Window at hw
    have hp : 0 < inverseBudget y := by unfold inverseBudget; omega
    omega
  · obtain ⟨A,b,_,hd,haa,hb,hP⟩ := hRO
    have hh := hP.2 hx
    have hip := image_parity b
    exact ⟨.RO,A,b,by simp [targetParity]; omega,by simp [bp]; omega,hd,hh.1,hh.2,haa,hb⟩
  · obtain ⟨A,b,_,hd,haa,hb,hP⟩ := hRE
    have hh := hP.2 hx
    have hip := image_parity b
    exact ⟨.RE,A,b,by simp [targetParity]; omega,by simp [bp]; omega,hd,hh.1,hh.2,haa,hb⟩

/-- A sector check is either impossible for a genuine parent or produces an
exact representation of that parent and an accepted child certificate. -/
theorem sectorOK_parent {s : NearState} {x y A b a d : Nat} {q : Sector} {w : Int} {c : Cert}
    (hr : Represents s x y) (hk : 0<s.k) (hD : 0<s.D) (ha : a%2=0) (hd : d%2=dp q)
    (hb : b%2=bp q) (hi : y=z q+image b) (hj : (x:Int)=(A:Int)+drift b)
    (haf : affine q A b a d)
    (h : sectorOK s q w (check (restore s q w) c)=true) :
    Represents (restore s q w) a d ∧ check (restore s q w) c=true := by
  have hy := hr.2
  have hk' : s.k-1+1=s.k := by omega
  rw [←hk'] at hy
  simp only [sectorOK,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with hg|⟨hh,hp⟩
  · exact False.elim (gapOK_sound hy hg b hb hi)
  · obtain ⟨b',hrep,_,_,hu⟩ := hitOK_sound hy hh
    have hbe := hu b hi
    subst b'
    have hrest := restore_sound hr hk hD hrep hj haf
    rcases hp with hp|hc
    · exact False.elim (rejectParity_sound hrest ha hd hp)
    · exact ⟨hrest,hc⟩

/-- Accepted certificates exclude all genuine blank-origin indices, not
merely the finite inverse depths explicitly represented in the certificate. -/
theorem check_excludes (c : Cert) : ∀ (s : NearState) (x y : Nat), Represents s x y → check s c=true →
    ∀ i : Nat, run i≠some (.D x y) := by
  induction c with
  | stop => intro s x y hr h; simp [check] at h
  | fork wl wr l r ihl ihr =>
    intro s x y hr h i hrun
    simp only [check,Bool.and_eq_true] at h
    have hg := guarded_sound hr h.1.1
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
          · subst q
            obtain ⟨hrep,hc⟩ := sectorOK_parent hr hg.1 hg.2.2.1 ha hdp hbp hi hj haf h.1.2
            exact ihl _ a d hrep hc i hh
          · subst q
            obtain ⟨hrep,hc⟩ := sectorOK_parent hr hg.1 hg.2.2.1 ha hdp hbp hi hj haf h.2
            exact ihr _ a d hrep hc i hh

#print axioms large_parent_sector
#print axioms sectorOK_parent
#print axioms check_excludes
end BB6.Agent41NearPower
