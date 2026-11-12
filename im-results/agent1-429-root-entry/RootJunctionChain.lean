import RootToJunc
import Low43RootPhysical
import W4HeadMax
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import JuncCanonical
import High3Ladder
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429RootJunctionChain

open BB6Coverage BB429RootEntry BB429RootToJunc
open BB429PhysicalFrontier BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncCanonical BB429High3Ladder
open BB429W4HeadMax BB429W4HeadPrefix
open BB429Low43RootPhysical

private theorem zipper_runWithMax_prefix_exists (n t : Nat) (z : Zipper)
    (q : Zipper × Int × Int)
    (hfull : runWithMax n z = some q) (ht : t≤n) :
    ∃ p : Zipper × Int × Int, runWithMax t z = some p := by
  have htime : t+(n-t)=n := by omega
  have hfull' : runWithMax (t+(n-t)) z = some q := by
    simpa [htime] using hfull
  cases hp : runWithMax t z with
  | none =>
      rw [runWithMax_add,hp] at hfull'
      simp at hfull'
  | some p => exact ⟨p,hp⟩

/-- Lift a source zipper head-maximum certificate to all literal raw
    #429 prefixes while retaining the exact tape representation. -/
theorem physical_source_max_prefix_bound
    (n t : Nat) (z : Zipper) (c : Config)
    (hrep : Represents z c) (q : Zipper × Int × Int)
    (hfull : runWithMax n z = some q) (ht : t≤n) :
    ∃ d : Config,
      run target429 t c = some d ∧ d.head ≤ c.head+q.2.2 := by
  obtain ⟨p,hp⟩ := zipper_runWithMax_prefix_exists n t z q hfull ht
  have htime : t+(n-t)=n := by omega
  have hfull' : runWithMax (t+(n-t)) z = some q := by
    simpa [htime] using hfull
  have hprefixMax := runWithMax_prefix_le t (n-t) z p hp q hfull'
  have hproj := runWithMax_toDelta t z
  rw [hp] at hproj
  simp at hproj
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep t z c hrep p.1 p.2.1 hproj
  exact ⟨d,hrun,by omega⟩

/-- The exact source-zipper monitor for the complete high-zero/low-J
    continuation from J(0,12) to J(21,11). This is a finite kernel
    computation over the original #429 transition table. -/
theorem root_junc0_to_junc21_max :
    runWithMax 1463 (junc 0 0 12) =
      some (junc 21 0 11, 15, 29) := by
  decide

/-- Full-tape physical lift of the J(0,12) -> J(21,11) source monitor.
    The input is the canonical J(0,12) tape with head at -3. -/
theorem root_junc0_to_junc21_physical :
    ∃ d : Config,
      run target429 1463 (translatedJ 0 12 (-3)) = some d ∧
      Represents (junc 21 0 11) d ∧
      d.head = 12 ∧
      (∀ t : Nat, t≤1463 →
        ∃ e : Config,
          run target429 t (translatedJ 0 12 (-3)) = some e ∧
          e.head≤26) := by
  let c0 : Config := translatedJ 0 12 (-3)
  have hrep : Represents (junc 0 0 12) c0 := by
    simpa [c0] using canonical_junc_rep 0 12 (-3)
  have hmax :
      runWithMax 1463 (junc 0 0 12) =
        some (junc 21 0 11, 15, 29) := root_junc0_to_junc21_max
  have hdelta :
      runWithDelta 1463 (junc 0 0 12) =
        some (junc 21 0 11,15) := by
    simpa [hmax] using runWithMax_toDelta 1463 (junc 0 0 12)
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 1463 (junc 0 0 12) c0 hrep
      (junc 21 0 11) 15 hdelta
  have hprefix :
      ∀ t : Nat, t≤1463 →
        ∃ e : Config,
          run target429 t c0 = some e ∧ e.head≤26 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 1463 t (junc 0 0 12) c0 hrep
        (junc 21 0 11,15,29) hmax ht
    have hc0 : c0.head = -3 := by rfl
    exact ⟨e,he,by rw [hc0] at hh; omega⟩
  have hc0 : c0.head = -3 := by rfl
  exact ⟨d,hrun,hrepD,by rw [hhead,hc0]; norm_num,hprefix⟩

/-- Every prefix of a successful raw monitored run has its own successful
    head-maximum monitor, with a maximum no larger than the full run's. -/
private theorem root_runWithHeadMax_prefix_monitor (m : Machine)
    (n t : Nat) (c d : Config) (h : Int)
    (hfull : runWithHeadMax m n c = some (d,h)) (ht : t≤n) :
    ∃ e h', runWithHeadMax m t c = some (e,h') ∧ h'≤h := by
  have htime : t+(n-t)=n := by omega
  have hcomp :
      runWithHeadMax m n c =
        (runWithHeadMax m t c).bind (fun (p,hp) =>
          (runWithHeadMax m (n-t) p).map (fun (q,hq) => (q,max hp hq))) := by
    simpa [htime] using runWithHeadMax_add m t (n-t) c
  rw [hcomp] at hfull
  cases hp : runWithHeadMax m t c with
  | none => simp [hp] at hfull
  | some p =>
      cases hq : runWithHeadMax m (n-t) p.1 with
      | none => simp [hp,hq] at hfull
      | some q =>
          have heq : (q.1,max p.2 q.2) = (d,h) := by
            simpa [hp,hq] using hfull
          have hmax : max p.2 q.2 = h := congrArg Prod.snd heq
          exact ⟨p.1,p.2,hp,by rw [← hmax]; exact Int.le_max_left _ _⟩

/-- Turn the prefix-monitor lemma into an ordinary raw-run head bound. -/
private theorem root_runWithHeadMax_prefix_raw (m : Machine)
    (n t : Nat) (c d : Config) (h : Int)
    (hfull : runWithHeadMax m n c = some (d,h)) (ht : t≤n) :
    ∃ e : Config, run m t c = some e ∧ e.head≤h := by
  obtain ⟨e,h',hmon,hle⟩ :=
    root_runWithHeadMax_prefix_monitor m n t c d h hfull ht
  have hrun := runWithHeadMax_projects m t c e h' hmon
  have hbound := runWithHeadMax_head_bound m t c e h' hmon
  exact ⟨e,hrun,by omega⟩

/-- A successful raw run always has a successful head-maximum monitor. -/
private theorem root_runWithHeadMax_exists_of_run (m : Machine) :
    ∀ (n : Nat) (c d : Config),
      run m n c = some d →
      ∃ h : Int, runWithHeadMax m n c = some (d,h) := by
  intro n
  induction n with
  | zero =>
      intro c d hrun
      have hd : d=c := by
        have hh : some c = some d := by simpa [run] using hrun
        exact (Option.some.inj hh).symm
      subst d
      exact ⟨c.head,by simp [runWithHeadMax]⟩
  | succ n ih =>
      intro c d hrun
      simp only [run] at hrun
      cases hp : run m n c with
      | none => simp [hp] at hrun
      | some p =>
          have hstep : rawStep m p = some d := by
            simpa [hp] using hrun
          obtain ⟨hprev,hmon⟩ := ih c p hp
          refine ⟨max hprev d.head, ?_⟩
          simp [runWithHeadMax,hmon,hstep]

/-- If every raw prefix head is bounded by F, the monitor's maximum is
    bounded by F as well. -/
private theorem root_runWithHeadMax_bound_of_prefix (m : Machine) :
    ∀ (n : Nat) (c d : Config) (h F : Int),
      runWithHeadMax m n c = some (d,h) →
      (∀ t : Nat, t≤n →
        ∃ e : Config, run m t c = some e ∧ e.head≤F) →
      h≤F := by
  intro n
  induction n with
  | zero =>
      intro c d h F hmon hprefix
      obtain ⟨e,he,hb⟩ := hprefix 0 (by omega)
      have heq : e=c := by
        have hh : some c = some e := by simpa [run] using he
        exact Option.some.inj hh
      subst e
      simp only [runWithHeadMax,Option.some.injEq,Prod.mk.injEq] at hmon
      rcases hmon with ⟨rfl,rfl⟩
      exact hb
  | succ n ih =>
      intro c d h F hmon hprefix
      simp only [runWithHeadMax] at hmon
      cases hp : runWithHeadMax m n c with
      | none => simp [hp] at hmon
      | some p =>
          rcases p with ⟨p,hprev⟩
          cases hs : rawStep m p with
          | none => simp [hp,hs] at hmon
          | some q =>
              have hpair : (q,max hprev q.head) = (d,h) := by
                simpa [hp,hs] using hmon
              have hprevPrefix :
                  ∀ t : Nat, t≤n →
                    ∃ e : Config, run m t c = some e ∧ e.head≤F := by
                intro t ht
                exact hprefix t (by omega)
              have hprevBound : hprev≤F :=
                ih c p hprev F (by simpa [hp] using hp) hprevPrefix
              have hrunFinal : run m (n+1) c = some q := by
                have hmon' :
                    runWithHeadMax m (n+1) c =
                      some (q,max hprev q.head) := by
                  simp [runWithHeadMax,hp,hs]
                exact runWithHeadMax_projects m (n+1) c q
                  (max hprev q.head) hmon'
              obtain ⟨e,he,hb⟩ := hprefix (n+1) (by omega)
              have heq : e=q := Option.some.inj (he.symm.trans hrunFinal)
              subst e
              have hmax : max hprev q.head = h := congrArg Prod.snd hpair
              rw [← hmax]
              exact max_le hprevBound hb

/-- The authentic blank root reaches J(21,11) after 1608 moves. Its
    cumulative head maximum is exactly the rightmost marked cell 26. -/
theorem root_after_1608_junc21_frontier :
    ∃ d : Config,
      run target429 1608 blank = some d ∧
      Represents (junc 21 0 11) d ∧
      d.head = 12 ∧
      d.tape 26 = true ∧
      (∀ x : Int, 26 < x → d.tape x = false) ∧
      (∀ t : Nat, t≤1608 →
        ∃ e : Config,
          run target429 t blank = some e ∧ e.head≤26) ∧
      runWithHeadMax target429 1608 blank = some (d,26) := by
  rcases root_after_145_junc_frontier with
    ⟨h145mon,h145rep,h145head,h145mark,h145blank⟩
  obtain ⟨c21,hsegment,hrep21,hhead21,hsegmentPrefix⟩ :=
    root_junc0_to_junc21_physical
  have h145run :
      run target429 145 blank = some (translatedJ 0 12 (-3)) :=
    runWithHeadMax_projects target429 145 blank
      (translatedJ 0 12 (-3)) 12 h145mon
  have htotal0 :
      run target429 (145+1463) blank = some c21 := by
    rw [run_add',h145run]
    exact hsegment
  have htime : 145+1463=1608 := by omega
  have htotal : run target429 1608 blank = some c21 := by
    simpa [htime] using htotal0
  have hhead : c21.head=12 := hhead21
  have hprefix :
      ∀ t : Nat, t≤1608 →
        ∃ e : Config,
          run target429 t blank = some e ∧ e.head≤26 := by
    intro t ht
    by_cases hle : t≤145
    · obtain ⟨e,he,hb⟩ :=
        root_runWithHeadMax_prefix_raw target429 145 t blank
          (translatedJ 0 12 (-3)) 12 h145mon hle
      exact ⟨e,he,by omega⟩
    · let s : Nat := t-145
      have hs : s≤1463 := by dsimp [s]; omega
      obtain ⟨e,he,hb⟩ := hsegmentPrefix s hs
      have htime2 : t=145+s := by dsimp [s]; omega
      have hraw : run target429 t blank = some e := by
        rw [htime2,run_add',h145run]
        exact he
      exact ⟨e,hraw,by omega⟩
  have hmark : c21.tape 26 = true := by
    rw [represented_junc_cell 21 11 c21 hrep21 26]
    rw [hhead]
    norm_num [jTape,jMark,jHole]
  have hblank : ∀ x : Int, 26<x → c21.tape x=false := by
    intro x hx
    rw [represented_junc_cell 21 11 c21 hrep21 x]
    rw [hhead]
    simp [jTape,jMark,jHole]
    omega
  obtain ⟨hmon⟩ :=
    root_runWithHeadMax_exists_of_run target429 1608 blank c21 htotal
  have hupper :=
    root_runWithHeadMax_bound_of_prefix target429 1608 blank c21 hmon
      26 hprefix
  have hlower : 26≤hmon := by
    by_contra hlt
    have hunchanged :=
      runWithHeadMax_tape_above target429 1608 blank c21 hmon
        26 (by omega)
    have hblank0 : blank.tape 26=false := by rfl
    rw [hmark,hblank0] at hunchanged
    contradiction
  have hmonExact : hmon=26 := by omega
  refine ⟨c21,htotal,hrep21,hhead,hmark,hblank,hprefix,?_⟩
  simpa [hmonExact] using
    (show runWithHeadMax target429 1608 blank = some (c21,hmon) from
      root_runWithHeadMax_exists_of_run target429 1608 blank c21 htotal |>.choose_spec)

/-- Continue the authentic blank root through the corrected low43 branch.
    The exact 3167-step endpoint is J(11,62), with head -29 and global
    head maximum 36. -/
theorem root_after_3167_junc11_frontier :
    ∃ d : Config,
      run target429 3167 blank = some d ∧
      Represents (junc 11 0 62) d ∧
      d.head = -29 ∧
      d.tape 36 = true ∧
      (∀ x : Int, 36 < x → d.tape x = false) ∧
      (∀ t : Nat, t≤3167 →
        ∃ e : Config,
          run target429 t blank = some e ∧ e.head≤36) ∧
      runWithHeadMax target429 3167 blank = some (d,36) := by
  rcases root_after_1608_junc21_frontier with
    ⟨c21,hroot,hrep21,hhead21,hmark26,hblank26,hrootPrefix,hrootMon⟩
  obtain ⟨cBranch,hbranch,hrepBranch,hbranchHead,hbranchPrefix⟩ :=
    root_low43_branch_to_junc11
  have hstartCanonical :=
    represented_junc_eq_translatedJ 21 11 c21 hrep21
  have hstart :
      c21 = shiftConfig 12 (jConfig 21 11) := by
    rw [hhead21] at hstartCanonical
    simpa [translatedJ,shiftConfig,jConfig] using hstartCanonical
  let dEnd : Config := shiftConfig 12 cBranch
  have hbranchShift :
      run target429 1559 c21 = some dEnd := by
    rw [hstart]
    have h := run_shiftConfig target429 1559 12 (jConfig 21 11)
    rw [hbranch] at h
    simpa [dEnd] using h
  have htotal0 :
      run target429 (1608+1559) blank = some dEnd := by
    rw [run_add',hroot]
    exact hbranchShift
  have htime : 1608+1559=3167 := by omega
  have htotal : run target429 3167 blank = some dEnd := by
    simpa [htime] using htotal0
  have hhead : dEnd.head = -29 := by
    dsimp [dEnd,shiftConfig]
    rw [hbranchHead]
    norm_num
  have hcanonicalBranch :=
    represented_junc_eq_translatedJ 11 62 cBranch hrepBranch
  have hrepEnd : Represents (junc 11 0 62) dEnd := by
    rw [hbranchHead] at hcanonicalBranch
    have hshift :
        shiftConfig 12 cBranch = translatedJ 11 62 (-29) := by
      rw [hcanonicalBranch]
      simp [shiftConfig,translatedJ]
    rw [show dEnd = shiftConfig 12 cBranch by rfl, hshift]
    exact canonical_junc_rep 11 62 (-29)
  have hprefix :
      ∀ t : Nat, t≤3167 →
        ∃ e : Config,
          run target429 t blank = some e ∧ e.head≤36 := by
    intro t ht
    by_cases hle : t≤1608
    · obtain ⟨e,he,hb⟩ := hrootPrefix t hle
      exact ⟨e,he,by omega⟩
    · let s : Nat := t-1608
      have hs : s≤1559 := by dsimp [s]; omega
      obtain ⟨e,he,hb⟩ := hbranchPrefix s hs
      let eShift : Config := shiftConfig 12 e
      have htime2 : t=1608+s := by dsimp [s]; omega
      have hraw : run target429 t blank = some eShift := by
        rw [htime2,run_add',hroot]
        have hshiftRun := run_shiftConfig target429 s 12 (jConfig 21 11)
        rw [he] at hshiftRun
        simpa [eShift,hstart] using hshiftRun
      exact ⟨eShift,hraw,by dsimp [eShift,shiftConfig]; omega⟩
  have hmark : dEnd.tape 36 = true := by
    rw [represented_junc_cell 11 62 dEnd hrepEnd 36]
    rw [hhead]
    norm_num [jTape,jMark,jHole]
  have hblank : ∀ x : Int, 36<x → dEnd.tape x=false := by
    intro x hx
    rw [represented_junc_cell 11 62 dEnd hrepEnd x]
    rw [hhead]
    simp [jTape,jMark,jHole]
    omega
  obtain ⟨hmon⟩ :=
    root_runWithHeadMax_exists_of_run target429 3167 blank dEnd htotal
  have hupper :=
    root_runWithHeadMax_bound_of_prefix target429 3167 blank dEnd hmon
      36 hprefix
  have hlower : 36≤hmon := by
    by_contra hlt
    have hunchanged :=
      runWithHeadMax_tape_above target429 3167 blank dEnd hmon
        36 (by omega)
    have hblank0 : blank.tape 36=false := by rfl
    rw [hmark,hblank0] at hunchanged
    contradiction
  have hmonExact : hmon=36 := by omega
  refine ⟨dEnd,htotal,hrepEnd,hhead,hmark,hblank,hprefix,?_⟩
  simpa [hmonExact] using
    (show runWithHeadMax target429 3167 blank = some (dEnd,hmon) from
      root_runWithHeadMax_exists_of_run target429 3167 blank dEnd htotal |>.choose_spec)

#print axioms root_junc0_to_junc21_max
#print axioms root_junc0_to_junc21_physical
#print axioms root_after_1608_junc21_frontier
#print axioms root_after_3167_junc11_frontier

end BB429RootJunctionChain
