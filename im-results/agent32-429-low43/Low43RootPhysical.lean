import Low43Physical
import Low43Continuation
import W4HeadMax
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import PhysicalRegularHeadMax
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low43RootPhysical

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429W4HeadMax BB429W4HeadPrefix
open BB429Low43Physical BB429Low43Continuation
open BB429PhysicalRegularHeadMax

private theorem runWithMax_prefix_exists (n t : Nat) (z : Zipper)
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

/-- Lift a source max certificate to every literal #429 raw prefix while
    retaining the complete zipper/tape representation. -/
theorem physical_source_max_prefix_bound
    (n t : Nat) (z : Zipper) (c : Config)
    (hrep : Represents z c) (q : Zipper × Int × Int)
    (hfull : runWithMax n z = some q) (ht : t≤n) :
    ∃ d : Config,
      run target429 t c = some d ∧ d.head ≤ c.head+q.2.2 := by
  obtain ⟨p,hp⟩ := runWithMax_prefix_exists n t z q hfull ht
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

/-- The concrete v=5,k=7 C/0 checkpoint continues for 119 moves to
    Junc(0,9,25), with a certified maximum rightward displacement of one. -/
theorem root_low43_C0_to_junc_physical
    (c : Config) (hrep : Represents (low43_C0_zipper 5 7) c) :
    ∃ d : Config,
      run target429 119 c = some d ∧
      Represents (junc 0 9 25) d ∧
      d.head=c.head-45 ∧
      (∀ t : Nat, t≤119 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+1) := by
  let zC0 : Zipper := low43_C0_zipper 5 7
  have hmax :
      runWithMax 119 zC0 =
        some (junc 0 9 25, -45, 1) := by
    simpa [zC0,low43_C0_zipper] using root_low43_C0_to_junc_max
  have hdelta :
      runWithDelta 119 zC0 = some (junc 0 9 25,-45) := by
    simpa [hmax] using runWithMax_toDelta 119 zC0
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 119 zC0 c hrep (junc 0 9 25) (-45) hdelta
  have hprefix :
      ∀ t : Nat, t≤119 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+1 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 119 t zC0 c hrep
        (junc 0 9 25,-45,1) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩

/-- Full physical low-43 branch from J(21,11) to Junc(0,9,25).
    Every prefix remains at or left of the new rightmost mark, 17. -/
theorem root_low43_branch_to_junc :
    ∃ cEnd : Config,
      run target429 331
        {state:=A,head:=0,tape:=jTape 21 11} = some cEnd ∧
      Represents (junc 0 9 25) cEnd ∧
      cEnd.head = -29 ∧
      (∀ t : Nat, t≤331 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤17) := by
  obtain ⟨cC,hCrun,hChead,hCRep,hCstate,hCcur,hCright,hCprev⟩ :=
    low43_C0_record 5 7
  obtain ⟨cEnd,hcont,hEndRep,hEndHead,hcontPrefix⟩ :=
    root_low43_C0_to_junc_physical cC hCRep
  have htotal0 : run target429 (212+119)
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    rw [run_add',hCrun]
    exact hcont
  have htime : 212+119=331 := by omega
  have htotal : run target429 331
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    simpa [htime] using htotal0
  have hhead : cEnd.head = -29 := by
    rw [hEndHead,hChead]
    norm_num
  have hprefix :
      ∀ t : Nat, t≤331 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤17 := by
    intro t ht
    by_cases hlt : t<212
    · obtain ⟨d,hd,hb⟩ := hCprev t hlt
      exact ⟨d,hd,by rw [hChead] at hb; omega⟩
    · by_cases heq : t=212
      · subst t
        exact ⟨cC,hCrun,by rw [hChead]; omega⟩
      · let s : Nat := t-212
        have hs : s≤119 := by dsimp [s]; omega
        obtain ⟨d,hseg,hb⟩ := hcontPrefix s hs
        have htime2 : t=212+s := by dsimp [s]; omega
        have hraw : run target429 t
            {state:=A,head:=0,tape:=jTape 21 11} = some d := by
          rw [htime2,run_add',hCrun]
          exact hseg
        exact ⟨d,hraw,by rw [hChead] at hb; omega⟩
  exact ⟨cEnd,htotal,hEndRep,hhead,hprefix⟩

/-- The regular zero-left return closes the root-specific low-43 branch at
    Junc(12,0,22), conserving the new rightmost mark at coordinate 17. -/
theorem root_low43_branch_to_junc12 :
    ∃ cEnd : Config,
      run target429 376
        {state:=A,head:=0,tape:=jTape 21 11} = some cEnd ∧
      Represents (junc 12 0 22) cEnd ∧
      cEnd.head = -8 ∧
      (∀ t : Nat, t≤376 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤17) := by
  obtain ⟨cJ,hJrun,hJrep,hJhead,hJprefix⟩ :=
    root_low43_branch_to_junc
  have hJrep' : Represents (junc 0 9 (22+3)) cJ := by
    simpa using hJrep
  obtain ⟨cEnd,hzero,hEndRep,hfrontier⟩ :=
    physical_zero_regular_frontier_conserved 9 22 cJ hJrep'
  have htotal0 : run target429 (331+45)
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    rw [run_add',hJrun]
    simpa using hzero
  have htime : 331+45=376 := by omega
  have htotal : run target429 376
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    simpa [htime] using htotal0
  have hhead : cEnd.head=-8 := by
    have hfrontier' :
        cEnd.head+25 = (-29: Int)+(2*9+22+6) := by
      simpa [hJhead] using hfrontier
    omega
  have hprefix :
      ∀ t : Nat, t≤376 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤17 := by
    intro t ht
    by_cases hlt : t≤331
    · exact hJprefix t hlt
    · let s : Nat := t-331
      have hs : s≤45 := by dsimp [s]; omega
      obtain ⟨d,hseg,hb⟩ :=
        physical_zero_regular_all_prefixes_before_old_mark 9 22 s cJ hJrep' hs
      have htime2 : t=331+s := by dsimp [s]; omega
      have hraw : run target429 t
          {state:=A,head:=0,tape:=jTape 21 11} = some d := by
        rw [htime2,run_add',hJrun]
        exact hseg
      have hmark : cJ.head+(2*9+22+6)=17 := by
        rw [hJhead]
        norm_num
      exact ⟨d,hraw,by rw [hmark] at hb; omega⟩
  exact ⟨cEnd,htotal,hEndRep,hhead,hprefix⟩

#print axioms physical_source_max_prefix_bound
#print axioms root_low43_C0_to_junc_physical
#print axioms root_low43_branch_to_junc
#print axioms root_low43_branch_to_junc12

end BB429Low43RootPhysical
