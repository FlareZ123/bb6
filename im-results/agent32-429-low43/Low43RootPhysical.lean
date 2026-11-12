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

/-- The concrete v=5,k=7 C/0 context continues for 438 moves to
    J(23,18), with a certified maximum rightward displacement of one. -/
theorem root_low43_C0_to_junc_physical
    (c : Config) (hrep : Represents (low43_C0_zipper 5 7) c) :
    ∃ d : Config,
      run target429 438 c = some d ∧
      Represents (junc 23 0 18) d ∧
      d.head=c.head-20 ∧
      (∀ t : Nat, t≤438 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+1) := by
  let zC0 : Zipper := low43_C0_zipper 5 7
  have hmax :
      runWithMax 438 zC0 =
        some (junc 23 0 18, -20, 1) := by
    simpa [zC0,low43_C0_zipper] using root_low43_C0_to_junc_max
  have hdelta :
      runWithDelta 438 zC0 = some (junc 23 0 18,-20) := by
    simpa [hmax] using runWithMax_toDelta 438 zC0
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 438 zC0 c hrep (junc 23 0 18) (-20) hdelta
  have hprefix :
      ∀ t : Nat, t≤438 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+1 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 438 t zC0 c hrep
        (junc 23 0 18,-20,1) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩

/-- The complete 1347-step C/0 continuation reaches J(11,62). Its
    all-prefix maximum is eight cells to the right of the C/0 entry. -/
theorem root_low43_C0_to_junc11_physical
    (c : Config) (hrep : Represents (low43_C0_zipper 5 7) c) :
    ∃ d : Config,
      run target429 1347 c = some d ∧
      Represents (junc 11 0 62) d ∧
      d.head=c.head-57 ∧
      (∀ t : Nat, t≤1347 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+8) := by
  let zC0 : Zipper := low43_C0_zipper 5 7
  have hmax :
      runWithMax 1347 zC0 =
        some (junc 11 0 62, -57, 8) := by
    simpa [zC0,low43_C0_zipper] using root_low43_C0_to_junc11_max
  have hdelta :
      runWithDelta 1347 zC0 = some (junc 11 0 62,-57) := by
    simpa [hmax] using runWithMax_toDelta 1347 zC0
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 1347 zC0 c hrep (junc 11 0 62) (-57) hdelta
  have hprefix :
      ∀ t : Nat, t≤1347 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+8 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 1347 t zC0 c hrep
        (junc 11 0 62,-57,8) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩

/-- Full physical low-43 branch from J(21,11) to J(23,18).
    Every prefix remains at or left of local coordinate 17. -/
theorem root_low43_branch_to_junc :
    ∃ cEnd : Config,
      run target429 650
        {state:=A,head:=0,tape:=jTape 21 11} = some cEnd ∧
      Represents (junc 23 0 18) cEnd ∧
      cEnd.head = -4 ∧
      (∀ t : Nat, t≤650 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤17) := by
  obtain ⟨cC,hCrun,hChead,hCRep,hCstate,hCcur,hCright,hCprev⟩ :=
    low43_C0_record 5 7
  obtain ⟨cEnd,hcont,hEndRep,hEndHead,hcontPrefix⟩ :=
    root_low43_C0_to_junc_physical cC hCRep
  have htotal0 : run target429 (212+438)
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    rw [run_add',hCrun]
    exact hcont
  have htime : 212+438=650 := by omega
  have htotal : run target429 650
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    simpa [htime] using htotal0
  have hhead : cEnd.head = -4 := by
    rw [hEndHead,hChead]
    norm_num
  have hprefix :
      ∀ t : Nat, t≤650 →
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
        have hs : s≤438 := by dsimp [s]; omega
        obtain ⟨d,hseg,hb⟩ := hcontPrefix s hs
        have htime2 : t=212+s := by dsimp [s]; omega
        have hraw : run target429 t
            {state:=A,head:=0,tape:=jTape 21 11} = some d := by
          rw [htime2,run_add',hCrun]
          exact hseg
        exact ⟨d,hraw,by rw [hChead] at hb; omega⟩
  exact ⟨cEnd,htotal,hEndRep,hhead,hprefix⟩

/-- Continue the same root-specific branch through J(23,18) to J(11,62).
    Every primitive prefix from J(21,11) remains at or left of local
    coordinate 24; the endpoint head is -41. -/
theorem root_low43_branch_to_junc11 :
    ∃ cEnd : Config,
      run target429 1559
        {state:=A,head:=0,tape:=jTape 21 11} = some cEnd ∧
      Represents (junc 11 0 62) cEnd ∧
      cEnd.head = -41 ∧
      (∀ t : Nat, t≤1559 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤24) := by
  obtain ⟨cC,hCrun,hChead,hCRep,hCstate,hCcur,hCright,hCprev⟩ :=
    low43_C0_record 5 7
  obtain ⟨cEnd,hcont,hEndRep,hEndHead,hcontPrefix⟩ :=
    root_low43_C0_to_junc11_physical cC hCRep
  have htotal0 : run target429 (212+1347)
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    rw [run_add',hCrun]
    exact hcont
  have htime : 212+1347=1559 := by omega
  have htotal : run target429 1559
      {state:=A,head:=0,tape:=jTape 21 11} = some cEnd := by
    simpa [htime] using htotal0
  have hhead : cEnd.head = -41 := by
    rw [hEndHead,hChead]
    norm_num
  have hprefix :
      ∀ t : Nat, t≤1559 →
        ∃ d : Config,
          run target429 t {state:=A,head:=0,tape:=jTape 21 11} = some d ∧
          d.head≤24 := by
    intro t ht
    by_cases hlt : t<212
    · obtain ⟨d,hd,hb⟩ := hCprev t hlt
      exact ⟨d,hd,by rw [hChead] at hb; omega⟩
    · by_cases heq : t=212
      · subst t
        exact ⟨cC,hCrun,by rw [hChead]; omega⟩
      · let s : Nat := t-212
        have hs : s≤1347 := by dsimp [s]; omega
        obtain ⟨d,hseg,hb⟩ := hcontPrefix s hs
        have htime2 : t=212+s := by dsimp [s]; omega
        have hraw : run target429 t
            {state:=A,head:=0,tape:=jTape 21 11} = some d := by
          rw [htime2,run_add',hCrun]
          exact hseg
        exact ⟨d,hraw,by rw [hChead] at hb; omega⟩
  exact ⟨cEnd,htotal,hEndRep,hhead,hprefix⟩


/-- Full-tape physical lift of the concrete low-even r=96 transition
    J(49,2) -> J(11,98), retaining the complete prefix head maximum. -/
theorem root_low_even_r96_physical
    (c : Config) (hrep : Represents (junc 49 0 2) c) :
    ∃ d : Config,
      run target429 719 c = some d ∧
      Represents (junc 11 0 98) d ∧
      d.head=c.head-89 ∧
      (∀ t : Nat, t≤719 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+12) := by
  let z49 : Zipper := junc 49 0 2
  have hmax :
      runWithMax 719 z49 =
        some (junc 11 0 98, -89, 12) := by
    simpa [z49] using root_low_even_r96_max
  have hdelta :
      runWithDelta 719 z49 = some (junc 11 0 98,-89) := by
    simpa [hmax] using runWithMax_toDelta 719 z49
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 719 z49 c hrep (junc 11 0 98) (-89) hdelta
  have hprefix :
      ∀ t : Nat, t≤719 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+12 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 719 t z49 c hrep
        (junc 11 0 98,-89,12) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩


/-- Physical all-prefix lift of the prepared J(11,62) -> J(10,74)
    high-three/low-odd route. The complete segment maximum is +68. -/
theorem root_junc11_to_junc10_physical
    (c : Config) (hrep : Represents (junc 11 0 62) c) :
    ∃ d : Config,
      run target429 2457 c = some d ∧
      Represents (junc 10 0 74) d ∧
      d.head=c.head-9 ∧
      (∀ t : Nat, t≤2457 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+68) := by
  let z11 : Zipper := junc 11 0 62
  have hmax :
      runWithMax 2457 z11 =
        some (junc 10 0 74, -9, 68) := by
    simpa [z11] using root_junc11_to_junc10_max
  have hdelta :
      runWithDelta 2457 z11 = some (junc 10 0 74,-9) := by
    simpa [hmax] using runWithMax_toDelta 2457 z11
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 2457 z11 c hrep (junc 10 0 74) (-9) hdelta
  have hprefix :
      ∀ t : Nat, t≤2457 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head≤c.head+68 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 2457 t z11 c hrep
        (junc 10 0 74,-9,68) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩

#print axioms physical_source_max_prefix_bound
#print axioms root_low43_C0_to_junc_physical
#print axioms root_low43_C0_to_junc11_physical
#print axioms root_low43_branch_to_junc
#print axioms root_low43_branch_to_junc11
#print axioms root_low_even_r96_physical
#print axioms root_junc11_to_junc10_physical

end BB429Low43RootPhysical
