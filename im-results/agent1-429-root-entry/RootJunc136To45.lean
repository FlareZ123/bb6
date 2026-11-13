import RootNoFatalChain
import PhysicalSafe
import PhysicalRegularHeadMax
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

namespace BB429RootJunc136To45

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429JuncHeadExcursion BB429W4CZeroSafe
open BB429PositiveSafe BB429ZeroRegularSafe
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429PhysicalGuardSafe BB429PhysicalRegularHeadMax
open BB429Low42RootNoFatal BB429RootNoFatalChain

/-- The authentic start and target of the seven ordinary Junc returns. -/
def rootJunc136 : Zipper := junc 0 0 136
def rootJunc45 : Zipper := junc 45 0 58

private theorem safe_compose (m n : Nat) (z z1 z2 : Zipper)
    (h1 : runSafe m z = some z1)
    (h2 : runSafe n z1 = some z2) :
    runSafe (m+n) z = some z2 := by
  rw [runSafe_add, h1]
  simp only [Option.bind_some]
  exact h2

/-- Exact composition of the seven C/0-free ordinary source macros:
    27 + 54 + 39 + 378 + 63 + 1890 + 111 = 2562 steps. -/
theorem root_regular_source_safe :
    runSafe 2562 rootJunc136 = some rootJunc45 := by
  have h1 : runSafe 27 rootJunc136 = some (junc 3 0 133) := by
    simpa [rootJunc136] using
      junc0_regular_safe 0 136 (by omega)
  have h2 : runSafe (juncPosFullTime 3 0) (junc 3 0 133) =
      some (junc 0 6 127) :=
    junc_positive_iter_safe 3 3 0 133 (by omega) (by omega)
  have h3 : runSafe 39 (junc 0 6 127) =
      some (junc 9 0 124) := by
    simpa using junc0_regular_safe 6 127 (by omega)
  have h4 : runSafe (juncPosFullTime 9 0) (junc 9 0 124) =
      some (junc 0 18 106) :=
    junc_positive_iter_safe 9 9 0 124 (by omega) (by omega)
  have h5 : runSafe 63 (junc 0 18 106) =
      some (junc 21 0 103) := by
    simpa using junc0_regular_safe 18 106 (by omega)
  have h6 : runSafe (juncPosFullTime 21 0) (junc 21 0 103) =
      some (junc 0 42 61) :=
    junc_positive_iter_safe 21 21 0 103 (by omega) (by omega)
  have h7 : runSafe 111 (junc 0 42 61) =
      some rootJunc45 := by
    simpa [rootJunc45] using junc0_regular_safe 42 61 (by omega)
  have h12 := safe_compose 27 (juncPosFullTime 3 0)
    rootJunc136 (junc 3 0 133) (junc 0 6 127) h1 h2
  have h123 := safe_compose (27+juncPosFullTime 3 0) 39
    rootJunc136 (junc 0 6 127) (junc 9 0 124) h12 h3
  have h1234 := safe_compose
    (27+juncPosFullTime 3 0+39) (juncPosFullTime 9 0)
    rootJunc136 (junc 9 0 124) (junc 0 18 106) h123 h4
  have h12345 := safe_compose
    (27+juncPosFullTime 3 0+39+juncPosFullTime 9 0) 63
    rootJunc136 (junc 0 18 106) (junc 21 0 103) h1234 h5
  have h123456 := safe_compose
    (27+juncPosFullTime 3 0+39+juncPosFullTime 9 0+63)
    (juncPosFullTime 21 0)
    rootJunc136 (junc 21 0 103) (junc 0 42 61) h12345 h6
  have htotal := safe_compose
    (27+juncPosFullTime 3 0+39+juncPosFullTime 9 0+63+
      juncPosFullTime 21 0) 111
    rootJunc136 (junc 0 42 61) rootJunc45 h123456 h7
  have htime :
      27+juncPosFullTime 3 0+39+juncPosFullTime 9 0+63+
        juncPosFullTime 21 0+111 = 2562 := by
    norm_num [juncPosFullTime]
  simpa [htime] using htotal

private theorem physical_run_add (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add', h1]
  exact h2

/-- A zero-left ordinary return preserves the absolute rightmost mark
    and keeps every physical head strictly to its left. -/
private theorem zero_frontier_segment (v W : Nat) (c : Config) (F : Int)
    (hrep : Represents (junc 0 v W) c)
    (hW : 3 ≤ W)
    (hF : c.head + ((2*v+W+3 : Nat) : Int) = F) :
    ∃ d : Config,
      BB6Coverage.run target429 (2*v+27) c = some d ∧
      Represents (junc (v+3) 0 (W-3)) d ∧
      (∀ t : Nat, t ≤ 2*v+27 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ e.head < F) ∧
      d.head + ((W : Nat) : Int) = F := by
  have hW3 : W-3+3 = W := Nat.sub_add_cancel hW
  have hrep' : Represents (junc 0 v (W-3+3)) c := by
    simpa [hW3] using hrep
  obtain ⟨d,hraw,hrepD,hfront⟩ :=
    physical_zero_regular_frontier_conserved v (W-3) c hrep'
  have hprefix :
      ∀ t : Nat, t ≤ 2*v+27 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ e.head < F := by
    intro t ht
    obtain ⟨e,he,hbound⟩ :=
      physical_zero_regular_all_prefixes_before_old_mark
        v (W-3) t c hrep' ht
    refine ⟨e,he,?_⟩
    have hcalc : 2*v+(W-3)+6 = 2*v+W+3 := by omega
    omega
  have hEnd : d.head + ((W : Nat) : Int) = F := by
    have hcalc : 2*v+(W-3)+6 = 2*v+W+3 := by omega
    calc
      d.head + ((W : Nat) : Int) =
          d.head + (((W-3+3 : Nat) : Int) := by rw [← hW3]
      _ = c.head + ((2*v+(W-3)+6 : Nat) : Int) := hfront
      _ = c.head + ((2*v+W+3 : Nat) : Int) := by congr 1 <;> omega
      _ = F := hF
  exact ⟨d,hraw,hrepD,hprefix,hEnd⟩

/-- Any affordable block of positive-left ordinary Junc returns preserves
    the absolute rightmost mark. Every physical primitive prefix stays
    strictly left of that mark. -/
private theorem positive_iter_frontier_segment
    (N U v w : Nat) (c : Config) (F : Int)
    (hrep : Represents (junc U v w) c)
    (hU : N ≤ U) (hw : 2*N ≤ w)
    (hF : c.head + ((2*v+w+3 : Nat) : Int) = F) :
    ∃ d : Config,
      BB6Coverage.run target429 (juncPosFullTime N v) c = some d ∧
      Represents (junc (U-N) (v+2*N) (w-2*N)) d ∧
      (∀ t : Nat, t ≤ juncPosFullTime N v →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ e.head < F) ∧
      d.head + ((2*(v+2*N)+(w-2*N)+3 : Nat) : Int) = F := by
  induction N generalizing U v w c F with
  | zero =>
      refine ⟨c, ?_, ?_, ?_, ?_⟩
      · simp [juncPosFullTime]
      · simpa using hrep
      · intro t ht
        have ht0 : t = 0 := by omega
        subst t
        refine ⟨c, by simp, ?_⟩
        omega
      · simpa using hF
  | succ N ih =>
      have hUpos : 1 ≤ U := by omega
      have hwpos : 2 ≤ w := by omega
      have hu : (U-1)+1 = U := Nat.sub_add_cancel hUpos
      have hwEq : (w-2)+2 = w := Nat.sub_add_cancel hwpos
      have hrep' :
          Represents (junc ((U-1)+1) v ((w-2)+2)) c := by
        simpa [hu,hwEq] using hrep
      obtain ⟨c1,hstep,hrep1,hfront1⟩ :=
        physical_positive_regular_frontier_conserved
          (U-1) v (w-2) c hrep'
      have hfront1' :
          c1.head + ((2*(v+2)+(w-2)+3 : Nat) : Int) = F := by
        calc
          _ = c.head + ((2*v+(w-2)+5 : Nat) : Int) := hfront1
          _ = c.head + ((2*v+w+3 : Nat) : Int) := by congr 1 <;> omega
          _ = F := hF
      have hU' : N ≤ U-1 := by omega
      have hw' : 2*N ≤ w-2 := by omega
      obtain ⟨d,htail,hrepD,hprefixTail,hfrontD⟩ :=
        ih (U-1) (v+2) (w-2) c1 F hrep1 hU' hw' hfront1'
      have hu' : U-1-N = U-(N+1) := by omega
      have hv' : v+2+2*N = v+2*(N+1) := by omega
      have hw'' : w-2-2*N = w-2*(N+1) := by omega
      have hrepD' :
          Represents (junc (U-(N+1)) (v+2*(N+1))
            (w-2*(N+1))) d := by
        simpa [hu',hv',hw''] using hrepD
      have hfrontD' :
          d.head + ((2*(v+2*(N+1))+(w-2*(N+1))+3 : Nat) : Int) = F := by
        simpa [hv',hw''] using hfrontD
      have htime :
          juncPosFullTime (N+1) v =
            (4*v+10)+juncPosFullTime N (v+2) := by rfl
      have htotal :
          BB6Coverage.run target429 (juncPosFullTime (N+1) v) c =
            some d := by
        rw [htime, BB6Bubble.run_add', hstep]
        exact htail
      refine ⟨d,htotal,hrepD',?_,hfrontD'⟩
      intro t ht
      by_cases hfirst : t ≤ 4*v+10
      · obtain ⟨e,he,hbound⟩ :=
          physical_positive_regular_all_prefixes_before_old_mark
            (U-1) v (w-2) t c hrep' hfirst
        refine ⟨e,he,?_⟩
        have hcalc : 2*v+(w-2)+5 = 2*v+w+3 := by omega
        omega
      · let s : Nat := t-(4*v+10)
        have ht' :
            t ≤ (4*v+10)+juncPosFullTime N (v+2) := by
          simpa [htime] using ht
        have hs : s ≤ juncPosFullTime N (v+2) := by
          dsimp [s]
          omega
        obtain ⟨e,he,hbound⟩ := hprefixTail s hs
        have htime' : t = (4*v+10)+s := by
          dsimp [s]
          omega
        have hrun : BB6Coverage.run target429 t c = some e := by
          rw [htime', BB6Bubble.run_add', hstep]
          exact he
        exact ⟨e,hrun,hbound⟩

/-- Compose two physical segments while retaining a strict common
    right-frontier bound at every prefix, including both endpoints. -/
private theorem frontier_compose
    (m n : Nat) (c c1 c2 : Config) (F : Int)
    (h1 : BB6Coverage.run target429 m c = some c1)
    (h2 : BB6Coverage.run target429 n c1 = some c2)
    (hp1 : ∀ t : Nat, t ≤ m →
      ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ e.head < F)
    (hp2 : ∀ t : Nat, t ≤ n →
      ∃ e : Config, BB6Coverage.run target429 t c1 = some e ∧ e.head < F) :
    BB6Coverage.run target429 (m+n) c = some c2 ∧
    (∀ t : Nat, t ≤ m+n →
      ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ e.head < F) := by
  constructor
  · exact physical_run_add m n c c1 c2 h1 h2
  · intro t ht
    by_cases hfirst : t ≤ m
    · exact hp1 t hfirst
    · let s : Nat := t-m
      have hs : s ≤ n := by dsimp [s]; omega
      obtain ⟨e,he,hbound⟩ := hp2 s hs
      have htime : t = m+s := by dsimp [s]; omega
      refine ⟨e,?_,hbound⟩
      rw [htime, BB6Bubble.run_add', h1]
      exact he

/-- The seven regular Junc segments from Junc(0,0,136) to Junc(45,0,58)
    form one exact 2562-step physical transition. The absolute rightmost
    marked cell is conserved, and every physical head prefix remains
    strictly to its left. The same source composition excludes C/0 at
    every primitive prefix, including the endpoint. -/
theorem root_regular_physical (c : Config)
    (hrep : Represents rootJunc136 c) :
    ∃ d : Config,
      BB6Coverage.run target429 2562 c = some d ∧
      Represents rootJunc45 d ∧
      (∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          e.head < c.head + (139 : Int)) ∧
      d.head + (61 : Int) = c.head + (139 : Int) ∧
      (∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false)) := by
  let F : Int := c.head + (139 : Int)
  have hF0 : c.head + ((2*0+136+3 : Nat) : Int) = F := by
    simp [F]
  obtain ⟨c1,h1,hrep1,hp1,hf1⟩ :=
    zero_frontier_segment 0 136 c F hrep (by omega) hF0
  have hF2 : c1.head + ((2*0+133+3 : Nat) : Int) = F := by
    simpa using hf1
  obtain ⟨c2,h2,hrep2,hp2,hf2⟩ :=
    positive_iter_frontier_segment 3 3 0 133 c1 F hrep1
      (by omega) (by omega) hF2
  have hF3 : c2.head + ((2*6+127+3 : Nat) : Int) = F := by
    simpa using hf2
  obtain ⟨c3,h3,hrep3,hp3,hf3⟩ :=
    zero_frontier_segment 6 127 c2 F hrep2 (by omega) hF3
  have hF4 : c3.head + ((2*0+124+3 : Nat) : Int) = F := by
    simpa using hf3
  obtain ⟨c4,h4,hrep4,hp4,hf4⟩ :=
    positive_iter_frontier_segment 9 9 0 124 c3 F hrep3
      (by omega) (by omega) hF4
  have hF5 : c4.head + ((2*18+106+3 : Nat) : Int) = F := by
    simpa using hf4
  obtain ⟨c5,h5,hrep5,hp5,hf5⟩ :=
    zero_frontier_segment 18 106 c4 F hrep4 (by omega) hF5
  have hF6 : c5.head + ((2*0+103+3 : Nat) : Int) = F := by
    simpa using hf5
  obtain ⟨c6,h6,hrep6,hp6,hf6⟩ :=
    positive_iter_frontier_segment 21 21 0 103 c5 F hrep5
      (by omega) (by omega) hF6
  have hF7 : c6.head + ((2*42+61+3 : Nat) : Int) = F := by
    simpa using hf6
  obtain ⟨c7,h7,hrep7,hp7,hf7⟩ :=
    zero_frontier_segment 42 61 c6 F hrep6 (by omega) hF7
  have hc12 := frontier_compose 27 (juncPosFullTime 3 0)
    c c1 c2 F h1 h2 hp1 hp2
  have hc123 := frontier_compose (27+juncPosFullTime 3 0) 39
    c c2 c3 F hc12.1 h3 hc12.2 hp3
  have hc1234 := frontier_compose
    (27+juncPosFullTime 3 0+39) (juncPosFullTime 9 0)
    c c3 c4 F hc123.1 h4 hc123.2 hp4
  have hc12345 := frontier_compose
    (27+juncPosFullTime 3 0+39+juncPosFullTime 9 0) 63
    c c4 c5 F hc1234.1 h5 hc1234.2 hp5
  have hc123456 := frontier_compose
    (27+juncPosFullTime 3 0+39+juncPosFullTime 9 0+63)
    (juncPosFullTime 21 0)
    c c5 c6 F hc12345.1 h6 hc12345.2 hp6
  have hc1234567 := frontier_compose
    (27+juncPosFullTime 3 0+39+juncPosFullTime 9 0+63+
      juncPosFullTime 21 0) 111
    c c6 c7 F hc123456.1 h7 hc123456.2 hp7
  have htime :
      27+juncPosFullTime 3 0+39+juncPosFullTime 9 0+63+
        juncPosFullTime 21 0+111 = 2562 := by
    norm_num [juncPosFullTime]
  have hrun : BB6Coverage.run target429 2562 c = some c7 := by
    simpa [htime] using hc1234567.1
  have hprefixF :
      ∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ e.head < F := by
    intro t ht
    apply hc1234567.2
    omega
  have hprefix :
      ∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          e.head < c.head + (139 : Int) := by
    simpa [F] using hprefixF
  have hfrontier : c7.head + (61 : Int) = c.head + (139 : Int) := by
    simpa [F] using hf7
  have hsafe := root_regular_source_safe
  have hnoC0 :
      ∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false) := by
    intro t ht
    by_cases hlt : t < 2562
    · exact physical_guarded_prefix 2562 t rootJunc136 rootJunc45
        c hrep hsafe hlt
    · have htEq : t = 2562 := by omega
      subst t
      refine ⟨c7,hrun,?_⟩
      have hs : c7.state.val = rootJunc45.state := hrep7.1
      have hs0 : rootJunc45.state = 0 := by rfl
      rw [hs0] at hs
      intro hbad
      omega
  exact ⟨c7,hrun,hrep7,hprefix,hfrontier,hnoC0⟩

/-- Compose the 2562-step regular chart with the 13,718-step authentic
    blank-root prefix. This gives a 16,280-step blank-root path to the
    concrete low-even prepared input Junc(45,0,58), with C/01 excluded
    at every physical prefix. On the appended regular chart, every head
    remains strictly left of the original Junc(0,0,136) rightmost mark. -/
theorem blank_root_no_fatal_to_junc45 :
    ∃ c0 d : Config,
      BB6Coverage.run target429 13718 blank = some c0 ∧
      Represents rootJunc136 c0 ∧
      BB6Coverage.run target429 16280 blank = some d ∧
      Represents rootJunc45 d ∧
      (∀ t : Nat, t ≤ 16280 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) ∧
      (∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 (13718+t) blank = some e ∧
          e.head < c0.head + (139 : Int)) ∧
      d.head + (61 : Int) = c0.head + (139 : Int) := by
  obtain ⟨c0,hroot,hrep0,hrootSafe⟩ :=
    blank_root_no_fatal_to_junc136
  have hrepStart : Represents rootJunc136 c0 := by
    simpa [rootJunc136,rootLow42End] using hrep0
  obtain ⟨d,hsegment,hrepD,hfront,hfrontEnd,hnoC0⟩ :=
    root_regular_physical c0 hrepStart
  have htotal0 :
      BB6Coverage.run target429 (13718+2562) blank = some d := by
    rw [BB6Bubble.run_add',hroot]
    exact hsegment
  have htime : 13718+2562=16280 := by omega
  have htotal : BB6Coverage.run target429 16280 blank = some d := by
    simpa [htime] using htotal0
  have hprefix :
      ∀ t : Nat, t ≤ 16280 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true) := by
    intro t ht
    by_cases hfirst : t ≤ 13718
    · exact hrootSafe t hfirst
    · let s : Nat := t-13718
      have hs : s ≤ 2562 := by dsimp [s]; omega
      obtain ⟨e,he,hgood⟩ := hnoC0 s hs
      have htime' : t = 13718+s := by dsimp [s]; omega
      have hrun : BB6Coverage.run target429 t blank = some e := by
        rw [htime',BB6Bubble.run_add',hroot]
        exact he
      refine ⟨e,hrun,?_⟩
      intro hbad
      exact hgood ⟨hbad.1,hbad.2.1⟩
  have hfrontRoot :
      ∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 (13718+t) blank = some e ∧
          e.head < c0.head + (139 : Int) := by
    intro t ht
    obtain ⟨e,he,hbound⟩ := hfront t ht
    refine ⟨e,?_,hbound⟩
    rw [BB6Bubble.run_add',hroot]
    exact he
  refine ⟨c0,d,hroot,hrepStart,htotal,hrepD,hprefix,hfrontRoot,?_⟩
  exact hfrontEnd

#print axioms root_regular_source_safe
#print axioms root_regular_physical
#print axioms blank_root_no_fatal_to_junc45

end BB429RootJunc136To45
