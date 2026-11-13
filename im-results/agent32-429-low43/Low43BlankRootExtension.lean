import LowEvenR32RootExtension
import Low43RootNext
import OuterSafe
import NoFatalGuard
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low43BlankRootExtension

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429FinishScanEDelta
open BB429PhysicalBridge BB429OuterSafe BB429W4CZeroSafe BB429NoFatalGuard
open BB429JuncHeadExcursion
open BB429LowEvenR32RootExtension
open BB429Low43RootNext

/-- Lift a source-level guarded run to every complete physical tape
    represented by its input zipper, preserving C/01 exclusion at all
    primitive prefixes. -/
private theorem source_no_fatal_physical
    (n : Nat) (z z' : Zipper) (c : Config)
    (hrep : Represents z c)
    (hsource : runNoFatal n z = some z') :
    ∃ d : Config,
      BB6Coverage.run target429 n c = some d ∧
      Represents z' d ∧
      (∀ t : Nat, t ≤ n →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ C01Free e) := by
  have hrun : BB429OddExcursion.run n z = some z' :=
    runNoFatal_to_run n z z' hsource
  obtain ⟨d, hraw, hrepD⟩ :=
    source_run_rep n z c hrep z' hrun
  refine ⟨d, hraw, hrepD, ?_⟩
  intro t ht
  obtain ⟨p, hp, hpSafe⟩ :=
    runNoFatal_prefix n t z z' hsource ht
  obtain ⟨e, he, hrepE⟩ :=
    source_run_rep t z c hrep p hp
  refine ⟨e, he, ?_⟩
  intro hbad
  have hstate : p.state = 2 := hrepE.1.symm.trans hbad.1
  have hcurrent : p.current = false := hrepE.2.1.symm.trans hbad.2.1
  have hr0 := hrepE.2.2.2 0
  have hr0' : e.tape (e.head+1) = p.right.getD 0 false := by
    simpa using hr0
  have hright0 : p.right[0]?.getD false = true := by
    simpa using hr0'.symm.trans hbad.2.2
  have hfatal : fatalCZero p = true := by
    simp [fatalCZero, hstate, hcurrent, hright0]
  simp [hfatal] at hpSafe

/-- Every physical prefix of one outer-safe Junc macro is C/01-free. -/
private theorem outer_no_fatal_segment
    (U v w : Nat) (c : Config)
    (hrep : Represents (junc U v w) c)
    (hw : 2*U+3 ≤ w) :
    ∃ d : Config,
      BB6Coverage.run target429 (outerCost U v) c = some d ∧
      Represents (junc (v+2*U+3) 0 ((w-2*U)-3)) d ∧
      (∀ t : Nat, t ≤ outerCost U v →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ C01Free e) := by
  have hsource :
      BB429OddExcursion.run (outerCost U v) (junc U v w) =
        some (junc (v+2*U+3) 0 ((w-2*U)-3)) :=
    runSafe_to_run (outerCost U v) (junc U v w)
      (junc (v+2*U+3) 0 ((w-2*U)-3))
      (junc_outer_safe U v w hw)
  obtain ⟨d, hrun, hrepD⟩ :=
    source_run_rep (outerCost U v) (junc U v w) c hrep
      (junc (v+2*U+3) 0 ((w-2*U)-3)) hsource
  refine ⟨d, hrun, hrepD, ?_⟩
  intro t ht
  by_cases hlt : t < outerCost U v
  · obtain ⟨e, he, hnoC0⟩ :=
      physical_outer_no_czero U v w t c hrep hw hlt
    exact ⟨e, he, by
      intro hbad
      exact hnoC0 ⟨hbad.1, hbad.2.1⟩⟩
  · have htEq : t = outerCost U v := by omega
    subst t
    refine ⟨d, hrun, ?_⟩
    intro hbad
    have hs : d.state.val = (junc (v+2*U+3) 0 ((w-2*U)-3)).state :=
      hrepD.1
    have hs0 : (junc (v+2*U+3) 0 ((w-2*U)-3)).state = 0 := by rfl
    rw [hs0] at hs
    omega

/-- Compose physical segments and preserve their complete-prefix
    C/01-free property. -/
private theorem physical_prefix_compose
    (m n : Nat) (c c1 c2 : Config)
    (h1 : BB6Coverage.run target429 m c = some c1)
    (h2 : BB6Coverage.run target429 n c1 = some c2)
    (hp1 : ∀ t : Nat, t ≤ m →
      ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e)
    (hp2 : ∀ t : Nat, t ≤ n →
      ∃ e : Config, BB6Coverage.run target429 t c1 = some e ∧ C01Free e) :
    BB6Coverage.run target429 (m+n) c = some c2 ∧
    (∀ t : Nat, t ≤ m+n →
      ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) := by
  have htotal : BB6Coverage.run target429 (m+n) c = some c2 := by
    rw [BB6Bubble.run_add', h1]
    exact h2
  refine ⟨htotal, ?_⟩
  intro t ht
  by_cases hfirst : t ≤ m
  · exact hp1 t hfirst
  · let s : Nat := t-m
    have hs : s ≤ n := by dsimp [s]; omega
    obtain ⟨e, he, hsafe⟩ := hp2 s hs
    have htime : t = m+s := by dsimp [s]; omega
    refine ⟨e, ?_, hsafe⟩
    rw [htime, BB6Bubble.run_add', h1]
    exact he

/-- Five outer-safe returns, U=0,3,9,21,45, form a single
    11139-step ladder J(0,w) -> J(93,w-171), for w >= 171. -/
theorem outer_ladder_0_to_93
    (w : Nat) (c : Config)
    (hrep : Represents (junc 0 0 w) c)
    (hw : 171 ≤ w) :
    ∃ d : Config,
      BB6Coverage.run target429 11139 c = some d ∧
      Represents (junc 93 0 (w-171)) d ∧
      (∀ t : Nat, t ≤ 11139 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧ C01Free e) := by
  obtain ⟨c3,h0,hr3,hp0⟩ :=
    outer_no_fatal_segment 0 0 w c hrep (by omega)
  have cost0 : outerCost 0 0 = 27 := by
    norm_num [outerCost, juncPosFullTime]
  have h0' : BB6Coverage.run target429 27 c = some c3 := by
    simpa [cost0] using h0
  have hp0' : ∀ t : Nat, t ≤ 27 →
      ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e := by
    simpa [cost0] using hp0

  obtain ⟨c9,h3,hr9,hp3⟩ :=
    outer_no_fatal_segment 3 0 (w-3) c3 (by simpa using hr3) (by omega)
  have cost3 : outerCost 3 0 = 93 := by
    norm_num [outerCost, juncPosFullTime]
  have h3' : BB6Coverage.run target429 93 c3 = some c9 := by
    simpa [cost3] using h3
  have hp3' : ∀ t : Nat, t ≤ 93 →
      ∃ e : Config, BB6Coverage.run target429 t c3 = some e ∧ C01Free e := by
    simpa [cost3] using hp3
  have chain120 := physical_prefix_compose 27 93 c c3 c9
    h0' h3' hp0' hp3'

  have hr9' : Represents (junc 9 0 (w-12)) c9 := by
    simpa [show (w-3)-9 = w-12 by omega] using hr9
  obtain ⟨c21,h9,hr21,hp9⟩ :=
    outer_no_fatal_segment 9 0 (w-12) c9 hr9' (by omega)
  have cost9 : outerCost 9 0 = 441 := by
    norm_num [outerCost, juncPosFullTime]
  have h9' : BB6Coverage.run target429 441 c9 = some c21 := by
    simpa [cost9] using h9
  have hp9' : ∀ t : Nat, t ≤ 441 →
      ∃ e : Config, BB6Coverage.run target429 t c9 = some e ∧ C01Free e := by
    simpa [cost9] using hp9
  have chain561 := physical_prefix_compose 120 441 c c9 c21
    chain120.1 h9' chain120.2 hp9'

  have hr21' : Represents (junc 21 0 (w-33)) c21 := by
    simpa [show (w-12)-21 = w-33 by omega] using hr21
  obtain ⟨c45,h21,hr45,hp21⟩ :=
    outer_no_fatal_segment 21 0 (w-33) c21 hr21' (by omega)
  have cost21 : outerCost 21 0 = 2001 := by
    norm_num [outerCost, juncPosFullTime]
  have h21' : BB6Coverage.run target429 2001 c21 = some c45 := by
    simpa [cost21] using h21
  have hp21' : ∀ t : Nat, t ≤ 2001 →
      ∃ e : Config, BB6Coverage.run target429 t c21 = some e ∧ C01Free e := by
    simpa [cost21] using hp21
  have chain2562 := physical_prefix_compose 561 2001 c c21 c45
    chain561.1 h21' chain561.2 hp21'

  have hr45' : Represents (junc 45 0 (w-78)) c45 := by
    simpa [show (w-33)-45 = w-78 by omega] using hr45
  obtain ⟨c93,h45,hr93,hp45⟩ :=
    outer_no_fatal_segment 45 0 (w-78) c45 hr45' (by omega)
  have cost45 : outerCost 45 0 = 8577 := by
    norm_num [outerCost, juncPosFullTime]
  have h45' : BB6Coverage.run target429 8577 c45 = some c93 := by
    simpa [cost45] using h45
  have hp45' : ∀ t : Nat, t ≤ 8577 →
      ∃ e : Config, BB6Coverage.run target429 t c45 = some e ∧ C01Free e := by
    simpa [cost45] using hp45
  have chain11139 := physical_prefix_compose 2562 8577 c c45 c93
    chain2562.1 h45' chain2562.2 hp45'
  have hfinal : (w-78)-93 = w-171 := by omega
  refine ⟨c93, chain11139.1, ?_, chain11139.2⟩
  simpa [hfinal] using hr93

def lowOddV22N34Start : Zipper := junc 93 0 45
def lowOddV22N34End : Zipper := junc 74 0 90
def low42J45K14Start : Zipper := junc 74 0 90
def low42J45K14End : Zipper := junc 0 0 248
def lowOddV38N26Start : Zipper := junc 93 0 77
def lowOddV38N26End : Zipper := junc 58 0 154

/-- Concrete guarded low-odd instance v=22,n=34. -/
theorem lowOdd_v22_n34_no_fatal_source :
    runNoFatal 3268 lowOddV22N34Start = some lowOddV22N34End := by
  decide

/-- Concrete guarded low42 instance j=45,k=14. -/
theorem low42_j45_k14_no_fatal_source :
    runNoFatal 9421 low42J45K14Start = some low42J45K14End := by
  decide

/-- Concrete guarded low-odd instance v=38,n=26. -/
theorem lowOdd_v38_n26_no_fatal_source :
    runNoFatal 7284 lowOddV38N26Start = some lowOddV38N26End := by
  decide

theorem lowOdd_v22_n34_no_fatal_physical (c : Config)
    (hrep : Represents lowOddV22N34Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 3268 c = some d ∧
      Represents lowOddV22N34End d ∧
      (∀ t : Nat, t ≤ 3268 →
        ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) :=
  source_no_fatal_physical 3268 lowOddV22N34Start lowOddV22N34End c hrep
    lowOdd_v22_n34_no_fatal_source

theorem low42_j45_k14_no_fatal_physical (c : Config)
    (hrep : Represents low42J45K14Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 9421 c = some d ∧
      Represents low42J45K14End d ∧
      (∀ t : Nat, t ≤ 9421 →
        ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) :=
  source_no_fatal_physical 9421 low42J45K14Start low42J45K14End c hrep
    low42_j45_k14_no_fatal_source

theorem lowOdd_v38_n26_no_fatal_physical (c : Config)
    (hrep : Represents lowOddV38N26Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 7284 c = some d ∧
      Represents lowOddV38N26End d ∧
      (∀ t : Nat, t ≤ 7284 →
        ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) :=
  source_no_fatal_physical 7284 lowOddV38N26Start lowOddV38N26End c hrep
    lowOdd_v38_n26_no_fatal_source

/-- Extend the 43,862-step blank-root r=32 chain through the exact
    outer/low-odd/low42 route to J(119,35), then through the new 36,006-step
    prepared chain to J(69,186). Every physical prefix is C/01-free. -/
theorem blank_root_lowEvenR32_to_junc69_186 :
    ∃ c93a c74 c248 c93b c58 c119 c69 : Config,
      BB6Coverage.run target429 55001 blank = some c93a ∧
      Represents (junc 93 0 45) c93a ∧
      BB6Coverage.run target429 58269 blank = some c74 ∧
      Represents (junc 74 0 90) c74 ∧
      BB6Coverage.run target429 67690 blank = some c248 ∧
      Represents (junc 0 0 248) c248 ∧
      BB6Coverage.run target429 78829 blank = some c93b ∧
      Represents (junc 93 0 77) c93b ∧
      BB6Coverage.run target429 86113 blank = some c58 ∧
      Represents (junc 58 0 154) c58 ∧
      BB6Coverage.run target429 100176 blank = some c119 ∧
      Represents (junc 119 0 35) c119 ∧
      BB6Coverage.run target429 136182 blank = some c69 ∧
      Represents (junc 69 0 186) c69 ∧
      (∀ t : Nat, t ≤ 136182 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧ C01Free e) := by
  obtain ⟨c184,c93old,c90,c216,h29698,hrep184,h40837,hrep93old,
      h42137,hrep90,h43862,hrep216,hprefixRoot⟩ :=
    blank_root_lowEvenR32_to_junc0_216

  obtain ⟨c93a,houter1,hrep93a,hpref1⟩ :=
    outer_ladder_0_to_93 216 c216 hrep216 (by omega)
  have chain55001 := physical_prefix_compose 43862 11139 blank c216 c93a
    h43862 houter1 hprefixRoot hpref1

  obtain ⟨c74,hodd1,hrep74,hprefodd1⟩ :=
    lowOdd_v22_n34_no_fatal_physical c93a hrep93a
  have chain58269 := physical_prefix_compose 55001 3268 blank c93a c74
    chain55001.1 hodd1 chain55001.2 hprefodd1

  obtain ⟨c248,h42,hrep248,hpref42⟩ :=
    low42_j45_k14_no_fatal_physical c74 hrep74
  have chain67690 := physical_prefix_compose 58269 9421 blank c74 c248
    chain58269.1 h42 chain58269.2 hpref42

  obtain ⟨c93b,houter2,hrep93b,hpref2⟩ :=
    outer_ladder_0_to_93 248 c248 hrep248 (by omega)
  have chain78829 := physical_prefix_compose 67690 11139 blank c248 c93b
    chain67690.1 houter2 chain67690.2 hpref2

  obtain ⟨c58,hodd2,hrep58,hprefodd2⟩ :=
    lowOdd_v38_n26_no_fatal_physical c93b hrep93b
  have chain86113 := physical_prefix_compose 78829 7284 blank c93b c58
    chain78829.1 hodd2 chain78829.2 hprefodd2

  obtain ⟨c119,houter58,hrep119,hpref58⟩ :=
    outer_no_fatal_segment 58 0 154 c58 hrep58 (by omega)
  have cost58 : outerCost 58 0 = 14063 := by
    norm_num [outerCost, juncPosFullTime]
  have houter58' : BB6Coverage.run target429 14063 c58 = some c119 := by
    simpa [cost58] using houter58
  have hpref58' : ∀ t : Nat, t ≤ 14063 →
      ∃ e : Config, BB6Coverage.run target429 t c58 = some e ∧ C01Free e := by
    simpa [cost58] using hpref58
  have chain100176 := physical_prefix_compose 86113 14063 blank c58 c119
    chain86113.1 houter58' chain86113.2 hpref58'

  obtain ⟨c69,hprepared,hrep69,hprefPrepared⟩ :=
    source_no_fatal_physical 36006 (junc 119 0 35) (junc 69 0 186)
      c119 hrep119 root_low43_119_to_69_no_fatal
  have chain136182 := physical_prefix_compose 100176 36006 blank c119 c69
    chain100176.1 hprepared chain100176.2 hprefPrepared

  exact ⟨c93a,c74,c248,c93b,c58,c119,c69,
    chain55001.1,hrep93a,
    chain58269.1,hrep74,
    chain67690.1,hrep248,
    chain78829.1,hrep93b,
    chain86113.1,hrep58,
    chain100176.1,hrep119,
    chain136182.1,hrep69,
    chain136182.2⟩

#print axioms lowOdd_v22_n34_no_fatal_source
#print axioms low42_j45_k14_no_fatal_source
#print axioms lowOdd_v38_n26_no_fatal_source
#print axioms outer_ladder_0_to_93
#print axioms blank_root_lowEvenR32_to_junc69_186

end BB429Low43BlankRootExtension
