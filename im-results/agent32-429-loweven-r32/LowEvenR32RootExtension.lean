import LowEvenR32RootChain
import OuterSafe
import NoFatalGuard
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429LowEvenR32RootExtension

open BB6Coverage BB6Bubble BB429OddExcursion BB429FinishScanEDelta
open BB429PhysicalBridge BB429OuterSafe BB429W4CZeroSafe BB429NoFatalGuard
open BB429LowEvenR32 BB429LowEvenR32RootChain

/-- The actual C/01 halting gateway is absent from this configuration. -/
def C01Free (c : Config) : Prop :=
  ¬(c.state.val = 2 ∧ c.tape c.head = false ∧
    c.tape (c.head+1) = true)

/-- Generic lift: a source-level runNoFatal certificate transports through
    the complete-tape Represents relation and gives physical safety at every
    primitive prefix, including the endpoint. -/
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

/-- Every physical prefix of an outer-safe Junc macro is C/01-free.
    Before the endpoint the stronger C/0 exclusion holds; at the endpoint
    the target is in state A. -/
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

/-- Compose two complete-tape physical segments and their all-prefix C/01
    exclusion without losing the exact primitive-time endpoint. -/
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

def low42J34K9Start : Zipper := junc 53 0 68
def low42J34K9End : Zipper := junc 0 0 184
def lowOddV6N42Start : Zipper := junc 93 0 13
def lowOddV6N42End : Zipper := junc 90 0 26
def low42J13K38Start : Zipper := junc 90 0 26
def low42J13K38End : Zipper := junc 0 0 216

/-- Concrete guarded source certificate for the all-parameter Low42 instance
    j=34,k=9: Junc(53,68) -> Junc(0,184), 5,613 primitive steps. -/
theorem low42_j34k9_no_fatal_source :
    runNoFatal 5613 low42J34K9Start = some low42J34K9End := by
  decide

/-- Concrete guarded source certificate for the all-parameter low-odd
    instance v=6,n=42: Junc(93,13) -> Junc(90,26), 1,300 steps. -/
theorem lowOdd_v6_n42_no_fatal_source :
    runNoFatal 1300 lowOddV6N42Start = some lowOddV6N42End := by
  decide

/-- Concrete guarded source certificate for Low42 j=13,k=38:
    Junc(90,26) -> Junc(0,216), 1,725 steps. -/
theorem low42_j13k38_no_fatal_source :
    runNoFatal 1725 low42J13K38Start = some low42J13K38End := by
  decide

theorem low42_j34k9_no_fatal_physical (c : Config)
    (hrep : Represents low42J34K9Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 5613 c = some d ∧
      Represents low42J34K9End d ∧
      (∀ t : Nat, t ≤ 5613 →
        ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) :=
  source_no_fatal_physical 5613 low42J34K9Start low42J34K9End c hrep
    low42_j34k9_no_fatal_source

theorem lowOdd_v6_n42_no_fatal_physical (c : Config)
    (hrep : Represents lowOddV6N42Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 1300 c = some d ∧
      Represents lowOddV6N42End d ∧
      (∀ t : Nat, t ≤ 1300 →
        ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) :=
  source_no_fatal_physical 1300 lowOddV6N42Start lowOddV6N42End c hrep
    lowOdd_v6_n42_no_fatal_source

theorem low42_j13k38_no_fatal_physical (c : Config)
    (hrep : Represents low42J13K38Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 1725 c = some d ∧
      Represents low42J13K38End d ∧
      (∀ t : Nat, t ≤ 1725 →
        ∃ e : Config, BB6Coverage.run target429 t c = some e ∧ C01Free e) :=
  source_no_fatal_physical 1725 low42J13K38Start low42J13K38End c hrep
    low42_j13k38_no_fatal_source

/-- The concrete r=32 root continuation, two Low42/outer-safe passes,
    the low-odd (4k+1) return, and a final Low42 return compose to a
    43,862-step blank-root prefix ending at Junc(0,0,216). Every primitive
    physical prefix is C/01-free. This remains a finite prefix theorem. -/
theorem blank_root_lowEvenR32_to_junc0_216 :
    ∃ c184 c93 c90 c216 : Config,
      BB6Coverage.run target429 29698 blank = some c184 ∧
      Represents (junc 0 0 184) c184 ∧
      BB6Coverage.run target429 40837 blank = some c93 ∧
      Represents (junc 93 0 13) c93 ∧
      BB6Coverage.run target429 42137 blank = some c90 ∧
      Represents (junc 90 0 26) c90 ∧
      BB6Coverage.run target429 43862 blank = some c216 ∧
      Represents (junc 0 0 216) c216 ∧
      (∀ t : Nat, t ≤ 43862 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧ C01Free e) := by
  obtain ⟨c0, c45, c32, h13718, hrep136, h16280, hrep45,
      h20687, hrep32, hhead32, hprefixRoot, hfrontRoot, hfrontEnd⟩ :=
    blank_root_lowEvenR32_to_junc11_146
  have hrepStart11 : Represents (junc 11 0 146) c32 := by
    simpa [lowEvenEnd] using hrep32

  obtain ⟨c25, houter11, hrep25, hpref11⟩ :=
    outer_no_fatal_segment 11 0 146 c32 hrepStart11 (by omega)
  have hcost11 : outerCost 11 0 = 621 := by
    norm_num [outerCost, juncPosFullTime]
  have houter11' : BB6Coverage.run target429 621 c32 = some c25 := by
    simpa [hcost11] using houter11
  have hpref11' : ∀ t : Nat, t ≤ 621 →
      ∃ e : Config, BB6Coverage.run target429 t c32 = some e ∧ C01Free e := by
    simpa [hcost11] using hpref11

  obtain ⟨c53, houter25, hrep53, hpref25⟩ :=
    outer_no_fatal_segment 25 0 121 c25 (by simpa using hrep25) (by omega)
  have hcost25 : outerCost 25 0 = 2777 := by
    norm_num [outerCost, juncPosFullTime]
  have houter25' : BB6Coverage.run target429 2777 c25 = some c53 := by
    simpa [hcost25] using houter25
  have hpref25' : ∀ t : Nat, t ≤ 2777 →
      ∃ e : Config, BB6Coverage.run target429 t c25 = some e ∧ C01Free e := by
    simpa [hcost25] using hpref25

  obtain ⟨c184, hlow42, hrep184, hpreflow42⟩ :=
    low42_j34k9_no_fatal_physical c53 (by simpa [low42J34K9Start] using hrep53)

  have chain21308 := physical_prefix_compose 20687 621 blank c32 c25
    h20687 houter11' (by simpa [C01Free] using hprefixRoot) hpref11'
  have chain24085 := physical_prefix_compose 21308 2777 blank c25 c53
    chain21308.1 houter25' chain21308.2 hpref25'
  have chain29698 := physical_prefix_compose 24085 5613 blank c53 c184
    chain24085.1 hlow42 chain24085.2 hpreflow42

  obtain ⟨c3, houter0, hrep3, hpref0⟩ :=
    outer_no_fatal_segment 0 0 184 c184 (by simpa using hrep184) (by omega)
  have hcost0 : outerCost 0 0 = 27 := by
    norm_num [outerCost, juncPosFullTime]
  have houter0' : BB6Coverage.run target429 27 c184 = some c3 := by
    simpa [hcost0] using houter0
  have hpref0' : ∀ t : Nat, t ≤ 27 →
      ∃ e : Config, BB6Coverage.run target429 t c184 = some e ∧ C01Free e := by
    simpa [hcost0] using hpref0
  have chain29725 := physical_prefix_compose 29698 27 blank c184 c3
    chain29698.1 houter0' chain29698.2 hpref0'

  obtain ⟨c9, houter3, hrep9, hpref3⟩ :=
    outer_no_fatal_segment 3 0 181 c3 (by simpa using hrep3) (by omega)
  have hcost3 : outerCost 3 0 = 93 := by
    norm_num [outerCost, juncPosFullTime]
  have houter3' : BB6Coverage.run target429 93 c3 = some c9 := by
    simpa [hcost3] using houter3
  have hpref3' : ∀ t : Nat, t ≤ 93 →
      ∃ e : Config, BB6Coverage.run target429 t c3 = some e ∧ C01Free e := by
    simpa [hcost3] using hpref3
  have chain29818 := physical_prefix_compose 29725 93 blank c3 c9
    chain29725.1 houter3' chain29725.2 hpref3'

  obtain ⟨c21, houter9, hrep21, hpref9⟩ :=
    outer_no_fatal_segment 9 0 172 c9 (by simpa using hrep9) (by omega)
  have hcost9 : outerCost 9 0 = 441 := by
    norm_num [outerCost, juncPosFullTime]
  have houter9' : BB6Coverage.run target429 441 c9 = some c21 := by
    simpa [hcost9] using houter9
  have hpref9' : ∀ t : Nat, t ≤ 441 →
      ∃ e : Config, BB6Coverage.run target429 t c9 = some e ∧ C01Free e := by
    simpa [hcost9] using hpref9
  have chain30259 := physical_prefix_compose 29818 441 blank c9 c21
    chain29818.1 houter9' chain29818.2 hpref9'

  obtain ⟨c45p, houter21, hrep45p, hpref21⟩ :=
    outer_no_fatal_segment 21 0 151 c21 (by simpa using hrep21) (by omega)
  have hcost21 : outerCost 21 0 = 2001 := by
    norm_num [outerCost, juncPosFullTime]
  have houter21' : BB6Coverage.run target429 2001 c21 = some c45p := by
    simpa [hcost21] using houter21
  have hpref21' : ∀ t : Nat, t ≤ 2001 →
      ∃ e : Config, BB6Coverage.run target429 t c21 = some e ∧ C01Free e := by
    simpa [hcost21] using hpref21
  have chain32260 := physical_prefix_compose 30259 2001 blank c21 c45p
    chain30259.1 houter21' chain30259.2 hpref21'

  obtain ⟨c93, houter45, hrep93, hpref45⟩ :=
    outer_no_fatal_segment 45 0 106 c45p (by simpa using hrep45p) (by omega)
  have hcost45 : outerCost 45 0 = 8577 := by
    norm_num [outerCost, juncPosFullTime]
  have houter45' : BB6Coverage.run target429 8577 c45p = some c93 := by
    simpa [hcost45] using houter45
  have hpref45' : ∀ t : Nat, t ≤ 8577 →
      ∃ e : Config, BB6Coverage.run target429 t c45p = some e ∧ C01Free e := by
    simpa [hcost45] using hpref45
  have chain40837 := physical_prefix_compose 32260 8577 blank c45p c93
    chain32260.1 houter45' chain32260.2 hpref45'

  obtain ⟨c90, hodd, hrep90, hprefoodd⟩ :=
    lowOdd_v6_n42_no_fatal_physical c93 (by simpa [lowOddV6N42Start] using hrep93)
  have chain42137 := physical_prefix_compose 40837 1300 blank c93 c90
    chain40837.1 hodd chain40837.2 hprefoodd

  obtain ⟨c216, hlow42last, hrep216, hpreflow42last⟩ :=
    low42_j13k38_no_fatal_physical c90 (by simpa [low42J13K38Start] using hrep90)
  have chain43862 := physical_prefix_compose 42137 1725 blank c90 c216
    chain42137.1 hlow42last chain42137.2 hpreflow42last

  exact ⟨c184, c93, c90, c216,
    by simpa using chain29698.1, hrep184,
    by simpa using chain40837.1, hrep93,
    by simpa using chain42137.1, hrep90,
    by simpa using chain43862.1, hrep216,
    chain43862.2⟩

#print axioms low42_j34k9_no_fatal_source
#print axioms lowOdd_v6_n42_no_fatal_source
#print axioms low42_j13k38_no_fatal_source
#print axioms low42_j34k9_no_fatal_physical
#print axioms lowOdd_v6_n42_no_fatal_physical
#print axioms low42_j13k38_no_fatal_physical
#print axioms blank_root_lowEvenR32_to_junc0_216

end BB429LowEvenR32RootExtension
