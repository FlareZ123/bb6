import RootJunc136To45
import LowEvenR32NoFatal
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429LowEvenR32RootChain

open BB6Coverage BB429PhysicalBridge
open BB429RootJunc136To45 BB429LowEvenR32

/-- The authentic blank-root execution reaches the concrete prepared
    low-even r=32 input Junc(45,0,58) after 16,280 primitive steps, then
    follows its exact 4,407-step no-fatal continuation to Junc(11,0,146).
    Every physical prefix through step 20,687 excludes the original
    C/01 halting gateway. This is a finite root-prefix theorem, not an
    all-time nonhalting result. -/
theorem blank_root_lowEvenR32_to_junc11_146 :
    ∃ c0 c45 cEnd : Config,
      BB6Coverage.run target429 13718 blank = some c0 ∧
      Represents rootJunc136 c0 ∧
      BB6Coverage.run target429 16280 blank = some c45 ∧
      Represents rootJunc45 c45 ∧
      BB6Coverage.run target429 20687 blank = some cEnd ∧
      Represents lowEvenEnd cEnd ∧
      cEnd.head = c45.head - 81 ∧
      (∀ t : Nat, t ≤ 20687 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) ∧
      (∀ t : Nat, t ≤ 2562 →
        ∃ e : Config,
          BB6Coverage.run target429 (13718+t) blank = some e ∧
          e.head < c0.head + (139 : Int)) ∧
      c45.head + (61 : Int) = c0.head + (139 : Int) := by
  obtain ⟨c0, c45, hroot, hrep0, hroot45, hrep45,
      hprefixRoot, hfrontRoot, hfrontEnd⟩ :=
    blank_root_no_fatal_to_junc45
  have hrepStart : Represents lowEvenStart c45 := by
    simpa [rootJunc45, lowEvenStart] using hrep45
  obtain ⟨cEnd, htail, hrepEnd, hhead, hprefixTail⟩ :=
    blank_root_lowEvenR32_no_fatal 16280 c45 hroot45 hrepStart
  have htime : 16280 + 4407 = 20687 := by omega
  have htotal : BB6Coverage.run target429 20687 blank = some cEnd := by
    simpa [htime] using htail
  have hprefix :
      ∀ t : Nat, t ≤ 20687 →
        ∃ e : Config,
          BB6Coverage.run target429 t blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true) := by
    intro t ht
    by_cases hfirst : t ≤ 16280
    · exact hprefixRoot t hfirst
    · let s : Nat := t - 16280
      have hs : s ≤ 4407 := by dsimp [s]; omega
      obtain ⟨e, he, hsafe⟩ := hprefixTail s hs
      have htime' : t = 16280 + s := by dsimp [s]; omega
      exact ⟨e, by simpa [htime'] using he, hsafe⟩
  exact ⟨c0, c45, cEnd, hroot, hrep0, hroot45, hrep45,
    htotal, hrepEnd, hhead, hprefix, hfrontRoot, hfrontEnd⟩

#print axioms blank_root_lowEvenR32_to_junc11_146

end BB429LowEvenR32RootChain
