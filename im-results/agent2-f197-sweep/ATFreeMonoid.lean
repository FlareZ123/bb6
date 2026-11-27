import ATFreeMonoidCore
import ATCostGrowth

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace F197
open Q

/-- First token P=AAT on e deposits u d in 36 primitive live steps;
    first Q=TAT on e deposits u C e in 46 primitive live steps. -/
theorem fmSourceHead (b : Bool) (l : Tape) (hl : l 0 = true) :
    run (fmSrcStep b)
      (other B (fmSourceToken b l)
        (atpRight (pre [true] blank))) =
    some (other B l (fmRightU (fmBase b))) := by
  cases b with
  | false =>
      simpa [fmSrcStep,fmSourceToken,fmRightU,fmBase,
        atpRight,pre] using atc_consume_e l hl
  | true =>
      have he : (pre [true] blank) 0 = true := by rfl
      simpa [fmSrcStep,fmSourceToken,fmRightU,fmBase,
        atpRight,pre] using
        atc_preconsume l (pre [true] blank) hl he

/-- Final base marker d or C e discharges the oldest P or Q marker,
    respectively, at the right terminal e boundary. -/
theorem fmDecodeHead (b : Bool) (l : Tape) (hl : l 0 = true) :
    run (fmBaseDecStep b)
      (other B (atpJ l) (fmRightA (fmBase b))) =
    some
      (other B (fmOutputToken b l)
        (atpRight (pre [true] blank))) := by
  cases b with
  | false =>
      simpa [fmBaseDecStep,fmOutputToken,fmRightA,fmBase,
        atpJ,atpXRight,atpRight,pre] using
        atc_counter_d l hl
  | true =>
      simpa [fmBaseDecStep,fmOutputToken,fmRightA,fmBase,
        atpJ,atpXRight,atpRight,pre] using
        atc_counter_base l hl

/-- All input prefix tokens are consumed before the paired-AAA scanner.
    This holds for every nonempty, arbitrarily mixed P/Q word. -/
theorem fmConsumeWord (b : Bool) (bs : List Bool)
    (l : Tape) (hl : l 0 = true) :
    run (fmSrcStep b + fmSrcCost bs)
      (other B (fmWordIn (b::bs) l)
        (atpRight (pre [true] blank))) =
    some
      (other B l
        (fmRightU (fmMarkers bs (fmBase b)))) := by
  rw [run_add]
  rw [show run (fmSrcStep b)
        (other B (fmWordIn (b::bs) l)
          (atpRight (pre [true] blank))) =
        some (other B (fmWordIn bs l)
          (fmRightU (fmBase b))) by
        simpa [fmWordIn] using
          fmSourceHead b (fmWordIn bs l)
            (fmWordIn_first bs l hl)]
  simp only [Option.bind_some]
  exact fmConsumeRest bs l (fmBase b) hl (fmBase_first b)

/-- All saved markers decode in reverse and restore the output token word
    in the original order, without inspecting any left data suffix. -/
theorem fmDecodeWord (b : Bool) (bs : List Bool)
    (l : Tape) (hl : l 0 = true) :
    run (fmDecCost bs + fmBaseDecStep b)
      (other B (atpJ l)
        (fmRightA (fmMarkers bs (fmBase b)))) =
    some
      (other B (fmWordOut (b::bs) l)
        (atpRight (pre [true] blank))) := by
  rw [run_add, fmDecodeRest bs l (fmBase b) hl (fmBase_first b)]
  simp only [Option.bind_some]
  simpa [fmWordOut] using
    fmDecodeHead b (fmWordOut bs l)
      (fmWordOut_first bs l hl)

/-- Main unbounded free-monoid reset theorem. Every nonempty mixed P/Q
    prefix is transformed blockwise P->P, Q->AAAT, followed by A H(data).
    No first-return hypothesis, finite enumeration or unproved no-halt
    premise appears. The exact primitive source run has type `some`. -/
theorem fmFullFamily (b : Bool) (bs data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run ((fmSrcStep b + fmSrcCost bs) +
      ((atpScanCost data + atpCarryCost data.reverse) +
        (fmDecCost bs + fmBaseDecStep b)))
      (other B
        (fmWordIn (b::bs) (atpSource data l))
        (atpRight (pre [true] blank))) =
    some
      (other B
        (fmWordOut (b::bs) (atpPhi data.reverse l))
        (atpRight (pre [true] blank))) := by
  have hs : (atpSource data l) 0 = true :=
    atpSource_first data l hne
  have hd : data.reverse ≠ [] := by simpa using hne
  let r : Tape := fmMarkers bs (fmBase b)
  have hr : r 0 = true := by
    exact fmMarkers_first bs (fmBase b) (fmBase_first b)
  rw [run_add, fmConsumeWord b bs (atpSource data l) hs]
  simp only [Option.bind_some]
  rw [run_add]
  rw [show run (atpScanCost data + atpCarryCost data.reverse)
        (other B (atpSource data l) (fmRightU r)) =
      some (other B (atpJ (atpPhi data.reverse l)) (fmRightA r)) by
        simpa [fmRightU,fmRightA,atgAccWith] using
          atg_staged data l r hne hl hr]
  simp only [Option.bind_some]
  exact fmDecodeWord b bs (atpPhi data.reverse l)
    (atpPhi_first data.reverse l hd)

/-- The carried data decoder costs 60 steps per data letter,
    plus four per T letter, less an offset 28. -/
theorem fmCarryCost_formula (data : List Bool) (hne : data ≠ []) :
    atpCarryCost data + 28 =
      60 * data.length + 4 * atCountT data := by
  induction data with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
      cases rest with
      | nil => cases c <;> decide
      | cons d ds =>
          have hh : d::ds ≠ [] := by simp
          have h := ih hh
          cases c <;> simp [atpCarryCost,atCountT] at * <;> omega

/-- The P/Q transport and reverse decoder costs add independently:
    68 for each P and 82 for each Q. -/
theorem fmSrcDecBalance (ws : List Bool) :
    fmSrcCost ws + fmDecCost ws =
      68 * ws.length + 14 * fmCountQ ws := by
  induction ws with
  | nil => rfl
  | cons b bs ih =>
      cases b <;>
        simp [fmSrcCost,fmDecCost,fmSrcStep,fmDecStep,fmCountQ] at * <;>
        omega

/-- Closed cost for the free monoid reset family: when |data|=q+1,
    this is 68·#P + 82·#Q + 74 + 68q + 14t. -/
theorem fmCostFormula (b : Bool) (bs data : List Bool)
    (hne : data ≠ []) :
    (fmSrcStep b + fmSrcCost bs) +
      ((atpScanCost data + atpCarryCost data.reverse) +
        (fmDecCost bs + fmBaseDecStep b)) =
    (6 + 68 * data.length + 14 * atCountT data) +
      (68 * (b::bs).length + 14 * fmCountQ (b::bs)) := by
  have hd : data.reverse ≠ [] := by simpa using hne
  have hs := atpScanCost_formula data hne
  have hc := fmCarryCost_formula data.reverse hd
  have hr := atCountT_reverse data
  have hb := fmSrcDecBalance bs
  cases b <;>
    simp [fmSrcStep,fmBaseDecStep,fmCountQ] at * <;>
    omega

/-- Closed-form, kernel-certified exact source run for *any* mixed P/Q
    prefix and arbitrary run-aligned left continuation. -/
theorem fmFullFamilyClosed (b : Bool) (bs data : List Bool) (l : Tape)
    (hne : data ≠ []) (hl : l 0 = true) :
    run ((6 + 68 * data.length + 14 * atCountT data) +
      (68 * (b::bs).length + 14 * fmCountQ (b::bs)))
      (other B
        (fmWordIn (b::bs) (atpSource data l))
        (atpRight (pre [true] blank))) =
    some
      (other B
        (fmWordOut (b::bs) (atpPhi data.reverse l))
        (atpRight (pre [true] blank))) := by
  rw [← fmCostFormula b bs data hne]
  exact fmFullFamily b bs data l hne hl

#print axioms fmSourceHead
#print axioms fmDecodeHead
#print axioms fmConsumeWord
#print axioms fmDecodeWord
#print axioms fmFullFamily
#print axioms fmCostFormula
#print axioms fmFullFamilyClosed

end F197
