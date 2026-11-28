import CanonicalPrefixFast
import Raw36Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100WeightedSplit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47CanonicalFrontier BB6.Agent29FastZipWeight BB6.Agent19CanonicalPartial

theorem splitBound (B : Nat) (p : PartialMachine) (cut n : Nat) (s : Slot)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hq : fastQueryOK B p n s = true)
    (children : ∀ mv, mv.next.val ≤ cut → ∀ m, compatible (refine p s (some mv)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound ((fastQueryOK_eq B p n s).symm.trans hq)
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hsc : readSlot c = s := by simpa [hr] using hread
    have hslot : s.1.val < cut := by
      rw [← hsc]
      exact knownRun_support p cut hcut hs n c hr
    have hh : ∀ m, compatible (refine p s none) m → WeightedBound B m := by
      simpa only [hsc] using first_hole_weighted_halt B p n c hf hr (by simpa only [hsc] using hhole)
        (by simpa only [hsc] using weightOK_sound p s n B hw)
    intro m hm
    rcases tnf_branch_frontier B cut p s hcut hs hhole hslot hf hh m (compatible_quotient hm) with hb | ⟨mv,hv,hqc⟩
    · exact hb
    · exact quotientSafe (refine_preserves_firstOne p s (some mv) hhole hf) (children mv hv) m hqc

/-- Exact table transport for externally proved weighted bounds. -/
theorem externalBound (B C : Nat) (p q : PartialMachine)
    (hle : C ≤ B) (he : tableOK p q = true)
    (safe : ∀ m, compatible q m → WeightedBound C m) :
    ∀ m, compatible p m → WeightedBound B m := by
  rw [tableOK_sound p q he]
  intro m hm k d hk hd
  exact Nat.le_trans (safe m hm k d hk hd) hle

/-- No assigned halt checker used at literal chunk roots. -/
def nohaltOK (p : PartialMachine) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun b => !(p (q,b) == some none)

theorem nohaltOK_sound (p : PartialMachine) (h : nohaltOK p = true) : weightedTNFNoAssignedHalt p := by
  intro ⟨q,b⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have he := List.all_eq_true.mp hq b hb
  simpa using he

/-- A conventional closed audit chunk at an exact source table. -/
theorem chunkBound (B : Nat) (p : PartialMachine) (cut : Nat) (a : Audit)
    (hcut : 0 < cut) (hs : supportOK p cut = true)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : nohaltOK p = true)
    (hc : BB6.Agent29CanonicalPrefix.prefixCheck B p cut a = true) :
    ∀ m, compatible p m → WeightedBound B m :=
  BB6.Agent29CanonicalFast.bound B p cut a hcut (supportOK_sound _ _ hs) hf (nohaltOK_sound _ hno)
    ((BB6.Agent29CanonicalPrefix.prefixCheck_eq B p cut a).symm.trans hc)

/-- Compose ordinary audit chunks and arbitrary external bound theorems. -/
theorem splitBound24 (B : Nat) (p : PartialMachine) (cut n : Nat) (s : Slot)
    (hcut : 0 < cut) (hs : supportOK p cut = true)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hq : fastQueryOK B p n s = true)
    (h00 : if 0 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,false,0⟩)) m → WeightedBound B m else True)
    (h01 : if 1 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,false,1⟩)) m → WeightedBound B m else True)
    (h02 : if 2 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,false,2⟩)) m → WeightedBound B m else True)
    (h03 : if 3 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,false,3⟩)) m → WeightedBound B m else True)
    (h04 : if 4 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,false,4⟩)) m → WeightedBound B m else True)
    (h05 : if 5 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,false,5⟩)) m → WeightedBound B m else True)
    (h06 : if 0 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,true,0⟩)) m → WeightedBound B m else True)
    (h07 : if 1 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,true,1⟩)) m → WeightedBound B m else True)
    (h08 : if 2 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,true,2⟩)) m → WeightedBound B m else True)
    (h09 : if 3 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,true,3⟩)) m → WeightedBound B m else True)
    (h10 : if 4 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,true,4⟩)) m → WeightedBound B m else True)
    (h11 : if 5 ≤ cut then ∀ m, compatible (refine p s (some ⟨false,true,5⟩)) m → WeightedBound B m else True)
    (h12 : if 0 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,false,0⟩)) m → WeightedBound B m else True)
    (h13 : if 1 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,false,1⟩)) m → WeightedBound B m else True)
    (h14 : if 2 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,false,2⟩)) m → WeightedBound B m else True)
    (h15 : if 3 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,false,3⟩)) m → WeightedBound B m else True)
    (h16 : if 4 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,false,4⟩)) m → WeightedBound B m else True)
    (h17 : if 5 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,false,5⟩)) m → WeightedBound B m else True)
    (h18 : if 0 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,true,0⟩)) m → WeightedBound B m else True)
    (h19 : if 1 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,true,1⟩)) m → WeightedBound B m else True)
    (h20 : if 2 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,true,2⟩)) m → WeightedBound B m else True)
    (h21 : if 3 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,true,3⟩)) m → WeightedBound B m else True)
    (h22 : if 4 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,true,4⟩)) m → WeightedBound B m else True)
    (h23 : if 5 ≤ cut then ∀ m, compatible (refine p s (some ⟨true,true,5⟩)) m → WeightedBound B m else True)
    : ∀ m, compatible p m → WeightedBound B m := by
  apply splitBound B p cut n s hcut (supportOK_sound _ _ hs) hf hq
  intro ⟨w,r,q⟩ hv
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq' with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · simpa only [if_pos (show 0 ≤ cut from hv)] using h00
  · simpa only [if_pos (show 0 ≤ cut from hv)] using h06
  · simpa only [if_pos (show 0 ≤ cut from hv)] using h12
  · simpa only [if_pos (show 0 ≤ cut from hv)] using h18
  · simpa only [if_pos (show 1 ≤ cut from hv)] using h01
  · simpa only [if_pos (show 1 ≤ cut from hv)] using h07
  · simpa only [if_pos (show 1 ≤ cut from hv)] using h13
  · simpa only [if_pos (show 1 ≤ cut from hv)] using h19
  · simpa only [if_pos (show 2 ≤ cut from hv)] using h02
  · simpa only [if_pos (show 2 ≤ cut from hv)] using h08
  · simpa only [if_pos (show 2 ≤ cut from hv)] using h14
  · simpa only [if_pos (show 2 ≤ cut from hv)] using h20
  · simpa only [if_pos (show 3 ≤ cut from hv)] using h03
  · simpa only [if_pos (show 3 ≤ cut from hv)] using h09
  · simpa only [if_pos (show 3 ≤ cut from hv)] using h15
  · simpa only [if_pos (show 3 ≤ cut from hv)] using h21
  · simpa only [if_pos (show 4 ≤ cut from hv)] using h04
  · simpa only [if_pos (show 4 ≤ cut from hv)] using h10
  · simpa only [if_pos (show 4 ≤ cut from hv)] using h16
  · simpa only [if_pos (show 4 ≤ cut from hv)] using h22
  · simpa only [if_pos (show 5 ≤ cut from hv)] using h05
  · simpa only [if_pos (show 5 ≤ cut from hv)] using h11
  · simpa only [if_pos (show 5 ≤ cut from hv)] using h17
  · simpa only [if_pos (show 5 ≤ cut from hv)] using h23

#print axioms splitBound24
#print axioms externalBound
#print axioms chunkBound
end BB6.Agent7D100WeightedSplit
