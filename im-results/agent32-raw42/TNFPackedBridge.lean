import TNFPackedClosed
import TNFClosedCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32PackedBridge
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent50SideCycle
open BB6Coverage.Agent10ZipAudit BB6Coverage.Agent13PackedZipper BB6Coverage.Agent31Pump
open BB6.Agent3PackedCycle BB6.Agent3PackedAudit BB6.Agent32Raw59QuickWeight
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent32PartialCut BB6.Agent8TNFPath
open BB6.Agent32PackedClosed

theorem padEq_complete (xs ys : List Bool) (h : ∀ i, xs.getD i false = ys.getD i false) : padEq xs ys = true := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      have h0 : false = y := h 0
      have H : ∀ i, ([] : List Bool).getD i false = ys.getD i false := fun i => h (i+1)
      simp only [padEq,List.all_cons,← h0,Bool.not_false,Bool.true_and]
      exact ih H
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h0 : x = false := h 0
      simp only [padEq,h0,Bool.not_false,Bool.true_and]
      exact ih [] (fun i => h (i+1))
    | cons y ys =>
      have h0 : x = y := h 0
      simp only [padEq,h0,beq_self_eq_true,Bool.true_and]
      exact ih ys (fun i => h (i+1))

theorem getD_take_ge (xs : List Bool) (n i : Nat) (h : n ≤ i) : (xs.take n).getD i false = false := by
  induction xs generalizing n i with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases i with
      | zero => omega
      | succ i => simpa only [List.take_succ_cons,List.getD_cons_succ] using ih n i (by omega)

theorem pack_mod_padEq {xs ys : List Bool} {k : Nat}
    (h : pack xs % 2^k = pack ys % 2^k) : padEq (xs.take k) (ys.take k) = true := by
  apply padEq_complete
  intro i
  by_cases hi : i < k
  · rw [getD_take_lt _ _ _ hi,getD_take_lt _ _ _ hi]
    exact pack_mod_eq_getD h i hi
  · rw [getD_take_ge _ _ _ (by omega),getD_take_ge _ _ _ (by omega)]

theorem tailH_zip (r : Bool) (b : Int) (c d : Z)
    (h : tailH r b (encH c) (encH d) = true) : zipTailEq r b c d = true := by
  simp only [tailH,encH,encode,Bool.and_eq_true,decide_eq_true_eq] at h
  simp only [zipTailEq,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨of_decide_eq_true h.1.1,of_decide_eq_true h.1.2⟩,?_⟩
  cases r
  · simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true] at h ⊢
    exact ⟨padEq_complete _ _ (pack_eq_getD (of_decide_eq_true h.2.1)),pack_mod_padEq (of_decide_eq_true h.2.2)⟩
  · simp only [ite_true,Bool.and_eq_true] at h ⊢
    exact ⟨pack_mod_padEq (of_decide_eq_true h.2.1),padEq_complete _ _ (pack_eq_getD (of_decide_eq_true h.2.2))⟩

theorem cycleH_zip (p : PartialMachine) (e k : Nat) (r : Bool) (b : Int)
    (h : cycleH p e k r b = true) : zipCycle p e k r b = true := by
  unfold cycleH at h
  rw [show startH = encH start from rfl,← enc_run] at h
  unfold zipCycle
  cases hc : zrun p e start with
  | none => simp [hc] at h
  | some c =>
    simp only [hc,Option.map_some,← enc_window] at h
    cases hd : zipWindow p r b k c with
    | none => simp [hd] at h
    | some d =>
      simpa only [hd] using tailH_zip r b c d (by simpa only [hd,Option.map_some] using h)

theorem packed_zip (B : Nat) (p : PartialMachine) (a : Audit)
    (h : packedCheck B p a = true) : zipCheck B p a = true := by
  induction a generalizing p with
  | last n s =>
    simpa only [packedCheck,packedQueryOK,readRunP_eq,zipQueryOK,zipCheck] using h
  | cycle e k r b =>
    simp only [packedCheck,Bool.and_eq_true] at h
    simp only [zipCheck,Bool.and_eq_true]
    exact ⟨h.1,cycleH_zip _ _ _ _ _ h.2⟩
  | far rev d C => exact h
  | proven q safe => exact h
  | split n s kids ih =>
    simp only [packedCheck,Bool.and_eq_true] at h
    simp only [zipCheck,Bool.and_eq_true]
    refine ⟨?_,allMoves_of _ ?_⟩
    · simpa only [packedQueryOK,readRunP_eq,zipQueryOK] using h.1
    · intro mv; exact ih mv _ (allMoves_sound _ h.2 mv)

theorem packed_closed (B cut : Nat) (p : PartialMachine) (t : Cut)
    (h : BB6.Agent32PackedClosed.closedCheck B cut p t = true) : BB6.Agent32Closed.closedCheck B cut p t = true := by
  induction t generalizing p cut with
  | keep => exact h
  | closed a =>
    simp only [BB6.Agent32PackedClosed.closedCheck,BB6.Agent32PackedClosed.quickLeaf_eq] at h
    simp only [BB6.Agent32Closed.closedCheck,BB6.Agent32Closed.quickLeaf_eq]
    exact packed_zip B p a h
  | split n s kids ih =>
    simp only [BB6.Agent32PackedClosed.closedCheck,Bool.and_eq_true] at h
    simp only [BB6.Agent32Closed.closedCheck,Bool.and_eq_true]
    refine ⟨?_,allMoves_of _ ?_⟩
    · simpa only [quickPackedQuery_eq,quickZipQuery_eq] using h.1
    · intro mv; have hh := allMoves_sound _ h.2 mv
      split
      next he => exact ih mv _ _ (by simpa only [if_pos he] using hh)
      next => rfl
#print axioms packed_closed
end BB6.Agent32PackedBridge
