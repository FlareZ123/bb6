import CachedPhaseTree
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent47HistoryPhaseTree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree BB6.Agent1NGram
open BB6Coverage.Agent13PackedZipper BB6.Agent3PackedCycle BB6.Agent48PackedPrefix
open BB6Coverage.Agent50SideCycle BB6Coverage.Agent10ZipAudit

/-- Reverse exact primitive history, indexed by the time elapsed from blank. -/
def Valid (p : PartialMachine) (t : Nat) (xs : List H) : Prop :=
  ∀ i ≤ t, runH p i startH = some (xs.getD (t-i) startH)

theorem head_valid {p t xs} (h : Valid p t xs) : runH p t startH = some (xs.headD startH) := by
  have hv := h t (Nat.le_refl _)
  simp only [Nat.sub_self] at hv
  cases xs <;> exact hv

theorem valid_start (p : PartialMachine) : Valid p 0 [startH] := by
  intro i hi
  have he : i = 0 := by omega
  subst i
  rfl

theorem push_valid {p t xs z} (hv : Valid p t xs) (hs : stepH p (xs.headD startH) = some z) :
    Valid p (t+1) (z::xs) := by
  intro i hi
  by_cases he : i = t+1
  · subst i
    rw [runH_add,head_valid hv]
    simp only [runH,hs,Option.bind_some,Nat.sub_self]
    rfl
  · have hi' : i ≤ t := by omega
    rw [show t+1-i = (t-i)+1 by omega]
    exact hv i hi'

def extend (p : PartialMachine) : Nat → List H → Option (List H)
  | 0, xs => some xs
  | n+1, xs => (stepH p (xs.headD startH)).bind fun z => extend p n (z::xs)

theorem extend_valid {p t xs n ys} (hv : Valid p t xs) (he : extend p n xs = some ys) :
    Valid p (t+n) ys := by
  induction n generalizing t xs with
  | zero =>
    have e : xs = ys := Option.some.inj he
    subst ys
    exact hv
  | succ n ih =>
    cases hs : stepH p (xs.headD startH) with
    | none =>
      simp only [extend,hs,Option.bind_none] at he
      contradiction
    | some z =>
      have ht : extend p n (z::xs) = some ys := by simpa only [extend,hs,Option.bind_some] using he
      have H := ih (t:=t+1) (push_valid hv hs) ht
      simpa only [show t+1+n=t+(n+1) by omega] using H

def advance (p : PartialMachine) (t : Nat) (xs : List H) (n : Nat) : Option (List H) :=
  if t ≤ n then extend p (n-t) xs else none

theorem advance_valid {p t xs n ys} (hv : Valid p t xs) (he : advance p t xs n = some ys) : Valid p n ys := by
  unfold advance at he
  split at he
  · rename_i hle
    have H := extend_valid hv he
    simpa only [show t+(n-t)=n by omega] using H
  · contradiction

theorem refine_valid {p t xs s mv} (hv : Valid p t xs) (hu : p s = none) :
    Valid (refine p s (some mv)) t xs := by
  intro i hi
  exact refineRunH p s mv hu i startH _ (hv i hi)

theorem window_of_run {p right boundary n z d} (hr : runH p n z = some d)
    (hw : ∀ j < n, ∀ y, runH p j z = some y → side right boundary y.h) :
    windowH p right boundary n z = some d := by
  induction n generalizing z with
  | zero => exact hr
  | succ n ih =>
    have hhead := hw 0 (by omega) z rfl
    cases hs : stepH p z with
    | none => simp [runH,hs] at hr
    | some c =>
      have ht : runH p n c = some d := by simpa only [runH,hs,Option.bind_some] using hr
      have hrest := ih ht (fun j hj y hy => hw (j+1) (by omega) y (by simpa only [runH,hs,Option.bind_some] using hy))
      simpa only [windowH,hhead,ite_true,hs,Option.bind_some] using hrest

def cycle (p : PartialMachine) (t : Nat) (xs : List H) (e k : Nat) (r : Bool) (b : Int) : Bool :=
  match advance p t xs (e+k) with
  | none => false
  | some ys => tailH r b (ys.getD k startH) (ys.headD startH) &&
      (List.range k).all (fun j => decide (side r b (ys.getD (k-j) startH).h))

theorem cycle_sound {p t xs e k r b} (hv : Valid p t xs) (hk : 0 < k)
    (hc : cycle p t xs e k r b = true) : ∀ m, compatible p m → NeverHalts m := by
  unfold cycle at hc
  cases ha : advance p t xs (e+k) with
  | none => simp [ha] at hc
  | some ys =>
    simp only [ha,Bool.and_eq_true] at hc
    have hy := advance_valid hv ha
    let c := ys.getD k startH
    let d := ys.headD startH
    have he : runH p e startH = some c := by
      have H := hy e (by omega)
      simpa only [show e+k-e=k by omega] using H
    have hd : runH p (e+k) startH = some d := head_valid hy
    rw [runH_add,he,Option.bind_some] at hd
    have hw : ∀ j < k, ∀ z, runH p j c = some z → side r b z.h := by
      intro j hj z hz
      have hrun := hy (e+j) (by omega)
      rw [runH_add,he,Option.bind_some,hz] at hrun
      have heq : z = ys.getD (k-j) startH := by
        exact Option.some.inj (by simpa only [show e+k-(e+j)=k-j by omega] using hrun)
      rw [heq]
      exact of_decide_eq_true (List.all_eq_true.mp hc.2 j (List.mem_range.mpr hj))
    have hwindow := window_of_run hd hw
    apply cycleH_sound p e k r b hk
    simp only [cycleH,he,hwindow]
    exact hc.1

/-- All prefix cells survive refinement at an unqueried row. A cycle leaf
    checks only the remaining primitive steps and reads the retained interval
    directly from the authenticated history. -/
def check (B : Nat) (p : PartialMachine) (t : Nat) (xs : List H) : Tree → Bool
  | .bad => false
  | .side e n r b => decide (0 < n) && cycle p t xs e n r b
  | .automata a => BB6.Agent4Automata.check p a
  | .last n s =>
    match advance p t xs n with
    | none => false
    | some ys => BB6.Agent5CachedPhaseTree.query B p n s (ys.headD startH) && BB6.Agent50TNFPilot.restOK p s
  | .split n s cut kids =>
    match advance p t xs n with
    | none => false
    | some ys =>
      BB6.Agent5CachedPhaseTree.query B p n s (ys.headD startH) && decide (0 < cut) && supportOK p cut &&
      (List.finRange 6).all (fun q => if q.val ≤ cut then bits.all (fun w => bits.all (fun r =>
        check B (refine p s (some ⟨w,r,q⟩)) n ys (kids ⟨w,r,q⟩))) else true)
termination_by structural a => a

theorem soundAt (B : Nat) (p : PartialMachine) (t : Nat) (xs : List H) (a : Tree)
    (hv : Valid p t xs) (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hc : check B p t xs a = true) : ∀ m, compatible p m → WeightedBound B m := by
  induction a generalizing p t xs with
  | bad => simp [check] at hc
  | side e n r b =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact fun m hm => weighted_never B m (cycle_sound hv hc.1 hc.2 m hm)
  | automata a => exact fun m hm => weighted_never B m (BB6.Agent4Automata.never p a hc m hm)
  | last n s =>
    simp only [check] at hc
    cases h : advance p t xs n with
    | none => simp [h] at hc
    | some ys =>
      have hy := advance_valid hv h
      simp only [h,BB6.Agent5CachedPhaseTree.query_eq B p n s _ (head_valid hy),Bool.and_eq_true] at hc
      exact BB6.Agent5FastPhaseTree.sound B p (.last n s) hf (by
        simp only [BB6.Agent5FastPhaseTree.check,Bool.and_eq_true]; exact hc)
  | split n s cut kids ih =>
    simp only [check] at hc
    cases h : advance p t xs n with
    | none => simp [h] at hc
    | some ys =>
      have hy := advance_valid hv h
      simp only [h,BB6.Agent5CachedPhaseTree.query_eq B p n s _ (head_valid hy),Bool.and_eq_true,decide_eq_true_eq] at hc
      have hu : p s = none := by
        have hq := hc.1.1.1
        simp only [BB6.Agent5FastPhaseTree.firstOK,Bool.and_eq_true,decide_eq_true_eq] at hq
        exact hq.1.2
      apply BB6.Agent5FastPhaseTree.splitFast B p n s cut hf hc.1.1.1 hc.1.1.2 hc.1.2
      intro mv hm
      rcases mv with ⟨w,r,q⟩
      apply ih ⟨w,r,q⟩ _ n ys (refine_valid hy hu) (refine_preserves_firstOne p s (some ⟨w,r,q⟩) hu hf)
      have H := List.all_eq_true.mp hc.2 q (mem_states q)
      simp only [hm,ite_true] at H
      exact List.all_eq_true.mp (List.all_eq_true.mp H w (mem_bits w)) r (mem_bits r)

def rootCheck (B : Nat) (p : PartialMachine) (a : Tree) : Bool := check B p 0 [startH] a

theorem sound (B : Nat) (p : PartialMachine) (a : Tree)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hc : rootCheck B p a = true) :
    ∀ m, compatible p m → WeightedBound B m := soundAt B p 0 [startH] a (valid_start p) hf hc

#print axioms sound
end BB6.Agent47HistoryPhaseTree
