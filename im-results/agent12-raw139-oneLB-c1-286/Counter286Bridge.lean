import Counter286
import FastThreeHoleAudit

namespace BB6.Agent12Counter286
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open Counter286 (C Ray cons tail table)

def ctr : PartialMachine := fromCodes [7,21,11,13,14,1,24,16,6,11,16,11]

def tableMove (s : Slot) : Option Move := (table s.1 s.2).map fun (w,d,q) => ⟨w,d,q⟩

theorem table_match (s : Slot) : ctr s = (tableMove s).map some := by
  rcases s with ⟨q,b⟩
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h | h | h <;> subst q <;> cases b <;> rfl

-- Observe the physical tape relative to its head, with no loss of a read bit.
def observe (c : Config) : C := ⟨c.state,
  fun n => c.tape (c.head - (n : Int) - 1),
  fun n => c.tape (c.head + (n : Int))⟩

def moveC (mv : Move) (c : C) : C :=
  if mv.right then ⟨mv.next, cons mv.write c.l, tail c.r⟩
  else ⟨mv.next, tail c.l, cons (c.l 0) (cons mv.write (tail c.r))⟩

theorem observe_move (mv : Move) (c : Config) :
    observe (applyMove c mv) = moveC mv (observe c) := by
  rcases mv with ⟨w,d,q⟩
  cases d with
  | false =>
    simp only [observe,applyMove,moveC,Bool.false_eq_true,ite_false]
    congr 1
    · funext n
      simp only [tail]
      split
      · omega
      · congr 1; omega
    · funext n
      cases n with
      | zero =>
        simp only [cons]
        split
        · omega
        · congr 1; omega
      | succ n =>
        cases n with
        | zero =>
          simp only [cons]
          split
          · rfl
          · omega
        | succ n =>
          simp only [cons,tail]
          split
          · omega
          · congr 1; omega
  | true =>
    simp only [observe,applyMove,moveC,ite_true]
    congr 1
    · funext n
      cases n with
      | zero =>
        simp only [cons]
        split
        · rfl
        · omega
      | succ n =>
        simp only [cons]
        split
        · omega
        · congr 1; omega
    · funext n
      simp only [tail]
      split
      · omega
      · congr 1; omega

theorem observed_slot (c : Config) : (observe c).q = c.state ∧ (observe c).r 0 = c.tape c.head := by
  constructor
  · rfl
  · simp [observe]

theorem step_eq (c : C) : Counter286.step c = (tableMove (c.q,c.r 0)).map (fun mv => moveC mv c) := by
  unfold Counter286.step tableMove moveC
  cases ht : table c.q (c.r 0) with
  | none => rfl
  | some v => rcases v with ⟨w,d,q⟩; rfl

theorem step_sound (m : Machine) (hm : compatible ctr m) (c : Config) (d : C)
    (hs : Counter286.step (observe c) = some d) :
    ∃ c', rawStep m c = some c' ∧ observe c' = d := by
  rw [step_eq,(observed_slot c).1,(observed_slot c).2] at hs
  change (tableMove (readSlot c)).map (fun mv => moveC mv (observe c)) = some d at hs
  cases ht : tableMove (readSlot c) with
  | none => simp [ht] at hs
  | some mv =>
    have hctr : ctr (readSlot c) = some (some mv) := by rw [table_match,ht]; rfl
    have hmv := hm _ _ hctr
    refine ⟨applyMove c mv, ?_, ?_⟩
    · simp [rawStep,hmv]
    · rw [observe_move]
      simpa [ht] using hs

theorem run_sound (m : Machine) (hm : compatible ctr m) (n : Nat) (c : Config) (d : C)
    (hs : Counter286.run n (observe c) = some d) :
    ∃ c', BB6Coverage.run m n c = some c' ∧ observe c' = d := by
  induction n generalizing c with
  | zero => exact ⟨c,rfl,Option.some.inj hs⟩
  | succ n ih =>
    cases ht : Counter286.step (observe c) with
    | none => simp [Counter286.run,ht] at hs
    | some e =>
      obtain ⟨c',hc',he⟩ := step_sound m hm c e ht
      have hh : Counter286.run n (observe c') = some d := by
        rw [he]; simpa [Counter286.run,ht] using hs
      obtain ⟨c'',hc'',hd⟩ := ih c' hh
      refine ⟨c'',?_,hd⟩
      rw [show n+1=1+n by omega, BB6Coverage.run_append]
      have h1 : BB6Coverage.run m 1 c = some c' := by simpa [BB6Coverage.run] using hc'
      rw [h1]; exact hc''

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  intro n
  obtain ⟨d,hd⟩ := Counter286.never n
  have hb : observe blank = Counter286.blankC := rfl
  rw [← hb] at hd
  obtain ⟨c,hc,_⟩ := run_sound m hm n blank d hd
  change (BB6Coverage.run m n blank).isSome = true
  rw [hc]; rfl

theorem weighted (B : Nat) : Cover (WeightedBound B) ctr := by
  apply Cover.leaf
  intro m hm k d hk hd
  have h := never m hm (k+1)
  change (BB6Coverage.run m (k+1) blank).isSome = true at h
  rw [hk.2] at h
  contradiction

#print axioms table_match
#print axioms observe_move
#print axioms never
#print axioms weighted
end BB6.Agent12Counter286
