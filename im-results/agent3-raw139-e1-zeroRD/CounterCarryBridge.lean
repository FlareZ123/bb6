import CounterCarry
import FastThreeHoleAudit

namespace BB6.Agent3CounterCarry
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open CounterCarry (C Ray cons tail table Variant)

def codes : Variant → List Nat
  | .d0 => [7,12,11,14,14,5,0,16,20,13,24,13]
  | .b1 => [7,12,11,14,14,5,0,16,20,13,24,7]
  | .d1 => [7,12,11,14,14,5,0,16,22,13,24,15]

def ctr (v : Variant) : PartialMachine := fromCodes (codes v)

def tableMove (v : Variant) (s : Slot) : Option Move := (table v s.1 s.2).map fun (w,d,q) => ⟨w,d,q⟩

theorem table_match (v : Variant) (s : Slot) : ctr v s = (tableMove v s).map some := by
  rcases s with ⟨q,b⟩
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h | h | h <;> subst q <;> cases b <;> cases v <;> rfl

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

theorem step_eq (v : Variant) (c : C) : CounterCarry.step v c = (tableMove v (c.q,c.r 0)).map (fun mv => moveC mv c) := by
  unfold CounterCarry.step tableMove moveC
  cases ht : table v c.q (c.r 0) with
  | none => rfl
  | some v => rcases v with ⟨w,d,q⟩; rfl

theorem step_sound (v : Variant) (m : Machine) (hm : compatible (ctr v) m) (c : Config) (d : C)
    (hs : CounterCarry.step v (observe c) = some d) :
    ∃ c', rawStep m c = some c' ∧ observe c' = d := by
  rw [step_eq,(observed_slot c).1,(observed_slot c).2] at hs
  change (tableMove v (readSlot c)).map (fun mv => moveC mv (observe c)) = some d at hs
  cases ht : tableMove (readSlot c) with
  | none => simp [ht] at hs
  | some mv =>
    have hctr : ctr v (readSlot c) = some (some mv) := by rw [table_match,ht]; rfl
    have hmv := hm _ _ hctr
    refine ⟨applyMove c mv, ?_, ?_⟩
    · simp [rawStep,hmv]
    · rw [observe_move]
      simpa [ht] using hs

theorem run_sound (v : Variant) (m : Machine) (hm : compatible (ctr v) m) (n : Nat) (c : Config) (d : C)
    (hs : CounterCarry.run v n (observe c) = some d) :
    ∃ c', BB6Coverage.run m n c = some c' ∧ observe c' = d := by
  induction n generalizing c with
  | zero => exact ⟨c,rfl,Option.some.inj hs⟩
  | succ n ih =>
    cases ht : CounterCarry.step (observe c) with
    | none => simp [CounterCarry.run,ht] at hs
    | some e =>
      obtain ⟨c',hc',he⟩ := step_sound v m hm c e ht
      have hh : CounterCarry.run v n (observe c') = some d := by
        rw [he]; simpa [CounterCarry.run,ht] using hs
      obtain ⟨c'',hc'',hd⟩ := ih c' hh
      refine ⟨c'',?_,hd⟩
      rw [show n+1=1+n by omega, BB6Coverage.run_append]
      have h1 : BB6Coverage.run m 1 c = some c' := by simpa [BB6Coverage.run] using hc'
      rw [h1]; exact hc''

theorem never (v : Variant) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m := by
  intro n
  obtain ⟨d,hd⟩ := CounterCarry.never v n
  have hb : observe blank = CounterCarry.blankC := rfl
  rw [← hb] at hd
  obtain ⟨c,hc,_⟩ := run_sound v m hm n blank d hd
  change (BB6Coverage.run m n blank).isSome = true
  rw [hc]; rfl

theorem weighted (v : Variant) (B : Nat) : Cover (WeightedBound B) (ctr v) := by
  apply Cover.leaf
  intro m hm k d hk hd
  have h := never v m hm (k+1)
  change (BB6Coverage.run m (k+1) blank).isSome = true at h
  rw [hk.2] at h
  contradiction

-- Separate theorem aliases retain the exact table identity in the audit tree.
def ctr210 := ctr .d0
def ctr251 := ctr .b1
def ctr657 := ctr .d1
theorem never210 : ∀ m, compatible ctr210 m → NeverHalts m := never .d0
theorem never251 : ∀ m, compatible ctr251 m → NeverHalts m := never .b1
theorem never657 : ∀ m, compatible ctr657 m → NeverHalts m := never .d1

#print axioms table_match
#print axioms observe_move
#print axioms never
#print axioms weighted
end BB6.Agent3CounterCarry
