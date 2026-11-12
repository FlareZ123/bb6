import ChampionRootBridge

/-!
# Bounded bitset simulation of the TM2 blank-root prefix

The finite tape uses bits 0..237 for absolute cells -10..227, with the
head offset by 10. bStep rejects moves outside this window. The embedB
simulation theorem proves every successful bounded step agrees with the
infinite-tape rawStep. The final 27,959-step computation is checked by
kernel reduction with decide.
-/
namespace BB6Coverage.Agent42InitialS1Bits
open BB6Coverage
open BB6Coverage.Agent48Champion

structure BConfig where
  state : Fin 6
  head : Nat
  tape : Nat
  deriving DecidableEq, Repr

def writeTape (tape head : Nat) (w : Bool) : Nat :=
  if w then Nat.lor tape (2^head)
  else if Nat.testBit tape head then Nat.xor tape (2^head) else tape

theorem testBit_writeTape (tape head j : Nat) (w : Bool) :
    Nat.testBit (writeTape tape head w) j =
      if j = head then w else Nat.testBit tape j := by
  unfold writeTape
  by_cases hj : j = head
  · subst j
    cases w <;> by_cases hb : Nat.testBit tape head <;>
      simp [hb, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  · have hbit : Nat.testBit (2^head) j = false := by
      rw [Nat.testBit_two_pow]
      simp [Ne.symm hj]
    have hself : Nat.testBit (2^head) head = true := by
      rw [Nat.testBit_two_pow]
      simp
    by_cases hb : Nat.testBit tape head
    · cases w <;> simp [hj, hb, hbit, hself, Nat.testBit_or, Nat.testBit_xor]
    · cases w <;> simp [hj, hb, hbit, hself, Nat.testBit_or, Nat.testBit_xor]

def bMove (c : BConfig) (t : Move) : BConfig :=
  { state := t.next
    head := if t.right then c.head+1 else c.head-1
    tape := writeTape c.tape c.head t.write }

def bStep (m : Machine) (c : BConfig) : Option BConfig :=
  if c.head < 238 then
    match m (c.state, Nat.testBit c.tape c.head) with
    | none => none
    | some t =>
      let h' := if t.right then c.head+1 else c.head-1
      if h' < 238 && (t.right || 0 < c.head) then some (bMove c t) else none
  else none

def bRun (m : Machine) : Nat → BConfig → Option BConfig
  | 0, c => some c
  | n+1, c => (bRun m n c).bind (bStep m)

def embedB (c : BConfig) : Config :=
  { state := c.state
    head := (c.head : Int) - 10
    tape := fun x =>
      if -10 ≤ x then
        Nat.testBit c.tape (Int.toNat (x+10))
      else false }

theorem embedB_head_read (c : BConfig) (hc : c.head < 238) :
    readSlot (embedB c) = (c.state, Nat.testBit c.tape c.head) := by
  have hrange : -10 ≤ (c.head:Int)-10 := by omega
  have hidx : Int.toNat ((c.head:Int)-10+10) = c.head := by omega
  simp [readSlot, embedB, hrange, hidx]

theorem embedB_move (c : BConfig) (t : Move)
    (hc : c.head < 238)
    (hmove : t.right = true ∨ 0 < c.head) :
    embedB (bMove c t) = applyMove (embedB c) t := by
  cases c with
  | mk s h tape =>
    have hc' : h < 238 := by simpa using hc
    cases t with
    | mk w r q =>
      cases r
      · have hpos : 0 < h := by simpa using hmove
        have hhead : ((h-1 : Nat) : Int)-10 = (h:Int)-10-1 := by omega
        simp only [embedB, bMove, applyMove, Bool.false_eq_true, if_false]
        rw [hhead]
        apply congrArg (fun f : Int → Bool => Config.mk q ((h:Int)-10-1) f)
        funext x
        by_cases hx : -10 ≤ x
        · have hidxnonneg : 0 ≤ x+10 := by omega
          have hcast : ((Int.toNat (x+10) : Nat) : Int) = x+10 :=
            Int.toNat_of_nonneg hidxnonneg
          by_cases heq : x = (h:Int)-10
          · subst x
            have hidx : Int.toNat ((h:Int)-10+10) = h := by omega
            simp [hx,hidx,testBit_writeTape]
          · have hidxne : Int.toNat (x+10) ≠ h := by
              intro hh
              have hcast' : ((Int.toNat (x+10) : Nat) : Int) = h := congrArg Int.ofNat hh
              rw [hcast] at hcast'
              omega
            simp [hx,heq,hidxne,testBit_writeTape]
        · have heq : x ≠ (h:Int)-10 := by omega
          simp [hx,heq]
      · have hhead : ((h+1 : Nat) : Int)-10 = (h:Int)-10+1 := by omega
        simp only [embedB, bMove, applyMove, if_true]
        rw [hhead]
        apply congrArg (fun f : Int → Bool => Config.mk q ((h:Int)-10+1) f)
        funext x
        by_cases hx : -10 ≤ x
        · have hidxnonneg : 0 ≤ x+10 := by omega
          have hcast : ((Int.toNat (x+10) : Nat) : Int) = x+10 :=
            Int.toNat_of_nonneg hidxnonneg
          by_cases heq : x = (h:Int)-10
          · subst x
            have hidx : Int.toNat ((h:Int)-10+10) = h := by omega
            simp [hx,hidx,testBit_writeTape]
          · have hidxne : Int.toNat (x+10) ≠ h := by
              intro hh
              have hcast' : ((Int.toNat (x+10) : Nat) : Int) = h := congrArg Int.ofNat hh
              rw [hcast] at hcast'
              omega
            simp [hx,heq,hidxne,testBit_writeTape]
        · have heq : x ≠ (h:Int)-10 := by omega
          simp [hx,heq]

theorem bStep_sound (m : Machine) (c d : BConfig)
    (h : bStep m c = some d) :
    rawStep m (embedB c) = some (embedB d) := by
  have hc : c.head < 238 := by
    by_cases hbound : c.head < 238
    · exact hbound
    · simp [bStep, hbound] at h
  simp only [bStep, if_pos hc] at h
  cases htr : m (c.state, Nat.testBit c.tape c.head) with
  | none => simp [htr] at h
  | some t =>
    have hstep : (if (if t.right then c.head+1 else c.head-1) < 238 &&
        (t.right || 0 < c.head) then some (bMove c t) else none) = some d := by
      simpa [htr] using h
    by_cases hcond :
        (decide ((if t.right then c.head+1 else c.head-1) < 238) &&
          (t.right || decide (0 < c.head))) = true
    · have hd : d = bMove c t := by
        simp [hcond] at hstep
        exact hstep.symm
      subst d
      have hmove : t.right = true ∨ 0 < c.head := by
        by_cases hr : t.right = true
        · exact Or.inl hr
        · right
          have hparts := Bool.and_eq_true_iff.mp hcond
          have hor := Bool.or_eq_true_iff.mp hparts.2
          rcases hor with hright | hpos
          · contradiction
          · exact of_decide_eq_true hpos
      have hm := embedB_move c t hc hmove
      simp [rawStep, embedB_head_read c hc, htr, hm]
    · simp [hcond] at hstep

theorem bRun_sound (m : Machine) (n : Nat) (c d : BConfig)
    (h : bRun m n c = some d) :
    run m n (embedB c) = some (embedB d) := by
  induction n generalizing c d with
  | zero =>
    simp [bRun] at h
    subst d
    rfl
  | succ n ih =>
    simp only [bRun] at h
    cases hr : bRun m n c with
    | none => simp [hr] at h
    | some mid =>
      have hstep : bStep m mid = some d := by simpa [hr] using h
      have hprev := ih c mid hr
      have hnext := bStep_sound m mid d hstep
      simp [run, hprev, hnext]

def b0 : BConfig := ⟨0, 10, 0⟩
def bFinal : BConfig := ⟨3, 39, 441711766194596082395824375185729628956870974218904739530347674252644983⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The blank-root prefix of TM2, checked by kernel reduction. -/
theorem tm2_blank_reaches_initialS1_bits :
    bRun tm2 27959 b0 = some bFinal := by decide

#print axioms tm2_blank_reaches_initialS1_bits

end BB6Coverage.Agent42InitialS1Bits
