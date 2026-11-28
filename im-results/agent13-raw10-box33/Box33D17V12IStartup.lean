import Box33D17V12ICarryScan
namespace MacroI
set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-- Starting the genuine long carry section is a five-transition universal
    identity, independent of the entire unread right stream. -/
theorem regular_head5 (r : Stream) :
    run 5 (cfg .A z (word (bits "01010") r)) =
    some (cfg .A (word (bits "1") z) (word (bits "0100") r)) := by rfl

/-- The exact six-transition right-pump (all left and right tapes arbitrary). -/
theorem regular_right4 (l r : Stream) :
    run 6 (cfg .A l (word (bits "0100") r)) =
    some (cfg .A (word (bits "1101") l) r) := by rfl

/-- Pump arbitrarily many four-bit blocks, preserving both arbitrary tails. -/
theorem regular_right4_many (k : Nat) (l r : Stream) :
    run (6*k)
      (cfg .A l (carryRepeat (bits "0100") k r)) =
    some (cfg .A (carryRepeat (bits "1101") k l) r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show 6*(k+1)=6*k+6 by omega,run_add,
        carry_repeat_snoc (bits "0100") k r,ih,
        Option.bind_some,regular_right4]
    rfl

/-- The final fixed 18 moves cross the literal 12-bit bridge into the
    carry-scan interface. Valid for any left tape and any unread right tape. -/
theorem regular_enter_carry (l r : Stream) :
    run 18 (cfg .A l (word (bits "010101010010") r)) =
    some (carryC l r) := by rfl

/-- Abstract j-parametric start-to-carry theorem; the input is written in
    rotated 0100 blocks. The additional word-conjugacy to phase(j,...) is
    separate and must be source-checked before original-root use. -/
theorem regular_start_rotated (j : Nat) (r : Stream) :
    run (29+6*j)
       (cfg .A z
         (word (bits "01010")
           (carryRepeat (bits "0100") j
             (word (bits "010101010010") r)))) =
    some (carryC
        (carryRepeat (bits "1101") (j+1) (word (bits "1") z)) r) := by
  have h5 := regular_head5
    (carryRepeat (bits "0100") j (word (bits "010101010010") r))
  have hp := regular_right4_many (j+1) (word (bits "1") z)
    (word (bits "010101010010") r)
  have he := regular_enter_carry
    (carryRepeat (bits "1101") (j+1) (word (bits "1") z)) r
  have hn : 29+6*j = 5+(6*(j+1)+18) := by omega
  rw [hn,run_add,h5,Option.bind_some,run_add]
  change (run (6*(j+1))
    (cfg .A (word (bits "1") z)
      (word (bits "0100")
        (carryRepeat (bits "0100") j
          (word (bits "010101010010") r))))).bind
    (run 18) = _
  rw [show word (bits "0100")
      (carryRepeat (bits "0100") j
         (word (bits "010101010010") r)) =
      carryRepeat (bits "0100") (j+1)
         (word (bits "010101010010") r) by rfl]
  rw [hp,Option.bind_some,he]


/-- Exact 0010 ↔ 0100 conjugacy for arbitrary block count and tape tail. -/
theorem regular_rotate_0010 (j : Nat) (r : Stream) :
    word (bits "010") (carryRepeat (bits "0010") j r) =
      carryRepeat (bits "0100") j (word (bits "010") r) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change word (bits "0100010") (carryRepeat (bits "0010") j r) =
      word (bits "0100")
        (carryRepeat (bits "0100") j (word (bits "010") r))
    rw [← ih]
    rfl

/-- Exact all-j source entry from the original phase boundary into the
    12-bit C carry scanner. This composes the 5-step head core, j+1 pumps,
    and the fixed 18-step exit, with a stream word-conjugacy. -/
theorem regular_start_phase (j : Nat) (r : Stream) :
    run (29+6*j) (phase j (word (bits "101010010") r)) =
      some (carryC
        (carryRepeat (bits "1101") (j+1) (word (bits "1") z)) r) := by
  have hprefix : phase j (word (bits "101010010") r) =
      cfg .A z (word (bits "01010")
        (carryRepeat (bits "0100") j
          (word (bits "010101010010") r))) := by
    change cfg .A z
      (word (bits "01010")
        (word (bits "010")
          (carryRepeat (bits "0010") j
            (word (bits "101010010") r)))) = _
    rw [regular_rotate_0010]
    rfl
  rw [hprefix]
  exact regular_start_rotated j r

#print axioms regular_rotate_0010
#print axioms regular_start_phase

#print axioms regular_head5
#print axioms regular_right4_many
#print axioms regular_enter_carry
#print axioms regular_start_rotated
end MacroI
