import Box33D17V12IParametric
namespace MacroI
set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-- Two full rightward carry-scan states, expressed with a fixed near-head
    12-bit left suffix and arbitrary farther left and right streams. -/
abbrev carryC (l r : Stream) : Config :=
  cfg .C (word (bits "101111111011") l) r
abbrev carryF (l r : Stream) : Config :=
  cfg .F (word (bits "111110111111") l) r

/-- Reading the N-language carry digit R=0101 advances four cells
    from state C to state F, preserving the entire arbitrary right suffix. -/
theorem carry_N1 (l r : Stream) :
    run 6 (carryC l (word (bits "0101") r)) =
      some (carryF (word (bits "1011") l) r) := by rfl

/-- Reading the B-language carry digit P=0010 advances four cells
    from state F to state C, preserving the entire arbitrary right suffix. -/
theorem carry_B1 (l r : Stream) :
    run 4 (carryF l (word (bits "0010") r)) =
      some (carryC (word (bits "1111") l) r) := by rfl

/-- The alternating two-digit carry pair has an exact TEN-step law
    over arbitrary infinite left and right tails. -/
theorem carry_pair (l r : Stream) :
    run 10 (carryC l (word (bits "01010010") r)) =
      some (carryC (word (bits "11111011") l) r) := by
  have h1 : run 6 (carryC l (word (bits "01010010") r)) =
      some (carryF (word (bits "1011") l) (word (bits "0010") r)) := by
    convert carry_N1 l (word (bits "0010") r) using 1 <;> rfl
  change run (6+4) (carryC l (word (bits "01010010") r)) = _
  rw [run_add,h1,Option.bind_some,carry_B1]
  rfl

/-- Prefix repetition in a two-sided infinite stream. -/
def carryRepeat (pattern : List Bool) : Nat → Stream → Stream
  | 0, r => r
  | n+1, r => word pattern (carryRepeat pattern n r)

theorem carry_repeat_snoc (pattern : List Bool) (k : Nat) (r : Stream) :
    carryRepeat pattern (k+1) r =
      carryRepeat pattern k (word pattern r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change word pattern (carryRepeat pattern (k+1) r) =
      word pattern (carryRepeat pattern k (word pattern r))
    rw [ih]

/-- Uniform carry-scan law for ARBITRARILY MANY alternating R,P pairs.
    This is a quantified part of the missing regular-language source proof,
    not a complete blank-tape nonhalting theorem. -/
theorem carry_pairs (k : Nat) (l r : Stream) :
    run (10*k) (carryC l (carryRepeat (bits "01010010") k r)) =
      some (carryC (carryRepeat (bits "11111011") k l) r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show 10*(k+1) = 10*k+10 by omega,run_add,
        carry_repeat_snoc (bits "01010010") k r,ih,
        Option.bind_some,carry_pair]
    rfl

#print axioms carry_pair
#print axioms carry_pairs
end MacroI
