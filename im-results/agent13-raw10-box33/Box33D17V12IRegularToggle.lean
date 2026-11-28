import Box33D17V12ICarry
namespace MacroI
set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-- A uniform four-outer-phase, zero-carry toggle on arbitrary infinite tail.
    This is the N = S B -> R B branch of the two-sorted regular candidate.
    Unlike finite simulation, it is parametrized over ALL j and r.
    The unproved branch is N = R B -> S (nextB B). -/
theorem regular_toggle (j : Nat) (r : Stream) :
    run (650 + 128*j)
      (phase j (word (bits "1010100001000") r)) =
      some (phase (j+4) (word (bits "1010100000101") r)) := by
  have h1 : run (110+32*j)
      (phase j (word (bits "1010100001000") r)) =
      some (phase (j+1) (word (bits "1100000101000") r)) := by
    convert evenPacket j (word (bits "01000") r) using 1 <;> rfl
  have h2 : run (108+32*(j+1))
      (phase (j+1) (word (bits "1100000101000") r)) =
      some (phase (j+2) (word (bits "1010100101000") r)) := by
    convert oddPacket (j+1) (word (bits "00101000") r) using 1 <;> rfl
  have h3 : run (132+32*(j+2))
      (phase (j+2) (word (bits "1010100101000") r)) =
      some (phase (j+3) (word (bits "1100000000101") r)) :=
    carryPacket (j+2) r
  have h4 : run (108+32*(j+3))
      (phase (j+3) (word (bits "1100000000101") r)) =
      some (phase (j+4) (word (bits "1010100000101") r)) := by
    convert oddPacket (j+3) (word (bits "00000101") r) using 1 <;> rfl
  have cost :
    650+128*j =
      (110+32*j)+((108+32*(j+1))+((132+32*(j+2))+(108+32*(j+3)))) := by
    omega
  rw [cost,run_add,h1,Option.bind_some,run_add,h2,Option.bind_some,
      run_add,h3,Option.bind_some,h4]

#print axioms regular_toggle
end MacroI
