import Raw13Frames
import Raw13RightCounter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13CoupledJump
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent46Raw13RightCounter
open BB6.Agent46Raw13Frames (A Path0 pathJoin)

theorem scan_eq (W : List Bool) :
    scan W = BB6.Agent46Raw13Frames.scan W := by
  induction W using scan.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 => rfl
  | case4 => rfl
  | case5 a b W ih => simp only [scan,BB6.Agent46Raw13Frames.scan,ih]

theorem blocks_eq (n : Nat) : oneBlocks n = rep [true,false,false,false] n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [oneBlocks,rep,ih]

theorem firstRule (n : Nat) (L W : List Bool) :
    Path0 (A (oneBlocks n ++ false::L) W)
      (A (ones (scan (true::W)).1 ++ zeros (4*n) ++ true::L) (scan (true::W)).2) := by
  simpa only [blocks_eq,scan_eq,ones,zeros,BB6.Agent46Raw13Frames.ones,BB6.Agent46Raw13Frames.zeros,
    Nat.mul_zero,List.replicate_zero,List.nil_append] using BB6.Agent46Raw13Frames.main 0 n L W

theorem secondRule (k n : Nat) (L W : List Bool) :
    Path0 (A (ones (2*(k+1)) ++ oneBlocks n ++ false::L) W)
      (A (zeros (4*n) ++ true::L) (zeros k ++ true::W)) := by
  simpa only [blocks_eq,ones,zeros,BB6.Agent46Raw13Frames.ones,BB6.Agent46Raw13Frames.zeros]
    using BB6.Agent46Raw13Frames.main_pos k n L W

/-- Source machine path, with both physical suffixes arbitrary. -/
theorem jump (m x d : Nat) (U R : List Bool) (ts us : List Triple)
    (hd : 0<d) (hx : x+2*d < 2^m) (ha : add ts d = some us) :
    Path0 (A (encode m x++U) (word ts R)) (A (encode m (x+2*d)++U) (word us R)) :=
  double_jump A Path0 pathJoin firstRule secondRule m x d U R ts us hd hx ha

#print axioms jump
end BB6.Agent46Raw13CoupledJump
