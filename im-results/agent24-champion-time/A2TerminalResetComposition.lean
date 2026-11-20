import P2RootS0Identity
import S1CountedDrain
import TM63SourceIncrementDispatcherComplete
import TerminalEncoderBridge
import TerminalAfterPrefix
import Lean.Elab.Tactic.Omega

/-!
# A=2 q4Tail branch to the canonical terminal section

This is a source-level composition draft.  It does not claim that the
authentic blank-root trajectory has reached the A=2 q4Tail frame, and
the complete import closure has not been Lean-preflighted.

The key reparameterization is:
  p2ResidualLeft 76 (q4TailS0Tail 79 (2^79-3))
    = d1pow K ++ markerWord 0 ++ d0 ++ binDec 80 (2^80-7) ++ lh,
where K=2^z+z+3.

After the q4Tail adapter, the S0 counted drain changes the all-ones
binary counter into the right unary counter.  The resulting S1 state is
exactly the input to the existing complete SectionResult dispatcher.
Since 2^80-7 is divisible by three, its final marker is zero, and the
existing terminal SectionBits bridge applies.

This gives a conditional exact halting leaf from the A=2 q4Tail frame;
the still-open global problem is reaching that frame from the authentic
blank root.
-/

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent38RootQ4TailS0
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42TerminalJoin
open BB6Coverage.Agent44SectionResultRunSource
open BB6ChampionArithmetic

/-- The A=2 outer width has fixed encoder length 80. -/
def a2OuterLength : Nat := 80

/-- The A=2 outer counter at width 80. -/
def a2OuterValue : Nat := 2^80-7

/-- Positive-z q4Tail frame at the A=2 outer-width parameters
w=79 and q=2^79-3. -/
def a2Q4Frame (z : Nat) : Config :=
  q4TailS0Frame z 79 (2^79-3)

/-- The positive-z inner block count. -/
def a2InnerCount (z : Nat) : Nat :=
  2^(2^z-1)

/-- The unary block count contributed by the A=2 residual prefix. -/
def a2PrefixBlocks (z : Nat) : Nat :=
  2^z+z+3

/-- Unary exponent after combining the q4Tail's left counter with its
leading d1 block. -/
def a2Unary (z : Nat) : Nat :=
  a2InnerCount z - 1 + a2PrefixBlocks z

/-- Right counter after the q4Tail S0 counted drain. -/
def a2Right (z : Nat) : Nat :=
  2^(a2InnerCount z - 1)-1

/-- Absolute head of the A=2 q4Tail S0 configuration. -/
def a2Head (z : Nat) : Int :=
  (3*2^z+3*z+7)+2+3*a2InnerCount z

/-- All-ones BinDec words are the repeated d0 block. -/
private theorem a2_binDec_allOnes (k : Nat) :
    binDec k (2^k-1) = d0pow k := by
  induction k with
  | zero =>
      simp [binDec,binaryCounterFuel,d0pow]
  | succ k ih =>
      have hp : 0 < 2^k := Nat.pow_pos (by decide)
      have hbound : 2^k-1 < 2^k := by omega
      have hpow : 2^(k+1) = 2^k*2 := by
        rw [Nat.pow_succ]
      have hnum : 2^(k+1)-1 = 2*(2^k-1)+1 := by omega
      rw [hnum,binDec_odd k (2^k-1) hbound]
      simp [d0pow,ih]

/-- d1pow is exactly a run of 3*k ones. -/
private theorem a2_d1pow_replicate (k : Nat) :
    d1pow k = List.replicate (3*k) true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [d1pow,d1,Nat.mul_succ,List.replicate_add,ih]

/-- The A=2 q4 tail has the exact three-block BinDec shape. -/
private theorem a2_binDec_tail (L : Nat) :
    binDec (L+3) (2^(L+3)-3) =
      d0 ++ d1 ++ d0pow (L+1) := by
  have hpow2 : 2 ≤ 2^(L+2) := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤L+2 by omega)
    simpa using hp
  have hpow1 : 1 ≤ 2^(L+1) := by
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hnum1 : 2^(L+3)-3 = 2*(2^(L+2)-2)+1 := by
    have hp : 2^(L+3) = 2^(L+2)*2 := by rw [Nat.pow_succ]
    omega
  have hnum2 : 2^(L+2)-2 = 2*(2^(L+1)-1) := by
    have hp : 2^(L+2) = 2^(L+1)*2 := by rw [Nat.pow_succ]
    omega
  have hbound1 : 2^(L+2)-2 < 2^(L+2) := by omega
  have hbound2 : 2^(L+1)-1 < 2^(L+1) := by omega
  calc
    binDec (L+3) (2^(L+3)-3)
        = binDec ((L+2)+1) (2*(2^(L+2)-2)+1) := by
            rw [show L+3=(L+2)+1 by omega,hnum1]
    _ = d0 ++ binDec (L+2) (2^(L+2)-2) :=
          binDec_odd (L+2) (2^(L+2)-2) hbound1
    _ = d0 ++ d1 ++ binDec (L+1) (2^(L+1)-1) := by
          rw [show L+2=(L+1)+1 by omega,hnum2]
          rw [binDec_even (L+1) (2^(L+1)-1) hbound2]
    _ = d0 ++ d1 ++ d0pow (L+1) := by
          rw [a2_binDec_allOnes]

/-- The terminal-width BinDec has two leading d1 blocks. -/
private theorem a2_binDec_width (L : Nat) :
    binDec (L+4) (2^(L+4)-7) =
      d0 ++ d1pow 2 ++ d0pow (L+1) := by
  have hpow3 : 4 ≤ 2^(L+3) := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2)
      (show 2≤L+3 by omega)
    simpa using hp
  have hpow2 : 2 ≤ 2^(L+2) := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤L+2 by omega)
    simpa using hp
  have hpow1 : 1 ≤ 2^(L+1) := by
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hnum1 : 2^(L+4)-7 = 2*(2^(L+3)-4)+1 := by
    have hp : 2^(L+4) = 2^(L+3)*2 := by rw [Nat.pow_succ]
    omega
  have hnum2 : 2^(L+3)-4 = 2*(2^(L+2)-2) := by
    have hp : 2^(L+3) = 2^(L+2)*2 := by rw [Nat.pow_succ]
    omega
  have hnum3 : 2^(L+2)-2 = 2*(2^(L+1)-1) := by
    have hp : 2^(L+2) = 2^(L+1)*2 := by rw [Nat.pow_succ]
    omega
  have hbound1 : 2^(L+3)-4 < 2^(L+3) := by omega
  have hbound2 : 2^(L+2)-2 < 2^(L+2) := by omega
  have hbound3 : 2^(L+1)-1 < 2^(L+1) := by omega
  calc
    binDec (L+4) (2^(L+4)-7)
        = binDec ((L+3)+1) (2*(2^(L+3)-4)+1) := by
            rw [show L+4=(L+3)+1 by omega,hnum1]
    _ = d0 ++ binDec (L+3) (2^(L+3)-4) :=
          binDec_odd (L+3) (2^(L+3)-4) hbound1
    _ = d0 ++ d1 ++ binDec (L+2) (2^(L+2)-2) := by
          rw [show L+3=(L+2)+1 by omega,hnum2]
          rw [binDec_even (L+2) (2^(L+2)-2) hbound2]
    _ = d0 ++ d1 ++ d1 ++ binDec (L+1) (2^(L+1)-1) := by
          rw [show L+2=(L+1)+1 by omega,hnum3]
          rw [binDec_even (L+1) (2^(L+1)-1) hbound3]
    _ = d0 ++ d1pow 2 ++ d0pow (L+1) := by
          rw [a2_binDec_allOnes]
          simp [d1pow,List.append_assoc]

/-- Dropping the four leading ones and the first two cells of the A=2
BinDec leaves the exact terminal-side suffix. -/
private theorem a2_tail0_drop6 (L : Nat) :
    (List.replicate 4 true ++
      binDec (L+3) (2^(L+3)-3) ++ lh).drop 6 =
      [true] ++ d1 ++ d0pow (L+1) ++ lh := by
  rw [a2_binDec_tail]
  simp [List.drop,List.replicate,d0,d1,List.append_assoc]

/-- The finite A=2 marker/digit boundary is exactly
markerWord(0) ++ d0pow(2) ++ d1pow(2). -/
private theorem a2_fixed_prefix (tail : List Bool) :
    [false,true,false,false] ++
      ([true,false,false,true,true,true] ++ ([true] ++ d1 ++ tail)) =
    markerWord 0 ++ d0pow 2 ++ d1pow 2 ++ tail := by
  simp [markerWord,d0,d1,d0pow,d1pow,List.append_assoc]

/-- Exact residual word at the A=2 q4Tail adapter output. -/
private theorem a2_residual_left_shape (z : Nat) :
    p2ResidualLeft (3*2^z+3*z+7)
      (q4TailS0Tail 79 (2^79-3)) =
    d1pow (2^z+z+3) ++ markerWord 0 ++ d0 ++
      binDec 80 (2^80-7) ++ lh := by
  let K : Nat := 2^z+z+3
  have hlen : (3*2^z+3*z+7)+2 = 3*K := by
    dsimp [K]
    omega
  have hrep :
      List.replicate ((3*2^z+3*z+7)+2) true = d1pow K := by
    rw [hlen]
    exact (a2_d1pow_replicate K).symm
  simp only [p2ResidualLeft,q4TailS0Tail]
  rw [hrep,a2_tail0_drop6]
  rw [a2_fixed_prefix (d0pow (76+1) ++ lh)]
  rw [a2_binDec_width]
  simp [d0pow,d0,List.append_assoc]

private theorem a2_config_ext {c d : Config}
    (hs : c.state=d.state) (hh : c.head=d.head)
    (ht : c.tape=d.tape) : c=d := by
  cases c
  cases d
  simp_all

/-- The A=2 q4Tail frame is exactly an S1 configuration after
reparameterizing its left BinDec word.  The nonzero binary counter is
preserved; the following counted drain transfers it to the right counter. -/
theorem a2_q4Frame_eq_s1Config (z : Nat) (hz : 1≤z) :
    a2Q4Frame z =
      s1Config 80 (2^80-7) 0 (a2Unary z) (a2Right z) 0 (a2Head z) := by
  let n : Nat := a2InnerCount z
  let K : Nat := a2PrefixBlocks z
  let m : Nat := 3*2^z+3*z+7
  have hframe :
      a2Q4Frame z =
        s0Config (p2ResidualLeft m (q4TailS0Tail 79 (2^79-3)))
          (n-1) (2^(n-1)-1) 0 (a2Head z) := by
    simpa [a2Q4Frame,n,m,a2Head,a2InnerCount] using
      (q4TailS0Frame_eq_s0Config z 79 (2^79-3) hz)
  have hres :
      p2ResidualLeft m (q4TailS0Tail 79 (2^79-3)) =
        d1pow K ++ markerWord 0 ++ d0 ++
          binDec 80 (2^80-7) ++ lh := by
    simpa [m,K,a2PrefixBlocks] using a2_residual_left_shape z
  have hbase :
      binDec (n-1) (2^(n-1)-1) = d0pow (n-1) :=
    a2_binDec_allOnes (n-1)
  have hcarry :
      binDec (n-1+K) (2^(n-1)-1) =
        d0pow (n-1) ++ d1pow K := by
    have hq : 0 < 2^(K-1) := Nat.pow_pos (by decide)
    have hraw := binDec_sub_one_carryPrefix (K-1) 0 (n-1) (by omega)
    have hlen : (K-1)+1+(n-1) = n-1+K := by omega
    have hval : ((2*0+1)*2^(n-1))-1 = 2^(n-1)-1 := by simp
    have hraw' :
        binDec (n-1+K) (2^(n-1)-1) =
          d0pow (n-1) ++ d1 ++ binDec (K-1) 0 := by
      simpa [hlen,hval] using hraw
    have hK : K=(K-1)+1 := by omega
    calc
      binDec (n-1+K) (2^(n-1)-1)
          = d0pow (n-1) ++ d1 ++ d1pow (K-1) := by
              simpa [binDec_zero] using hraw'
      _ = d0pow (n-1) ++ d1pow K := by
              rw [hK,d1pow]
  have hleft :
      s0LeftFacing (p2ResidualLeft m (q4TailS0Tail 79 (2^79-3)))
          (n-1) (2^(n-1)-1) =
      s0LeftFacing (markerWord 0 ++ d0 ++ binDec 80 (2^80-7) ++ lh)
          (n-1+K) (2^(n-1)-1) := by
    simp only [s0LeftFacing]
    rw [hbase,hres,hcarry]
    simp [List.append_assoc]
  have hcfg :
      s0Config (p2ResidualLeft m (q4TailS0Tail 79 (2^79-3)))
          (n-1) (2^(n-1)-1) 0 (a2Head z) =
      s1Config 80 (2^80-7) 0 (n-1+K) (2^(n-1)-1) 0 (a2Head z) := by
    apply a2_config_ext
    · simp
    · rfl
    · funext x
      simp only [s0Config,s1Config,s0Tape]
      rw [hleft]
  simpa [a2Unary,a2Right,a2InnerCount,a2PrefixBlocks,n,K] using
    hframe.trans hcfg

private theorem a2_unary_pos (z : Nat) : 0<a2Unary z := by
  unfold a2Unary a2InnerCount a2PrefixBlocks
  omega

private theorem a2_drain_bound (z : Nat) :
    a2Right z < 2^(a2Unary z) := by
  unfold a2Right a2Unary a2InnerCount a2PrefixBlocks
  have hpow :
      2^(2^(2^z-1)-1) ≤
        2^(2^(2^z-1)-1+(2^z+z+3)) := by
    apply Nat.pow_le_pow_right
    omega
  omega

/-- The S0 counted drain converts the A=2 q4Tail output into the exact
S1 reset-chain input. -/
theorem a2_q4Frame_counted_drain (z : Nat) (hz : 1≤z) :
    run tm2 (drainCost (a2Right z) 0) (a2Q4Frame z) =
      some (s1Config 80 (2^80-7) 0 (a2Unary z) 0
        (a2Right z) (a2Head z)) := by
  rw [a2_q4Frame_eq_s1Config z hz]
  exact s1Config_counted_drain 80 (2^80-7) 0 (a2Unary z)
    (a2InnerCount z-1) 0 (a2Head z) (a2_drain_bound z)

/-- Primitive-recursive endpoint of the complete source reset countdown. -/
def a2FinalResult (z : Nat) : SectionResult :=
  sectionResult (2^80-7) 0 (a2Unary z) (a2Right z)

/-- Head after all A=2 outer-counter decrements. -/
def a2FinalHead (z : Nat) : Int :=
  sectionHeadAfter (2^80-7) (a2Right z) (a2Head z)

/-- Exact source cost from the A=2 q4Tail frame through the counted drain
and complete SectionResult countdown. -/
def a2PrefixCost (z : Nat) : Nat :=
  drainCost (a2Right z) 0 + (a2FinalResult z).cost

/-- Since 2^80-7 is divisible by three, the SectionResult marker returns
to zero after the complete countdown. -/
theorem a2_final_marker_zero (z : Nat) :
    (a2FinalResult z).marker = 0 := by
  unfold a2FinalResult
  rw [sectionResult_marker]
  decide

/-- Exact original-TM2 run from the A=2 q4Tail frame to the marker-zero
terminal S1 configuration. -/
theorem a2_q4Frame_to_terminalConfig (z : Nat) (hz : 1≤z) :
    run tm2 (a2PrefixCost z) (a2Q4Frame z) =
      some (s1Config 80 0 0 (a2FinalResult z).exponent 0
        (a2FinalResult z).right (a2FinalHead z)) := by
  have hdrain := a2_q4Frame_counted_drain z hz
  have hcount := sectionResult_run_complete 80 (2^80-7) 0
    (a2Unary z) (a2Right z) (a2Head z)
    (by decide) (by decide) (a2_unary_pos z)
  have hmarker := a2_final_marker_zero z
  unfold a2PrefixCost a2FinalResult a2FinalHead
  rw [run_add,hdrain]
  simp only [Option.bind_some]
  rw [hmarker] at hcount
  exact hcount

/-- The terminal S1 configuration has exactly the SectionBits interface
consumed by the existing arbitrary-exterior terminal macro. -/
theorem a2_q4Frame_terminalSection (z : Nat) :
    TerminalFinish.SectionBits 80 (a2FinalResult z).exponent
      (s1Config 80 0 0 (a2FinalResult z).exponent 0
        (a2FinalResult z).right (a2FinalHead z)).tape
      (a2FinalHead z) := by
  simpa [s1Config] using
    (s0_reset_sectionBits 80 (a2FinalResult z).exponent
      (a2FinalResult z).right (a2FinalHead z))

/-- If the authentic blank-root run reaches the A=2 q4Tail frame, it
halts after the exact counted-drain, reset-chain, and terminal costs. -/
theorem a2_q4Frame_blank_prefix_halts
    (z rootSteps : Nat) (hz : 1≤z)
    (hroot : run tm2 rootSteps blank = some (a2Q4Frame z)) :
    HaltsAfter tm2
      (rootSteps + a2PrefixCost z +
        terminalMoves 80 (a2FinalResult z).exponent) := by
  have hpost := a2_q4Frame_to_terminalConfig z hz
  have hprefix :
      run tm2 (rootSteps+a2PrefixCost z) blank =
        some (s1Config 80 0 0 (a2FinalResult z).exponent 0
          (a2FinalResult z).right (a2FinalHead z)) := by
    rw [run_add,hroot]
    simp only [Option.bind_some]
    exact hpost
  exact tm2_halts_after_terminal_prefix
    (rootSteps+a2PrefixCost z) 80 (a2FinalResult z).exponent
    (s1Config 80 0 0 (a2FinalResult z).exponent 0
      (a2FinalResult z).right (a2FinalHead z)).tape
    (a2FinalHead z)
    (by simpa [s1Config,s0Config] using hprefix)
    (a2_q4Frame_terminalSection z)

/-- The corresponding BB(6) attainable-score interface, conditional on
the same genuine blank-root prefix to the A=2 q4Tail frame. -/
theorem a2_q4Frame_blank_prefix_attainable
    (z rootSteps : Nat) (hz : 1≤z)
    (hroot : run tm2 rootSteps blank = some (a2Q4Frame z)) :
    Attainable
      (rootSteps + a2PrefixCost z +
        terminalMoves 80 (a2FinalResult z).exponent + 7) := by
  have hpost := a2_q4Frame_to_terminalConfig z hz
  have hprefix :
      run tm2 (rootSteps+a2PrefixCost z) blank =
        some (s1Config 80 0 0 (a2FinalResult z).exponent 0
          (a2FinalResult z).right (a2FinalHead z)) := by
    rw [run_add,hroot]
    simp only [Option.bind_some]
    exact hpost
  exact champion_attainable_after_terminal_prefix
    (rootSteps+a2PrefixCost z) 80 (a2FinalResult z).exponent
    (s1Config 80 0 0 (a2FinalResult z).exponent 0
      (a2FinalResult z).right (a2FinalHead z)).tape
    (a2FinalHead z)
    (by simpa [s1Config,s0Config] using hprefix)
    (a2_q4Frame_terminalSection z)

#print axioms a2_q4Frame_eq_s1Config
#print axioms a2_q4Frame_counted_drain
#print axioms a2_q4Frame_to_terminalConfig
#print axioms a2_q4Frame_blank_prefix_halts
#print axioms a2_q4Frame_blank_prefix_attainable

end BB6Coverage.Agent24ChampionTime
