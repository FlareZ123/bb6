import TerminalAfterPrefix
import S1Encoder
import CountedReset
import Lean.Elab.Tactic.Omega

/-!
# Source S0 reset endpoint to the arbitrary-exterior terminal section

This is the finite-word join between the original S0 encoder and the
source-certified TerminalFinish.SectionBits interface.  It is uniform in
the two unary lengths, the right counter, and the absolute head position.
It does not assume or prove any reset dynamics.
-/

namespace BB6Coverage.Agent42TerminalJoin

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic

private theorem terminal_sideBit_three_ones (xs : List Bool) (i : Nat) :
    sideBit (true::true::true::xs) i =
      if i < 3 then true else sideBit xs (i-3) := by
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => simp [sideBit] <;> omega

private theorem terminal_sideBit_d1pow_append
    (n i : Nat) (tail : List Bool) (hi : i < 3*n) :
    sideBit (d1pow n ++ tail) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      change sideBit (true::true::true::(d1pow n ++ tail)) i = true
      rw [terminal_sideBit_three_ones]
      by_cases hsmall : i < 3
      · simp [hsmall]
      · simp [hsmall]
        exact ih (i-3) (by omega)

private theorem terminal_sideBit_d1pow_append_ge
    (n i : Nat) (tail : List Bool) (hi : 3*n ≤ i) :
    sideBit (d1pow n ++ tail) i = sideBit tail (i-3*n) := by
  induction n generalizing i with
  | zero => simp [d1pow]
  | succ n ih =>
      change sideBit (true::true::true::(d1pow n ++ tail)) i =
        sideBit tail (i-3*(n+1))
      rw [terminal_sideBit_three_ones]
      have hge : ¬ i < 3 := by omega
      simp [hge]
      rw [ih (i-3) (by omega)]
      congr 1 <;> omega

private def terminalResetTail (L : Nat) : List Bool :=
  markerWord 0 ++ d0 ++ d1pow L ++ lh

private theorem terminal_sideBit_resetTail (L j : Nat) :
    sideBit (terminalResetTail L) (5+j) =
      sideBit (d1pow L ++ lh) j := by
  have hidx : 5+j = j+5 := by omega
  rw [hidx]
  change sideBit (false::true::false::false::true::(d1pow L ++ lh)) (j+5) = _
  simp only [Nat.add_succ, Nat.add_zero, sideBit]

private theorem terminal_sideBit_resetTail_0 (L : Nat) :
    sideBit (terminalResetTail L) 0 = false := by
  simp [terminalResetTail, markerWord, d0, sideBit]

private theorem terminal_sideBit_resetTail_1 (L : Nat) :
    sideBit (terminalResetTail L) 1 = true := by
  simp [terminalResetTail, markerWord, d0, sideBit]

private theorem terminal_sideBit_resetTail_2 (L : Nat) :
    sideBit (terminalResetTail L) 2 = false := by
  simp [terminalResetTail, markerWord, d0, sideBit]

private theorem terminal_sideBit_resetTail_3 (L : Nat) :
    sideBit (terminalResetTail L) 3 = false := by
  simp [terminalResetTail, markerWord, d0, sideBit]

private theorem terminal_sideBit_resetTail_4 (L : Nat) :
    sideBit (terminalResetTail L) 4 = true := by
  simp [terminalResetTail, markerWord, d0, sideBit]

private theorem terminal_sideBit_d1pow_LH
    (L j : Nat) (hj : j < 3*L+2) :
    sideBit (d1pow L ++ lh) j = true := by
  by_cases hlt : j < 3*L
  · exact terminal_sideBit_d1pow_append L j lh hlt
  · have hge : 3*L ≤ j := by omega
    have hrem : j-3*L = 0 ∨ j-3*L = 1 := by omega
    rw [terminal_sideBit_d1pow_append_ge L j lh hge]
    rcases hrem with h0 | h1
    · rw [h0]; simp [lh, sideBit]
    · rw [h1]; simp [lh, sideBit]

private theorem terminal_sideBit_d1pow_LH_zero (L : Nat) :
    sideBit (d1pow L ++ lh) (3*L+2) = false := by
  rw [terminal_sideBit_d1pow_append_ge L (3*L+2) lh (by omega)]
  simp [lh, sideBit]

private theorem terminal_sideBit_d1pow_LH_three
    (L j : Nat) (hj : 3 ≤ j) (hj' : j ≤ 5) :
    sideBit (d1pow L ++ lh) (3*L+j) = true := by
  rw [terminal_sideBit_d1pow_append_ge L (3*L+j) lh (by omega)]
  have hcases : j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hcases with h3|h4|h5
  · rw [h3]; simp [lh, sideBit]
  · rw [h4]; simp [lh, sideBit]
  · rw [h5]; simp [lh, sideBit]

private theorem terminal_sideBit_d1pow_LH_farZero
    (L k : Nat) (hk : k ≥ 6) :
    sideBit (d1pow L ++ lh) (3*L+k) = false := by
  rw [terminal_sideBit_d1pow_append_ge L (3*L+k) lh (by omega)]
  have hidx : k = (k-6)+6 := by omega
  rw [hidx]
  simp [lh, sideBit]

/-- The original-source S0 configuration at the all-ones reset endpoint
has exactly the arbitrary-exterior terminal S1 section.  The right counter
is unrestricted: only the first seven cells of its encoded suffix are
needed by the terminal theorem. -/
theorem s0_reset_sectionBits (L a b : Nat) (h : Int) :
    TerminalFinish.SectionBits L a
      (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh) a 0 b h).tape h := by
  let l := markerWord 0 ++ d0 ++ binDec L 0 ++ lh
  let tail := terminalResetTail L
  let cfg := s0Config l a 0 b h
  have hleft : s0LeftFacing l a 0 = d1pow a ++ tail := by
    simp only [s0LeftFacing, l, binDec_zero, tail, terminalResetTail, List.append_assoc]
  have hleftCell (i : Nat) :
      cfg.tape (h-(i:Int)) = sideBit (d1pow a ++ tail) i := by
    simpa [cfg,hleft] using s0Config_left_cell l a 0 b h i
  have hrightCell (i : Nat) :
      cfg.tape (h+1+(i:Int)) = sideBit (s0RightFacing b) i := by
    simpa [cfg] using s0Config_right_cell l a 0 b h i
  have hrightCell' (i : Nat) :
      cfg.tape (h+(i+1:Int)) = sideBit (s0RightFacing b) i := by
    have heq : h+(i+1:Int) = h+1+(i:Int) := by omega
    rw [heq]
    exact hrightCell i
  have hleftCell' (i : Nat) :
      cfg.tape (h-(i:Int)) = sideBit (d1pow a ++ tail) i := hleftCell i
  have hr0 : cfg.tape (h+1) = false := by
    have hc := hrightCell' 0
    simpa [s0RightFacing, sideBit] using hc
  have hr1 : cfg.tape (h+2) = true := by
    have hc := hrightCell' 1
    simpa [s0RightFacing, sideBit] using hc
  have hr2 : cfg.tape (h+3) = true := by
    have hc := hrightCell' 2
    simpa [s0RightFacing, sideBit] using hc
  have hr3 : cfg.tape (h+4) = true := by
    have hc := hrightCell' 3
    simpa [s0RightFacing, sideBit] using hc
  have hr4 : cfg.tape (h+5) = false := by
    have hc := hrightCell' 4
    simpa [s0RightFacing, sideBit] using hc
  have hr5 : cfg.tape (h+6) = false := by
    have hc := hrightCell' 5
    simpa [s0RightFacing, sideBit] using hc
  have hr6 : cfg.tape (h+7) = true := by
    have hc := hrightCell' 6
    simpa [s0RightFacing, d1pow, d1, sideBit] using hc
  change TerminalFinish.SectionBits L a cfg.tape h
  constructor
  · exact hr0
  · exact hr1
  · exact hr2
  · exact hr3
  · exact hr4
  · exact hr5
  · exact hr6
  · intro j hj hj'
    let i := Int.toNat (h-j)
    have hi : i < 3*a := by dsimp [i]; omega
    have hc := hleftCell' i
    have hcoord : h-(i:Int) = j := by dsimp [i]; omega
    rw [hcoord] at hc
    exact hc.trans (terminal_sideBit_d1pow_append a i tail hi)
  · have hc := hleftCell' (3*a)
    have hval : sideBit (d1pow a ++ tail) (3*a) = false := by
      rw [terminal_sideBit_d1pow_append_ge a (3*a) tail (by omega)]
      simpa [tail] using terminal_sideBit_resetTail_0 L
    exact hc.trans hval
  · have hc := hleftCell' (3*a+1)
    have hval : sideBit (d1pow a ++ tail) (3*a+1) = true := by
      rw [terminal_sideBit_d1pow_append_ge a (3*a+1) tail (by omega)]
      simpa [tail] using terminal_sideBit_resetTail_1 L
    have hcoord : h-↑(3*a+1) = h-↑(3*a)-1 := by omega
    rw [hcoord] at hc
    exact hc.trans hval
  · have hc := hleftCell' (3*a+2)
    have hval : sideBit (d1pow a ++ tail) (3*a+2) = false := by
      rw [terminal_sideBit_d1pow_append_ge a (3*a+2) tail (by omega)]
      simpa [tail] using terminal_sideBit_resetTail_2 L
    have hcoord : h-↑(3*a+2) = h-↑(3*a)-2 := by omega
    rw [hcoord] at hc
    exact hc.trans hval
  · have hc := hleftCell' (3*a+3)
    have hval : sideBit (d1pow a ++ tail) (3*a+3) = false := by
      rw [terminal_sideBit_d1pow_append_ge a (3*a+3) tail (by omega)]
      simpa [tail] using terminal_sideBit_resetTail_3 L
    have hcoord : h-↑(3*a+3) = h-↑(3*a)-3 := by omega
    rw [hcoord] at hc
    exact hc.trans hval
  · intro j hj hj'
    let i := Int.toNat (h-j)
    have hiLo : 3*a+4 ≤ i := by dsimp [i]; omega
    have hiHi : i ≤ 3*a+6+3*L := by dsimp [i]; omega
    have hc := hleftCell' i
    have hcoord : h-(i:Int) = j := by dsimp [i]; omega
    rw [hcoord] at hc
    have hval : sideBit (d1pow a ++ tail) i = true := by
      by_cases hfirst : i = 3*a+4
      · rw [hfirst]
        rw [terminal_sideBit_d1pow_append_ge a (3*a+4) tail (by omega)]
        simpa [tail] using terminal_sideBit_resetTail_4 L
      · have hge : 3*a+5 ≤ i := by omega
        rw [terminal_sideBit_d1pow_append_ge a i tail (by omega)]
        have hidx : i-3*a = 5 + (i-(3*a+5)) := by omega
        rw [hidx]
        rw [terminal_sideBit_resetTail]
        exact terminal_sideBit_d1pow_LH L (i-(3*a+5)) (by omega)
    exact hc.trans hval
  · have hc := hleftCell' (3*a+7+3*L)
    have hval : sideBit (d1pow a ++ tail) (3*a+7+3*L) = false := by
      rw [terminal_sideBit_d1pow_append_ge a _ tail (by omega)]
      have hidx : 3*a+7+3*L-3*a = 5+(3*L+2) := by omega
      rw [hidx]
      rw [terminal_sideBit_resetTail]
      exact terminal_sideBit_d1pow_LH_zero L
    have hcoord : h-↑(3*a+7+3*L) = h-↑(3*a)-↑(7+3*L) := by omega
    rw [hcoord] at hc
    exact hc.trans hval
  · intro j hj hj'
    let i := Int.toNat (h-j)
    have hiLo : 3*a+8+3*L ≤ i := by dsimp [i]; omega
    have hiHi : i ≤ 3*a+10+3*L := by dsimp [i]; omega
    have hc := hleftCell' i
    have hcoord : h-(i:Int) = j := by dsimp [i]; omega
    rw [hcoord] at hc
    have hval : sideBit (d1pow a ++ tail) i = true := by
      rw [terminal_sideBit_d1pow_append_ge a i tail (by omega)]
      have hidx : i-3*a = 5+(3*L+(i-(3*a+5+3*L))) := by omega
      rw [hidx]
      rw [terminal_sideBit_resetTail]
      have hrem :
          i-(3*a+5+3*L) = 3 ∨ i-(3*a+5+3*L) = 4 ∨ i-(3*a+5+3*L) = 5 := by omega
      rcases hrem with h3|h4|h5
      · rw [h3]; exact terminal_sideBit_d1pow_LH_three L 3 (by omega) (by omega)
      · rw [h4]; exact terminal_sideBit_d1pow_LH_three L 4 (by omega) (by omega)
      · rw [h5]; exact terminal_sideBit_d1pow_LH_three L 5 (by omega) (by omega)
    exact hc.trans hval
  · have hc := hleftCell' (3*a+11+3*L)
    have hval : sideBit (d1pow a ++ tail) (3*a+11+3*L) = false := by
      rw [terminal_sideBit_d1pow_append_ge a _ tail (by omega)]
      have hidx : 3*a+11+3*L-3*a = 5+(3*L+6) := by omega
      rw [hidx]
      rw [terminal_sideBit_resetTail]
      exact terminal_sideBit_d1pow_LH_farZero L 6 (by omega)
    have hcoord : h-↑(3*a+11+3*L) = h-↑(3*a)-↑(11+3*L) := by omega
    rw [hcoord] at hc
    exact hc.trans hval
  · have hc := hleftCell' (3*a+12+3*L)
    have hval : sideBit (d1pow a ++ tail) (3*a+12+3*L) = false := by
      rw [terminal_sideBit_d1pow_append_ge a _ tail (by omega)]
      have hidx : 3*a+12+3*L-3*a = 5+(3*L+7) := by omega
      rw [hidx]
      rw [terminal_sideBit_resetTail]
      exact terminal_sideBit_d1pow_LH_farZero L 7 (by omega)
    have hcoord : h-↑(3*a+12+3*L) = h-↑(3*a)-↑(12+3*L) := by omega
    rw [hcoord] at hc
    exact hc.trans hval

/-- A genuine blank-root TM63 prefix that reaches this S0 reset endpoint
can be scored immediately by the all-parameter terminal macro and the
published champion's root correction. -/
theorem champion_attainable_after_s0_reset_prefix
    (n L a b : Nat) (h : Int)
    (hprefix : run tm2 n blank =
      some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh) a 0 b h)) :
    Attainable (n + terminalMoves L a + 7) := by
  have hprefix' : run tm2 n blank =
      some ⟨(3 : Fin 6), h,
        (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh) a 0 b h).tape⟩ := by
    simpa [s0Config] using hprefix
  exact champion_attainable_after_terminal_prefix
    n L a _ h hprefix' (s0_reset_sectionBits L a b h)

/-- Compose Agent 8's conditional, exact Rst0/Rst1/Rst2 count with
the source-certified terminal section and champion root correction.  The
remaining machine-specific obligations are precisely the prefix witness
and the uniform original-source Inc0 premise already exposed by
`countedRst012_of_prefix`; this theorem adds no surrogate cost assumption. -/
theorem champion_attainable_after_countedRst012
    (cfg : Config) (rootSteps L a b m n : Nat) (h : Int)
    (ha : 0 < a)
    (hblank : run tm2 rootSteps blank = some cfg)
    (hprefix :
      run tm2 (resetPrefixCost m n a b) cfg =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta m) (2^b-1) 0 h))
    (hInc0 : ∀ z c, 0 < z → z < 2^(a+b+resetDelta m) →
      run tm2 (inc0Cost z c)
        (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta m) z c h) =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta m) (z-1) (c+1) h)) :
    Attainable
      (rootSteps + proposedIncrementCost m n a b +
        terminalMoves L (a+b+resetDelta m) + 7) := by
  have hstage := countedRst012_of_prefix cfg
    (markerWord 0 ++ d0 ++ binDec L 0 ++ lh) a b m n h ha hprefix hInc0
  have hblankStage :
      run tm2 (rootSteps + proposedIncrementCost m n a b) blank =
        some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
          (a+b+resetDelta m) 0 (2^b-1) h) := by
    calc
      run tm2 (rootSteps + proposedIncrementCost m n a b) blank =
          (run tm2 rootSteps blank).bind
            (fun c => run tm2 (proposedIncrementCost m n a b) c) :=
        run_add tm2 blank rootSteps (proposedIncrementCost m n a b)
      _ = some (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
            (a+b+resetDelta m) 0 (2^b-1) h) := by
        simp [hblank, hstage]
  exact champion_attainable_after_s0_reset_prefix
    (rootSteps + proposedIncrementCost m n a b)
    L (a+b+resetDelta m) (2^b-1) h hblankStage

#print axioms champion_attainable_after_countedRst012
#print axioms s0_reset_sectionBits
#print axioms champion_attainable_after_s0_reset_prefix

end BB6Coverage.Agent42TerminalJoin
