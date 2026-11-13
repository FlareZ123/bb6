import Q4Suffix
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# TM63 q4 suffix: exact right-facing endpoint

The q4 suffix's final local frame determines the nine-cell canonical S0
right word.  Its cells beyond the local frame are unchanged by the
first-ten frame, counted scan, and final tail.  The only extra input
needed for a *full tape* equality is the source prefix's infinite blank
right tail; this module isolates that interface.
-/

namespace BB6Coverage.Agent24Q4Endpoint

open BB6Coverage
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8S1Encoder

private theorem q4Endpoint_d0_length : d0.length = 3 := by
  rfl

private theorem q4Endpoint_d0pow_length (b : Nat) :
    (d0pow b).length = 3*b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      simp [d0pow, q4Endpoint_d0_length, ih]
      omega

/-- The nearest-first d0 word is periodic false,false,true. -/
private theorem q4Endpoint_sideBit_d0pow_mod (b i : Nat)
    (hi : i < 3*b) :
    sideBit (d0pow b) i = decide (i % 3 = 2) := by
  induction b generalizing i with
  | zero => omega
  | succ b ih =>
      change sideBit (d0 ++ d0pow b) i = decide (i % 3 = 2)
      by_cases hi0 : i < 3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h0 | h1 | h2
        · subst i
          simp [d0, sideBit]
        · subst i
          simp [d0, sideBit]
        · subst i
          simp [d0, sideBit]
      · have hi3 : 3 ≤ i := by omega
        have hi' : i-3 < 3*b := by omega
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          d0 (d0pow b) i (by rw [q4Endpoint_d0_length]; omega)]
        rw [q4Endpoint_d0_length]
        have hmod : i % 3 = (i-3) % 3 := by omega
        simpa [hmod] using ih (i-3) hi'

private theorem q4Endpoint_sideBit_drop_one (xs : List Bool) (i : Nat) :
    sideBit (xs.drop 1) i = sideBit xs (i+1) := by
  cases xs with
  | nil => simp [sideBit]
  | cons x xs => simp [sideBit]

/-- The exact prefix right-stream theorem implies the infinite blank tail
    needed to identify the suffix's entire right half. -/
theorem q4_prefix_far_tail (b : Nat) (Tq : Int → Bool) (h : Int)
    (hright : ∀ i : Nat,
      Tq (h+1+(i:Int)) =
        BB6Coverage.Agent8S1Encoder.sideBit
          (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i) :
    ∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false := by
  intro i hi
  rw [hright]
  have hlen :=
    BB6Coverage.Agent6Q4Prefix.q4RightFacing_length b
  exact BB6Coverage.Agent6Q4Prefix.sideBit_ge_length
    (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i (by omega)

/-- A cell in the final 29-move local frame, expressed relative to its
    origin g. -/
private theorem q4_tail_frame_cell (T : Int → Bool) (g r : Int)
    (hr : -4 ≤ r ∧ r ≤ 4) :
    (frameAt T g q4TailInside q4TailEnd).tape (g+r) =
      decide (r ∈ q4TailEnd.marked) := by
  rw [frameAt_tape]
  have hcoord : g+r-g = r := by omega
  rw [hcoord]
  have hin : q4TailInside r = true := by
    simp [q4TailInside]
    omega
  simp [hin]

/-- The original q4 suffix frame has exactly the target's nine-cell
    right-facing word, and preserves the blank ray beyond it. -/
theorem q4_suffix_right_word (T : Int → Bool) (h : Int) (b : Nat)
    (hshape : q4RightShape T h b)
    (htail : ∀ i : Nat, 9+3*b ≤ i →
      T (h+1+(i:Int)) = false) :
    ∀ i : Nat,
      (frameAt
        (d0Sweep b
          (frameAt T h q4First10Inside q4First10End).tape
          (h+10))
        (h+10+(3*b:Int)) q4TailInside q4TailEnd).tape
          (h+6+(3*b:Int)+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  intro i
  change U.tape (h+6+(3*b:Int)+(i:Int)) =
    sideBit (s0RightFacing 0) i
  by_cases hi : i < 9
  · have hcoord :
        h+6+(3*b:Int)+(i:Int) = g+(-4+(i:Int)) := by
      dsimp [g]
      omega
    rw [hcoord]
    have hrange : -4 ≤ (-4+(i:Int)) ∧ (-4+(i:Int)) ≤ 4 := by omega
    have hv := q4_tail_frame_cell T2 g (-4+(i:Int)) hrange
    have hcases :
        i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
        i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    all_goals
      subst i
      simpa [U, q4TailEnd, s0RightFacing, d1pow, d1, sideBit] using hv
  · have hi9 : 9 ≤ i := by omega
    let x : Int := h+6+(3*b:Int)+(i:Int)
    have hframe : U.tape x = T2 x := by
      dsimp [U]
      rw [frameAt_tape]
      have hnot : q4TailInside (x-g) = false := by
        simp [q4TailInside]
        dsimp [x,g]
        omega
      simp [hnot]
    have hscan : T2 x = T1 x := by
      dsimp [T2]
      exact d0Sweep_after b T1 (h+10) x (by
        dsimp [x,g]
        omega)
    have hfirst : T1 x = T x := by
      dsimp [T1]
      rw [frameAt_tape]
      have hnot : q4First10Inside (x-h) = false := by
        simp [q4First10Inside]
        dsimp [x,g]
        omega
      simp [hnot]
    have hidx : x = h+1+((5+3*b+i:Int)) := by
      dsimp [x,g]
      omega
    have hzero := htail (5+3*b+i) (by omega)
    have hlen : (s0RightFacing 0).length = 9 := by
      simp [s0RightFacing, d1pow, d1]
    have htarget :
        sideBit (s0RightFacing 0) i = false :=
      BB6Coverage.Agent6Q4Prefix.sideBit_ge_length
        (s0RightFacing 0) i (by omega)
    calc
      U.tape (h+6+(3*b:Int)+(i:Int)) = U.tape x := by rfl
      _ = T2 x := hframe
      _ = T1 x := hscan
      _ = T x := hfirst
      _ = false := by
        rw [hidx]
        exact hzero
      _ = sideBit (s0RightFacing 0) i := htarget.symm

/-- Source-run version of the right-facing endpoint lemma. -/
theorem q4_suffix_run_right_word (T : Int → Bool) (h : Int) (b : Nat)
    (hshape : q4RightShape T h b)
    (htail : ∀ i : Nat, 9+3*b ≤ i →
      T (h+1+(i:Int)) = false) :
    ∃ U,
      run BB6Coverage.Agent48Champion.tm2 (39+3*b) ⟨4,h,T⟩ = some U ∧
      (∀ i : Nat,
        U.tape (h+6+(3*b:Int)+(i:Int)) =
          sideBit (s0RightFacing 0) i) := by
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  refine ⟨U, ?_, ?_⟩
  · exact q4_suffix_frame T h b hshape
  · simpa [U, T1, T2, g] using q4_suffix_right_word T h b hshape htail

/-- Direct interface from Agent 6's exported prefix stream to the
    source-connected q4 suffix right endpoint. -/
theorem q4_suffix_run_right_word_of_prefix
    (Tq : Int → Bool) (h : Int) (b : Nat)
    (hshape : q4RightShape Tq h b)
    (hright : ∀ i : Nat,
      Tq (h+1+(i:Int)) =
        BB6Coverage.Agent8S1Encoder.sideBit
          (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i) :
    ∃ U,
      run BB6Coverage.Agent48Champion.tm2 (39+3*b) ⟨4,h,Tq⟩ = some U ∧
      (∀ i : Nat,
        U.tape (h+6+(3*b:Int)+(i:Int)) =
          sideBit (s0RightFacing 0) i) := by
  exact q4_suffix_run_right_word Tq h b hshape
    (q4_prefix_far_tail b Tq h hright)

#print axioms q4_prefix_far_tail
#print axioms q4_suffix_right_word
#print axioms q4_suffix_run_right_word
#print axioms q4_suffix_run_right_word_of_prefix

/-- The first-ten frame marks every cell from its head through five cells
to the right. -/
private theorem q4Endpoint_first10_six (T : Int → Bool) (h : Int)
    (i : Nat) (hi : i < 6) :
    (frameAt T h q4First10Inside q4First10End).tape
      (h+(i:Int)) = true := by
  have hcases :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rw [frameAt_tape]
  have hcoord : (h+(i:Int))-h = (i:Int) := by omega
  rw [hcoord]
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 <;>
    subst i <;>
    simp [q4First10Inside, q4First10End]

/-- The q4 suffix preserves the entire left-facing tape stream.  The
nearest 3*b cells are the periodic d0 output of the counted scan; the next
six are the fixed all-one bridge; everything farther left is the q4
prefix's original stream with its consumed head cell removed. -/
theorem q4_suffix_left_word
    (T : Int → Bool) (h : Int) (b L n a : Nat)
    (hleft : ∀ i : Nat,
      T (h-(i:Int)) = sideBit (q4LeftFacing L n a) i) :
    ∀ i : Nat,
      (frameAt
        (d0Sweep b
          (frameAt T h q4First10Inside q4First10End).tape
          (h+10))
        (h+10+(3*b:Int)) q4TailInside q4TailEnd).tape
          (h+5+(3*b:Int)-(i:Int)) =
      sideBit (s1LeftFacing L n 1 (a+b+2) (2^b-1)) i := by
  intro i
  rw [q4SuffixTargetLeft L n a b]
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  let x : Int := h+5+(3*b:Int)-(i:Int)
  have hxFrame : x < g-4 := by
    dsimp [x,g]
    omega
  have hU : U.tape x = T2 x := by
    dsimp [U]
    rw [frameAt_tape]
    have hnot : q4TailInside (x-g) = false := by
      simp [q4TailInside]
      omega
    simp [hnot]
  have hlen0 : (d0pow b).length = 3*b :=
    q4Endpoint_d0pow_length b
  have hlen1 : (d1pow 2).length = 6 := by
    simp [d1pow, d1]
  let tail := (q4LeftFacing L n a).drop 1
  by_cases hi0 : i < 3*b
  · have hside :
        sideBit (d0pow b ++ d1pow 2 ++ tail) i =
          sideBit (d0pow b) i := by
      rw [List.append_assoc]
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_left
        (d0pow b) (d1pow 2 ++ tail) i (by rw [hlen0]; omega)]
    have hcell : T2 x = sideBit (d0pow b) i := by
      have hperiod : T2 x = decide (i % 3 = 2) := by
        by_cases hscan : h+10 ≤ x
        · let d : Nat := 3*b-5-i
          have hdi : i ≤ 3*b-5 := by
            dsimp [x] at hscan
            omega
          have hxcoord : x = h+10+(d:Int) := by
            dsimp [x,d]
            omega
          let j : Nat := d/3
          let r : Nat := d%3
          have hdiv : d = 3*j+r := by
            dsimp [j,r,d]
            omega
          have hj : j < b := by
            dsimp [j,d]
            omega
          have hrcases : r=0 ∨ r=1 ∨ r=2 := by
            dsimp [r,d]
            omega
          obtain ⟨hb0,hb1,hb2⟩ :=
            d0Sweep_block b T1 (h+10) j hj
          rcases hrcases with hr0 | hr1 | hr2
          · have hx0 : x = h+10+(3*(j:Int)) := by
              rw [hxcoord]
              have hdEq : d = 3*j := by
                rw [hdiv,hr0]
                omega
              omega
            have hiMod : i%3=1 := by
              dsimp [r,d] at hr0
              omega
            rw [hx0]
            simpa [T2,hiMod] using hb0
          · have hx1 : x = h+10+(3*(j:Int))+1 := by
              rw [hxcoord]
              have hdEq : d = 3*j+1 := by
                rw [hdiv,hr1] <;> omega
              omega
            have hiMod : i%3=0 := by
              dsimp [r,d] at hr1
              omega
            rw [hx1]
            simpa [T2,hiMod] using hb1
          · have hx2 : x = h+10+(3*(j:Int))+2 := by
              rw [hxcoord]
              have hdEq : d = 3*j+2 := by
                rw [hdiv,hr2] <;> omega
              omega
            have hiMod : i%3=2 := by
              dsimp [r,d] at hr2
              omega
            rw [hx2]
            simpa [T2,hiMod] using hb2
        · have hlow : x < h+10 := by omega
          let j : Nat := 3*b-i
          have hjrange : 1 ≤ j ∧ j ≤ 4 := by
            dsimp [j]
            dsimp [x] at hlow
            omega
          have hcells := q4First10_cells T h
          have hcases : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
          rcases hcases with hj1 | hj2 | hj3 | hj4
          · have hx6 : x=h+6 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=2 := by
              dsimp [j] at hj1
              omega
            have hT1 : T1 (h+6)=true := by
              simpa [T1] using hcells.2.1
            have hbefore : T2 (h+6)=T1 (h+6) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+6) (by omega)
            rw [hx6,hbefore,hT1]
            simp [hiMod]
          · have hx7 : x=h+7 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=1 := by
              dsimp [j] at hj2
              omega
            have hT1 : T1 (h+7)=false := by
              simpa [T1] using hcells.2.2.1
            have hbefore : T2 (h+7)=T1 (h+7) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+7) (by omega)
            rw [hx7,hbefore,hT1]
            simp [hiMod]
          · have hx8 : x=h+8 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=0 := by
              dsimp [j] at hj3
              omega
            have hT1 : T1 (h+8)=false := by
              simpa [T1] using hcells.2.2.2.1
            have hbefore : T2 (h+8)=T1 (h+8) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+8) (by omega)
            rw [hx8,hbefore,hT1]
            simp [hiMod]
          · have hx9 : x=h+9 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=2 := by
              dsimp [j] at hj4
              omega
            have hT1 : T1 (h+9)=true := by
              simpa [T1] using hcells.2.2.2.2
            have hbefore : T2 (h+9)=T1 (h+9) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+9) (by omega)
            rw [hx9,hbefore,hT1]
            simp [hiMod]
      exact hperiod.trans
        (q4Endpoint_sideBit_d0pow_mod b i hi0).symm
    calc
      U.tape x = T2 x := hU
      _ = sideBit (d0pow b) i := hcell
      _ = sideBit (d0pow b ++ d1pow 2 ++ tail) i := hside.symm
  · by_cases hi1 : i < 3*b+6
    · have hside :
          sideBit (d0pow b ++ d1pow 2 ++ tail) i = true := by
        rw [List.append_assoc]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d0pow b) (d1pow 2 ++ tail) i (by rw [hlen0]; omega)]
        rw [hlen0]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_left
          (d1pow 2) tail (i-3*b) (by rw [hlen1]; omega)]
        exact BB6Coverage.Agent6Q4Prefix.sideBit_d1pow_true
          2 (i-3*b) (by omega)
      have hcell : T2 x = true := by
        have hbefore : T2 x = T1 x := by
          dsimp [T2]
          exact d0Sweep_before b T1 (h+10) x (by dsimp [x]; omega)
        let j : Nat := i-3*b
        let k : Nat := 5-j
        have hj : j<6 := by dsimp [j]; omega
        have hk : k<6 := by dsimp [k,j]; omega
        have hxk : x=h+(k:Int) := by
          dsimp [x,k,j]
          omega
        have hT1 : T1 x=true := by
          rw [hxk]
          simpa [T1] using q4Endpoint_first10_six T h k hk
        exact hbefore.trans hT1
      calc
        U.tape x = T2 x := hU
        _ = true := hcell
        _ = sideBit (d0pow b ++ d1pow 2 ++ tail) i := hside.symm
    · let j : Nat := i-(3*b+6)
      have hside :
          sideBit (d0pow b ++ d1pow 2 ++ tail) i =
            sideBit tail j := by
        rw [List.append_assoc]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d0pow b) (d1pow 2 ++ tail) i (by rw [hlen0]; omega)]
        rw [hlen0]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d1pow 2) tail (i-3*b) (by rw [hlen1]; omega)]
        rw [hlen1]
        have hidx : (i-3*b)-6 = j := by
          dsimp [j]
          omega
        rw [hidx]
      have hcell : T2 x = sideBit tail j := by
        have hbefore : T2 x = T1 x := by
          dsimp [T2]
          exact d0Sweep_before b T1 (h+10) x (by dsimp [x]; omega)
        have hfirst : T1 x = T x := by
          dsimp [T1]
          rw [frameAt_tape]
          have hnot : q4First10Inside (x-h) = false := by
            simp [q4First10Inside]
            dsimp [x]
            omega
          simp [hnot]
        have hxcoord : x = h-((j+1:Int)) := by
          dsimp [x,j]
          omega
        have hprefix : T x = sideBit (q4LeftFacing L n a) (j+1) := by
          rw [hxcoord]
          exact hleft (j+1)
        have hdrop := q4Endpoint_sideBit_drop_one
          (q4LeftFacing L n a) j
        calc
          T2 x = T1 x := hbefore
          _ = T x := hfirst
          _ = sideBit (q4LeftFacing L n a) (j+1) := hprefix
          _ = sideBit tail j := hdrop.symm
      calc
        U.tape x = T2 x := hU
        _ = sideBit tail j := hcell
        _ = sideBit (d0pow b ++ d1pow 2 ++ tail) i := hside.symm

/-- Source-run version of the complete left-facing q4 suffix endpoint. -/
theorem q4_suffix_run_left_word (T : Int → Bool) (h : Int) (b L n a : Nat)
    (hshape : q4RightShape T h b)
    (hleft : ∀ i : Nat,
      T (h-(i:Int)) = sideBit (q4LeftFacing L n a) i) :
    ∃ U,
      run BB6Coverage.Agent48Champion.tm2 (39+3*b) ⟨4,h,T⟩ = some U ∧
      (∀ i : Nat,
        U.tape (h+5+(3*b:Int)-(i:Int)) =
          sideBit (s1LeftFacing L n 1 (a+b+2) (2^b-1)) i) := by
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  refine ⟨U, ?_, ?_⟩
  · exact q4_suffix_frame T h b hshape
  · simpa [U,T1,T2,g] using q4_suffix_left_word T h b L n a hleft

/-- Compose the parameter-uniform odd-Rst2 q4 prefix and suffix into an
exact original-source S1-to-S1 run.  This closes the entire q4 macro,
including both infinite tape exteriors, rather than only its finite frame. -/
theorem q4_suffix_run_target_of_prefix
    (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    ∃ Tq,
      run BB6Coverage.Agent48Champion.tm2 (32+12*a) (s1Config L n 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      run BB6Coverage.Agent48Champion.tm2 (39+3*b) ⟨4,h,Tq⟩ =
        some (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0
          (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hhead,hleft,hshape,hright⟩ :=
    BB6Coverage.Agent6Q4Prefix.oddRst2_q4_prefix
      L n a b h hn hbound
  let T1 := (frameAt Tq h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let H : Int := h+5+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  have hshape8 : BB6Coverage.Agent8Q4Suffix.q4RightShape Tq h b := by
    simpa [BB6Coverage.Agent6Q4Prefix.q4RightShape,
      BB6Coverage.Agent8Q4Suffix.q4RightShape] using hshape
  have hleft8 : ∀ i : Nat,
      Tq (h-(i:Int)) =
        sideBit (BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (n-1) a) i := by
    intro i
    simpa [BB6Coverage.Agent6Q4Prefix.q4LeftFacing,
      BB6Coverage.Agent8Q4Suffix.q4LeftFacing] using hleft i
  have htail := q4_prefix_far_tail b Tq h hright
  have hrightU :
      ∀ i : Nat, U.tape (h+6+(3*b:Int)+(i:Int)) =
        sideBit (s0RightFacing 0) i := by
    simpa [U,T1,T2,g] using
      q4_suffix_right_word Tq h b hshape8 htail
  have hleftU :
      ∀ i : Nat, U.tape (h+5+(3*b:Int)-(i:Int)) =
        sideBit (s1LeftFacing L (n-1) 1 (a+b+2) (2^b-1)) i := by
    simpa [U,T1,T2,g] using
      q4_suffix_left_word Tq h b L (n-1) a hleft8
  have hsuffix : run BB6Coverage.Agent48Champion.tm2 (39+3*b) ⟨4,h,Tq⟩ = some U := by
    exact q4_suffix_frame Tq h b hshape8
  have htarget : U =
      s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 H := by
    apply config_ext
    · simp [U,frameAt_state,q4TailEnd]
    · simp [U,frameAt_head,q4TailEnd,g,H] <;> omega
    · funext x
      by_cases hx : x ≤ H
      · let i : Nat := Int.toNat (H-x)
        have hcoord : x = H-(i:Int) := by
          dsimp [i]
          omega
        rw [hcoord]
        have hleftCell :
            U.tape (H-(i:Int)) =
              (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 H).tape
                (H-(i:Int)) := by
          calc
            U.tape (H-(i:Int)) =
                U.tape (h+5+(3*b:Int)-(i:Int)) := by simp [H]
            _ = sideBit (s1LeftFacing L (n-1) 1 (a+b+2) (2^b-1)) i :=
              hleftU i
            _ = (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 H).tape
                  (H-(i:Int)) :=
              (s1Config_left_cell L (n-1) 1 (a+b+2) (2^b-1) 0 H i).symm
        exact hleftCell
      · let i : Nat := Int.toNat (x-H-1)
        have hcoord : x = H+1+(i:Int) := by
          dsimp [i]
          omega
        rw [hcoord]
        calc
          U.tape (H+1+(i:Int)) =
              sideBit (s0RightFacing 0) i := by
                have hr := hrightU i
                have hrightCoord :
                    h+6+(3*b:Int)+(i:Int) = H+1+(i:Int) := by
                  dsimp [H]
                  omega
                rw [hrightCoord] at hr
                exact hr
          _ = sideBit (s1PhysicalRight 0) i := by
                rfl
          _ = (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 H).tape
                (H+1+(i:Int)) := by
                exact (s1Config_right_cell
                  L (n-1) 1 (a+b+2) (2^b-1) 0 H i).symm
  refine ⟨Tq,hprefix,?_⟩
  rw [hsuffix,htarget]

/-- Counted source theorem for the complete odd-Rst2 q4 macro. -/
theorem oddRst2_q4_counted_source
    (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    run BB6Coverage.Agent48Champion.tm2 (71+12*a+3*b) (s1Config L n 2 a 0 b h) =
      some (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hsuffix⟩ :=
    q4_suffix_run_target_of_prefix L n a b h hn hbound
  have hsum : 71+12*a+3*b = (32+12*a)+(39+3*b) := by omega
  rw [hsum,BB6Coverage.Agent8CountedReset.run_add,hprefix]
  simpa using hsuffix

#print axioms q4_suffix_left_word
#print axioms q4_suffix_run_left_word
#print axioms q4_suffix_run_target_of_prefix
#print axioms oddRst2_q4_counted_source



/-- Authentic TM63 root instance of the complete q4 source transition. -/
theorem tm2_q4_root_source :
    run BB6Coverage.Agent48Champion.tm2 332 (s1Config 3 7 2 6 0 63 29) =
      some (s1Config 3 6 1 71 (2^63-1) 0 223) := by
  simpa using
    (oddRst2_q4_counted_source 3 7 6 63 29
      (by decide) (by decide))

#print axioms tm2_q4_root_source

end BB6Coverage.Agent24Q4Endpoint
