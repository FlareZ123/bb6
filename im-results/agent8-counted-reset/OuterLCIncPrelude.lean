import S1Encoder
import CountedLBinDecHRun
import CountedOddBase
import CountedReset
import CostRecurrence
import Lean.Elab.Tactic.Omega

/-!
A source-table proof of the outer TM63 reset prefix through the universal
D-to-B LBinDec H-run.  The three marker bridges are finite original-table
traces, lifted to arbitrary infinite tapes by the checked run_frame theorem.
The outer counter is factored uniformly using S1Encoder's odd-factor lemma.
This is an intermediate source theorem: it does not yet prove the subsequent
return/transfer postlude or the full Inc0 macro.
-/

namespace BB6Coverage.Agent8OuterLCInc

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic

/-- Fieldwise extensionality for the concrete TM63 configuration structure. -/
private theorem config_ext {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk s h t =>
      cases d with
      | mk s' h' t' =>
          simp_all

/-- Moving the index past a list prefix selects the same cell in the suffix. -/
theorem outer_sideBit_append_shift (xs ys : List Bool) (i : Nat) :
    sideBit (xs ++ ys) (xs.length+i) = sideBit ys i := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      simp only [List.length_cons, Nat.succ_add, List.cons_append, sideBit]
      exact ih i

/-- A suffix cannot affect an index strictly inside the list prefix. -/
theorem outer_sideBit_append_prefix (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simp only [List.cons_append, sideBit]
          exact ih i hi

/-- Every cell in the repeated unary-one word is one. -/
theorem outer_sideBit_d1pow (a i : Nat) (hi : i < 3*a) :
    sideBit (d1pow a) i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih =>
      by_cases h : i < 3
      · have hi0 : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hi0 with hi0 | hi0 | hi0 <;> subst i <;>
          simp [d1pow,d1,sideBit]
      · have hi' : i-3 < 3*a := by omega
        have heq : i = 3 + (i-3) := by omega
        rw [heq]
        change sideBit (d1 ++ d1pow a) (d1.length+(i-3)) = true
        rw [outer_sideBit_append_shift]
        exact ih (i-3) hi'

/-- The S1 tape immediately to the left of the D head exposes marker ++ d0
after the initial unary a-block. -/
private theorem outer_markerWord_length (m : Nat) (hm : m < 3) :
    (markerWord m).length = m+2 := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hm0 with h0 | h1 | h2 <;> subst m <;> simp [markerWord]

theorem outer_s1_marker_prefix_cell (L n m a b : Nat) (h : Int)
    (hm : m < 3) (i : Nat) (hi : i ≤ m+4) :
    (s1Config L n m a 0 b h).tape
      (h-((3*a+i):Int)) = sideBit (markerWord m ++ d0) i := by
  have hcell := s1Config_left_cell L n m a 0 b h (3*a+i)
  push_cast at hcell
  have hword : s1LeftFacing L n m a 0 =
      d1pow a ++ (markerWord m ++ d0 ++ binDec L n ++ lh) := by
    simp [s1LeftFacing,binDec_zero,List.append_assoc]
  rw [hword] at hcell
  rw [← d1pow_length a] at hcell
  rw [outer_sideBit_append_shift] at hcell
  have hmarker : (markerWord m).length = m+2 :=
    outer_markerWord_length m hm
  have hlen : (markerWord m ++ d0).length = m+5 := by
    simp [hmarker,d0] <;> omega
  have hi' : i < (markerWord m ++ d0).length := by omega
  have hrest : markerWord m ++ d0 ++ binDec L n ++ lh =
      (markerWord m ++ d0) ++ (binDec L n ++ lh) := by
    simp [List.append_assoc]
  rw [hrest] at hcell
  rw [outer_sideBit_append_prefix _ _ _ hi'] at hcell
  exact hcell

/-- At the exact start of the outer binary counter, the source tape is
the corresponding head-facing bit of BinDec(L,n) ++ lh. -/
theorem outer_s1_counter_cell (L n m a b : Nat) (h : Int)
    (hm : m < 3) (i : Nat) :
    (s1Config L n m a 0 b h).tape
      (h-((3*a+m+5+i):Int)) = sideBit (binDec L n ++ lh) i := by
  have hcell := s1Config_left_cell L n m a 0 b h (3*a+m+5+i)
  push_cast at hcell
  have hword : s1LeftFacing L n m a 0 =
      (d1pow a ++ markerWord m ++ d0) ++ (binDec L n ++ lh) := by
    simp [s1LeftFacing,binDec_zero,List.append_assoc]
  rw [hword] at hcell
  rw [← d1pow_length a] at hcell
  simp only [Nat.add_assoc] at hcell
  rw [outer_sideBit_append_shift] at hcell
  have hmarker : (markerWord m).length = m+2 :=
    outer_markerWord_length m hm
  have hlen : (d1pow a ++ markerWord m ++ d0).length =
      3*a+m+5 := by
    simp [d1pow_length,hmarker,d0] <;> omega
  rw [← hlen] at hcell
  rw [outer_sideBit_append_shift] at hcell
  exact hcell

/-- Under the odd-factor decomposition of n, the outer counter starts
with d1^r ++ d0 exactly, not merely with a finite sampled prefix. -/
theorem outer_s1_counter_carry_cell
    (L n m a b : Nat) (h : Int) (hm : m < 3)
    (q r len i : Nat)
    (hn : n = (2*q+1)*2^r) (hL : L = len+1+r)
    (hq : q < 2^len) :
    (s1Config L n m a 0 b h).tape
      (h-((3*a+m+5+i):Int)) =
      sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) i := by
  rw [outer_s1_counter_cell L n m a b h hm i]
  have hbin : binDec L n = d1pow r ++ d0 ++ binDec len q := by
    rw [hL,hn]
    exact binDec_carryPrefix len q r hq
  rw [hbin]

/-- Finite D-to-D bridge inputs for the three source marker words.  The
right neighbour is the zero left by the counted unary sweep. -/
def markerBridgeInput (m : Nat) : FConfig :=
  if m % 3 = 0 then ⟨3,0,[-1,-4]⟩
  else if m % 3 = 1 then ⟨3,0,[0,-2,-5]⟩
  else ⟨3,0,[0,-1,-3,-6]⟩

/-- Exact finite outputs of the marker bridges. -/
theorem markerBridgeInput_tape (m : Nat) (hm : m < 3) (i : Nat)
    (hi : i ≤ m+4) :
    (embed (markerBridgeInput m)).tape (-(i:Int)) =
      sideBit (markerWord m ++ d0) i := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  have hi0 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
  rcases hm0 with hm0 | hm0 | hm0 <;> subst m <;>
    rcases hi0 with hi0 | hi0 | hi0 | hi0 | hi0 | hi0 | hi0 <;>
    subst i <;> simp [embed,markerBridgeInput,markerWord,d0,sideBit] <;> omega

def markerBridgeOutput (m : Nat) : FConfig :=
  if m % 3 = 0 then ⟨3,-5,[-3,-2,-1,0]⟩
  else if m % 3 = 1 then ⟨3,-6,[-4,-3,-2,-1,1]⟩
  else ⟨3,-7,[-5,-4,-3,-2,0,1]⟩

/-- The complete read window for the marker bridge, relative to its D head. -/
def markerBridgeInside (m : Nat) (x : Int) : Bool :=
  decide (-(m+4:Int) ≤ x ∧ x ≤ 1)

def markerBridgeInsideAt (m : Nat) (h0 x : Int) : Bool :=
  markerBridgeInside m (x-h0)

def markerBridgeFrameIn (m : Nat) (T : Int → Bool) (h0 : Int) : Config :=
  frame (markerBridgeInsideAt m h0) T
    (shiftConfig h0 (embed (markerBridgeInput m)))

def markerBridgeFrameOut (m : Nat) (T : Int → Bool) (h0 : Int) : Config :=
  frame (markerBridgeInsideAt m h0) T
    (shiftConfig h0 (embed (markerBridgeOutput m)))

/-- The three marker cases are exact finite original-TM63 traces. -/
theorem markerBridge_finite (m : Nat) (hm : m < 3) :
    fRun tm2 (3*m+17) (markerBridgeInput m) =
      some (markerBridgeOutput m) := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hm0 with h0 | h1 | h2 <;> subst m <;> decide

/-- Every head query in each finite marker bridge stays in its checked
window.  The finite-list interpreter is connected to the full tape by
finite_run_source. -/
theorem markerBridge_heads (m : Nat) (hm : m < 3) :
    ∀ k, k<3*m+17 → ∀ d,
      run tm2 k (embed (markerBridgeInput m)) = some d →
      markerBridgeInside m d.head = true := by
  intro k hk d hd
  have hcheck : (List.range (3*m+17)).all (fun k =>
      match fRun tm2 k (markerBridgeInput m) with
      | none => true
      | some z => markerBridgeInside m z.head) = true := by
    have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
    rcases hm0 with h0 | h1 | h2 <;> subst m <;> decide
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := finite_run_source tm2 k (markerBridgeInput m)
  cases hrun : fRun tm2 k (markerBridgeInput m) with
  | none =>
      simp only [hrun,Option.map_none] at hsource
      rw [← hsource] at hd
      cases hd
  | some z =>
      simp only [hrun,Option.map_some] at hsource
      have hd' := Option.some.inj (hsource.trans hd)
      subst d
      simpa [hrun,embed] using hitem

/-- The marker bridge lifted to arbitrary infinite tape backgrounds. -/
theorem markerBridge_run (m : Nat) (hm : m < 3)
    (T : Int → Bool) (h0 : Int) :
    run tm2 (3*m+17) (markerBridgeFrameIn m T h0) =
      some (markerBridgeFrameOut m T h0) := by
  have hin : ∀ k, k<3*m+17 → ∀ d,
      run tm2 k (shiftConfig h0 (embed (markerBridgeInput m))) = some d →
      markerBridgeInsideAt m h0 d.head = true := by
    intro k hk d hd
    rw [shift_run] at hd
    cases hr : run tm2 k (embed (markerBridgeInput m)) with
    | none => simp [hr] at hd
    | some d0 =>
        simp [hr] at hd
        have hlocal := markerBridge_heads m hm k hk d0 hr
        have heq : shiftConfig h0 d0 = d := hd
        subst d
        simpa [markerBridgeInsideAt,shiftConfig] using hlocal
  have hfr := run_frame tm2 (markerBridgeInsideAt m h0) T
    (shiftConfig h0 (embed (markerBridgeInput m))) (3*m+17) hin
  have hbase :
      run tm2 (3*m+17) (shiftConfig h0 (embed (markerBridgeInput m))) =
        some (shiftConfig h0 (embed (markerBridgeOutput m))) := by
    rw [shift_run]
    rw [← finite_run_source tm2 (3*m+17) (markerBridgeInput m)]
    rw [markerBridge_finite m hm]
    rfl
  change run tm2 (3*m+17)
      (frame (markerBridgeInsideAt m h0) T
        (shiftConfig h0 (embed (markerBridgeInput m)))) =
    some (frame (markerBridgeInsideAt m h0) T
      (shiftConfig h0 (embed (markerBridgeOutput m))))
  rw [hfr,hbase]
  rfl

/-- The finite marker input has a zero immediately to the right of D. -/
theorem markerBridgeInput_right_zero (m : Nat) (hm : m < 3) :
    (embed (markerBridgeInput m)).tape 1 = false := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hm0 with h0 | h1 | h2 <;> subst m <;> decide

/-- The framed marker output always has state D and head h0-(m+5). -/
theorem markerBridgeFrameOut_state (m : Nat) (hm : m < 3)
    (T : Int → Bool) (h0 : Int) :
    (markerBridgeFrameOut m T h0).state = 3 := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hm0 with h0' | h1 | h2 <;> subst m <;>
    simp [markerBridgeFrameOut,frame,shiftConfig,embed,markerBridgeOutput]

theorem markerBridgeFrameOut_head (m : Nat) (hm : m < 3)
    (T : Int → Bool) (h0 : Int) :
    (markerBridgeFrameOut m T h0).head = h0-(m+5:Int) := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hm0 with h0' | h1 | h2 <;> subst m <;>
    simp [markerBridgeFrameOut,frame,shiftConfig,embed,markerBridgeOutput] <;> omega

/-- The marker bridge clears the final d0 cell, producing the right-zero
boundary required by counted_LBinDec_HRun. -/
theorem markerBridgeFrameOut_right_zero (m : Nat) (hm : m < 3)
    (T : Int → Bool) (h0 : Int) :
    (markerBridgeFrameOut m T h0).tape (h0-(m+5:Int)+1) = false := by
  have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
  rcases hm0 with h0' | h1 | h2
  · subst m
    have hcoord : h0-5+1-h0 = -4 := by omega
    simp [markerBridgeFrameOut,frame,markerBridgeInsideAt,markerBridgeInside,
      shiftConfig,embed,markerBridgeOutput,hcoord]
  · subst m
    have hcoord : h0-6+1-h0 = -5 := by omega
    simp [markerBridgeFrameOut,frame,markerBridgeInsideAt,markerBridgeInside,
      shiftConfig,embed,markerBridgeOutput,hcoord]
  · subst m
    have hcoord : h0-7+1-h0 = -6 := by omega
    simp [markerBridgeFrameOut,frame,markerBridgeInsideAt,markerBridgeInside,
      shiftConfig,embed,markerBridgeOutput,hcoord]

/-- Everything strictly to the left of the bridge window is inherited from
the source tape; the preceding counted sweep has not touched it. -/
theorem markerBridgeFrameOut_preserves_source
    (m a : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≤ h-(3*a:Int)-(m+5:Int)) :
    (markerBridgeFrameOut m (sweptLeft (3*a) T h)
      (h-(3*a:Int))).tape x = T x := by
  have hlt : x-(h-(3*a:Int)) < -(m+4:Int) := by omega
  have hfalse : markerBridgeInsideAt m (h-(3*a:Int)) x = false := by
    simp [markerBridgeInsideAt,markerBridgeInside]
    omega
  change (frame (markerBridgeInsideAt m (h-(3*a:Int)))
    (sweptLeft (3*a) T h)
    (shiftConfig (h-(3*a:Int)) (embed (markerBridgeOutput m)))).tape x = T x
  simp only [frame,hfalse]
  exact sweptLeft_preserves_left (3*a) T h x (by omega)

/-- The actual S1 configuration after the counted 3a-cell left sweep is
exactly the framed finite marker-bridge input.  This is the point where
arbitrary source tails and arbitrary right-hand tape are retained. -/
theorem outer_afterSweep_eq_markerBridgeFrameIn
    (L n m a b : Nat) (h : Int) (hm : m < 3) :
    markerBridgeFrameIn m
      (sweptLeft (3*a) (s1Config L n m a 0 b h).tape h)
      (h-(3*a:Int)) =
    ⟨3,h-(3*a:Int),
      sweptLeft (3*a) (s1Config L n m a 0 b h).tape h⟩ := by
  let T : Int → Bool := (s1Config L n m a 0 b h).tape
  let h0 : Int := h-(3*a:Int)
  let T1 : Int → Bool := sweptLeft (3*a) T h
  apply config_ext
  · have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
    rcases hm0 with h0' | h1 | h2 <;> subst m <;>
      simp [markerBridgeFrameIn,frame,shiftConfig,embed,markerBridgeInput]
  · have hm0 : m=0 ∨ m=1 ∨ m=2 := by omega
    rcases hm0 with h0' | h1 | h2 <;> subst m <;>
      simp [markerBridgeFrameIn,frame,shiftConfig,embed,markerBridgeInput]
  · funext x
    change (if markerBridgeInsideAt m h0 x then
      (shiftConfig h0 (embed (markerBridgeInput m))).tape x else T1 x) = T1 x
    by_cases hinside : markerBridgeInsideAt m h0 x = true
    · simp only [hinside]
      have hbounds : -(m+4:Int) ≤ x-h0 ∧ x-h0 ≤ 1 := by
        simpa [markerBridgeInsideAt,markerBridgeInside] using hinside
      by_cases hle : x ≤ h0
      · let i : Nat := Int.toNat (h0-x)
        have hnon : 0 ≤ h0-x := by omega
        have hcast : (i:Int) = h0-x := by
          dsimp [i]
          exact Int.toNat_of_nonneg hnon
        have hi : i ≤ m+4 := by
          dsimp [i]
          omega
        have hcoord : x = h-((3*a+i):Int) := by
          dsimp [h0] at hcast
          omega
        have hsweep : T1 x = T x := by
          dsimp [T1]
          apply sweptLeft_preserves_left
          dsimp [h0] at hle
          omega
        have hcell := outer_s1_marker_prefix_cell L n m a b h hm i hi
        have hsource : T x = sideBit (markerWord m ++ d0) i := by
          rw [hcoord]
          simpa [T] using hcell
        have hbase := markerBridgeInput_tape m hm i hi
        have hrel : x-h0 = -(i:Int) := by omega
        calc
          (shiftConfig h0 (embed (markerBridgeInput m))).tape x =
              (embed (markerBridgeInput m)).tape (x-h0) := rfl
          _ = sideBit (markerWord m ++ d0) i := by rw [hrel]; exact hbase
          _ = T x := hsource.symm
          _ = T1 x := hsweep.symm
      · have hx : x = h0+1 := by omega
        subst x
        have hr : T (h+1) = false := by
          have hc := s1Config_right_cell L n m a 0 b h 0
          simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
        have hzero : T1 (h0+1) = false := by
          dsimp [T1]
          exact sweptLeft_boundary_right_zero (3*a) T h hr
        have hbase := markerBridgeInput_right_zero m hm
        have hcoord : h0+1-h0 = 1 := by omega
        simp [shiftConfig,hcoord,hbase,hzero]
    · have hfalse : markerBridgeInsideAt m h0 x = false := by
        cases hb : markerBridgeInsideAt m h0 x <;> simp_all
      simp [hfalse]

/-- The output tape preserves every source cell at or left of the H-run
head, including the complete d1^r ++ d0 outer-counter boundary. -/
theorem outer_markerBridge_preserves_source
    (L n m a b : Nat) (h : Int) (hm : m < 3) (x : Int)
    (hx : x ≤ h-(3*a:Int)-(m+5:Int)) :
    (markerBridgeFrameOut m
      (sweptLeft (3*a) (s1Config L n m a 0 b h).tape h)
      (h-(3*a:Int))).tape x =
      (s1Config L n m a 0 b h).tape x := by
  exact markerBridgeFrameOut_preserves_source m a
    (s1Config L n m a 0 b h).tape h x hx

/-- The outer S1 prefix reaches the universal LBinDec H-run.  The exact
cost through this point is 9a+3m+17+12*v₂(n)+4. -/
theorem outerLCInc_preHRun
    (L n m a b : Nat) (h : Int)
    (hm : m < 3) (hn0 : 0 < n) (hnlt : n < 2^L) :
    ∃ q r len, n = (2*q+1)*2^r ∧ L = len+1+r ∧ q < 2^len ∧
      v2 n = r ∧
      run tm2 (9*a+3*m+17+12*v2 n+4)
        (s1Config L n m a 0 b h) =
      some ⟨1,h-(3*a+m+5:Int)+2,
        lbinDecHRunTape (v2 n)
          (markerBridgeFrameOut m
            (sweptLeft (3*a) (s1Config L n m a 0 b h).tape h)
            (h-(3*a:Int))).tape
          (h-(3*a+m+5:Int))⟩ := by
  obtain ⟨q,r,len,hn,hL,hq⟩ :=
    exists_odd_factor_bounded L n hn0 hnlt
  have hv2 : v2 n = r := by
    rw [hn]
    exact v2_odd_factor q r
  refine ⟨q,r,len,hn,hL,hq,hv2,?_⟩
  rw [hv2]
  let T : Int → Bool := (s1Config L n m a 0 b h).tape
  let h0 : Int := h-(3*a:Int)
  let h1 : Int := h0-(m+5:Int)
  let T1 : Int → Bool := sweptLeft (3*a) T h
  let T2 : Int → Bool := (markerBridgeFrameOut m T1 h0).tape
  have hr : T (h+1) = false := by
    have hc := s1Config_right_cell L n m a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hones : leftOnes T h (3*a) := by
    intro i hi
    have hc := s1Config_left_cell L n m a 0 b h i
    have hword : s1LeftFacing L n m a 0 =
        d1pow a ++ (markerWord m ++ d0 ++ binDec L n ++ lh) := by
      simp [s1LeftFacing,binDec_zero,List.append_assoc]
    rw [hword] at hc
    have hprefix : i < (d1pow a).length := by
      rw [d1pow_length]
      omega
    have hbit : sideBit (d1pow a ++
        (markerWord m ++ d0 ++ binDec L n ++ lh)) i = true := by
      rw [outer_sideBit_append_prefix _ _ _ hprefix]
      exact outer_sideBit_d1pow a i (by exact hi)
    simpa [T] using hc.trans hbit
  have hsweep :
      run tm2 (9*a) (s1Config L n m a 0 b h) =
        some ⟨3,h0,T1⟩ := by
    have hs := counted_left_sweep (3*a) T h hones hr
    have hcost : 3*(3*a)=9*a := by omega
    simpa [T,h0,T1,hcost,s1Config,s0Config] using hs
  have hframe :
      markerBridgeFrameIn m T1 h0 = ⟨3,h0,T1⟩ := by
    simpa [T,T1,h0] using
      outer_afterSweep_eq_markerBridgeFrameIn L n m a b h hm
  have hbridge :
      run tm2 (3*m+17) ⟨3,h0,T1⟩ =
        some (markerBridgeFrameOut m T1 h0) := by
    rw [← hframe]
    exact markerBridge_run m hm T1 h0
  have hcfg :
      markerBridgeFrameOut m T1 h0 = ⟨3,h1,T2⟩ := by
    cases hOut : markerBridgeFrameOut m T1 h0 with
    | mk s hOutHead t =>
        have hs : s = 3 := by
          simpa [hOut] using markerBridgeFrameOut_state m hm T1 h0
        have hh : hOutHead = h1 := by
          simpa [hOut,h1,h0] using markerBridgeFrameOut_head m hm T1 h0
        subst s
        subst hOutHead
        simp [T2,hOut]
  have hbridge' :
      run tm2 (3*m+17) ⟨3,h0,T1⟩ = some ⟨3,h1,T2⟩ := by
    rw [hbridge,hcfg]
  have hpres : ∀ x, x≤h1 → T2 x = T x := by
    intro x hx
    have hp := outer_markerBridge_preserves_source L n m a b h hm x
      (by simpa [h0,h1] using hx)
    simpa [T,T1,T2,h0,h1] using hp
  have hright : T2 (h1+1) = false := by
    have hp := markerBridgeFrameOut_right_zero m hm T1 h0
    simpa [T2,h1,h0] using hp
  have hleft : leftOnes T2 h1 (3*r) := by
    intro i hi
    have hpi := hpres (h1-(i:Int)) (by omega)
    have hcell := outer_s1_counter_carry_cell L n m a b h hm q r len i
      hn hL hq
    have hcoord : h1-(i:Int) = h-((3*a+m+5+i):Int) := by
      dsimp [h1,h0]
      omega
    have hbit : sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) i = true := by
      have hprefix : i < (d1pow r).length := by
        rw [d1pow_length]
        omega
      have hrest : d1pow r ++ d0 ++ binDec len q ++ lh =
          d1pow r ++ (d0 ++ binDec len q ++ lh) := by
        simp [List.append_assoc]
      rw [hrest,outer_sideBit_append_prefix _ _ _ hprefix]
      exact outer_sideBit_d1pow r i (by exact hi)
    calc
      T2 (h1-(i:Int)) = T (h1-(i:Int)) := hpi
      _ = sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) i := by
        rw [hcoord]
        simpa [T] using hcell
      _ = true := hbit
  have hz0 : T2 (h1-(3*r:Int)) = false := by
    have hp := hpres (h1-(3*r:Int)) (by omega)
    have hcell := outer_s1_counter_carry_cell L n m a b h hm q r len (3*r)
      hn hL hq
    have hcoord : h1-(3*r:Int) = h-((3*a+m+5+3*r):Int) := by
      dsimp [h1,h0]
      omega
    have hbit : sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) (3*r) = false := by
      have hrest : d1pow r ++ d0 ++ binDec len q ++ lh =
          d1pow r ++ (d0 ++ binDec len q ++ lh) := by
        simp [List.append_assoc]
      rw [hrest, ← d1pow_length r]
      have hshift := outer_sideBit_append_shift
        (d1pow r) (d0 ++ binDec len q ++ lh) 0
      simpa [d0, sideBit] using hshift
    calc
      T2 (h1-(3*r:Int)) = T (h1-(3*r:Int)) := hp
      _ = sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) (3*r) := by
        rw [hcoord]
        simpa [T] using hcell
      _ = false := hbit
  have hz1 : T2 (h1-(3*r:Int)-1) = false := by
    have hp := hpres (h1-(3*r:Int)-1) (by omega)
    have hcell := outer_s1_counter_carry_cell L n m a b h hm q r len (3*r+1)
      hn hL hq
    have hcoord : h1-(3*r:Int)-1 =
        h-((3*a+m+5+(3*r+1)):Int) := by
      dsimp [h1,h0]
      omega
    have hbit :
        sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) (3*r+1) = false := by
      have hrest : d1pow r ++ d0 ++ binDec len q ++ lh =
          d1pow r ++ (d0 ++ binDec len q ++ lh) := by
        simp [List.append_assoc]
      rw [hrest,← d1pow_length r,outer_sideBit_append_shift]
      simp [d0,sideBit]
    calc
      T2 (h1-(3*r:Int)-1) = T (h1-(3*r:Int)-1) := hp
      _ = sideBit (d1pow r ++ d0 ++ binDec len q ++ lh) (3*r+1) := by
        rw [hcoord]
        simpa [T] using hcell
      _ = false := hbit
  have hhrun := counted_LBinDec_HRun r T2 h1 hleft hz0 hz1 hright
  have hcost : 9*a+3*m+17+12*r+4 =
      9*a+((3*m+17)+(12*r+4)) := by omega
  rw [hcost,run_append,hsweep]
  simp only [Option.bind_some]
  rw [run_append,hbridge']
  simp only [Option.bind_some]
  have hbase : h-(3*a:Int)-(m+5:Int) =
      h-(3*a+m+5:Int) := by omega
  have hhead : h-(3*a:Int)-(m+5:Int)+2 =
      h-(3*a+m+5:Int)+2 := by omega
  rw [← hhead,← hbase]
  simpa [T,T1,T2,h0,h1] using hhrun

#print axioms markerBridge_finite
#print axioms markerBridge_heads
#print axioms markerBridge_run
#print axioms outer_afterSweep_eq_markerBridgeFrameIn
#print axioms outerLCInc_preHRun

end BB6Coverage.Agent8OuterLCInc
