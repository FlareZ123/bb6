import RootShift
import ChampionRootBridge
import CountedSweep
import CountedOddBase
import S1Encoder
import CountedReset
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent8Rst1Prime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

/-- A finite interval in head-relative coordinates. -/
def inWindow (lo hi : Int) : Int → Bool :=
  fun x => decide (lo ≤ x ∧ x ≤ hi)

/-- Recenter an infinite tape at the current head. -/
def centerTape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => T (h+x)

/-- The exact infinite-tape result of applying a finite local frame at head h. -/
def frameAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c : FConfig) : Config :=
  shiftConfig h (frame inside (centerTape T h) (embed c))

theorem config_ext {c d : Config}
    (hs : c.state = d.state)
    (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      simp only at hs hh ht
      cases hs
      cases hh
      cases ht
      rfl

@[simp] theorem frameAt_state (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) :
    (frameAt T h inside c).state = c.state := by
  rfl

@[simp] theorem frameAt_head (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) :
    (frameAt T h inside c).head = c.head + h := by
  rfl

@[simp] theorem frameAt_tape (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int) :
    (frameAt T h inside c).tape x =
      (if inside (x-h) then decide (x-h ∈ c.marked) else T x) := by
  have hcoord : h + (x-h) = x := by omega
  simp [frameAt, frame, shiftConfig, centerTape, embed, hcoord]

/-- Lift finite trace head bounds to the original infinite-tape semantics. -/
theorem finiteHeads (inside : Int → Bool) (c : FConfig) (n : Nat)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true) :
    ∀ k, k<n → ∀ d, run tm2 k (embed c) = some d → inside d.head = true := by
  intro k hk d hd
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := finite_run_source tm2 k c
  cases hrun : fRun tm2 k c with
  | none =>
      simp only [hrun, Option.map_none] at hsource
      rw [← hsource] at hd
      cases hd
  | some f =>
      simp only [hrun, Option.map_some] at hsource
      have hd' := Option.some.inj (hsource.trans hd)
      subst d
      simpa [hrun, embed] using hitem

/-- A finite TM63 trace, together with a head-window certificate, acts on
an arbitrary surrounding tape without any finite-tape approximation. -/
theorem finiteBridgeFrame (inside background : Int → Bool)
    (c d : FConfig) (n : Nat)
    (hexact : fRun tm2 n c = some d)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true) :
    run tm2 n (frame inside background (embed c)) =
      some (frame inside background (embed d)) := by
  have hheads := finiteHeads inside c n hcheck
  rw [run_frame tm2 inside background (embed c) n hheads]
  rw [← finite_run_source tm2 n c, hexact]
  rfl

/-- Translate a local finite trace to any absolute head coordinate. The
hypothesis only specifies cells in the finite region actually queried. -/
theorem bridgeAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c d : FConfig) (n : Nat)
    (hc : c.head = 0)
    (hexact : fRun tm2 n c = some d)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true)
    (hmatch : ∀ x, inside x = true →
      T (h+x) = decide (x ∈ c.marked)) :
    run tm2 n ⟨c.state,h,T⟩ = some (frameAt T h inside d) := by
  have hframe :
      frame inside (centerTape T h) (embed c) =
        ({state := c.state, head := 0, tape := centerTape T h} : Config) := by
    cases c with
    | mk s ch marks =>
      have hch : ch = 0 := hc
      subst ch
      apply config_ext
      · rfl
      · rfl
      · funext x
        have hcoord : h + (x-h) = x := by omega
        by_cases hx : inside x = true
        · simp [frame, embed, centerTape, hx, hmatch x hx, hcoord]
        · simp [frame, embed, centerTape, hx, hcoord]
  have hrun := finiteBridgeFrame inside (centerTape T h) c d n hexact hcheck
  rw [hframe] at hrun
  have hshift :
      shiftConfig h
        ({state := c.state, head := 0, tape := centerTape T h} : Config)
        = ⟨c.state,h,T⟩ := by
    apply config_ext
    · rfl
    · simp [shiftConfig]
    · funext x
      have hcoord : h + (x-h) = x := by omega
      simp [shiftConfig, centerTape, hcoord]
  rw [← hshift, shift_run, hrun]
  rfl

/-! The five fixed bridges in the Rst1' itinerary. Their finite traces are
exact computations of the published TM63 transition table. -/

def inside8 : Int → Bool := inWindow (-3) 0
def bridge8Start : FConfig := ⟨3,0,[-1]⟩
def bridge8End : FConfig := ⟨3,-2,[0,-2,-3]⟩

theorem bridge8_exact : fRun tm2 8 bridge8Start = some bridge8End := by decide

theorem bridge8_heads :
    (List.range 8).all (fun k =>
      match fRun tm2 k bridge8Start with
      | none => true
      | some f => inside8 f.head) = true := by decide

theorem bridge8_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside8 x = true →
      T (h+x) = decide (x ∈ bridge8Start.marked)) :
    run tm2 8 ⟨3,h,T⟩ = some (frameAt T h inside8 bridge8End) := by
  exact bridgeAt T h inside8 bridge8Start bridge8End 8 rfl
    bridge8_exact bridge8_heads hmatch

def inside20 : Int → Bool := inWindow (-5) 3
def bridge20Start : FConfig := ⟨3,0,[-3,-2,-1,2,3]⟩
def bridge20End : FConfig := ⟨3,4,[1,0,-1,-3,-4,-5]⟩

theorem bridge20_exact :
    fRun tm2 20 bridge20Start = some bridge20End := by decide

theorem bridge20_heads :
    (List.range 20).all (fun k =>
      match fRun tm2 k bridge20Start with
      | none => true
      | some f => inside20 f.head) = true := by decide

theorem bridge20_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside20 x = true →
      T (h+x) = decide (x ∈ bridge20Start.marked)) :
    run tm2 20 ⟨3,h,T⟩ = some (frameAt T h inside20 bridge20End) := by
  exact bridgeAt T h inside20 bridge20Start bridge20End 20 rfl
    bridge20_exact bridge20_heads hmatch

def inside9 : Int → Bool := inWindow (-2) 2
def bridge9Start : FConfig := ⟨3,0,[0,2]⟩
def bridge9End : FConfig := ⟨3,3,[0,-1,-2]⟩

theorem bridge9_exact : fRun tm2 9 bridge9Start = some bridge9End := by decide

theorem bridge9_heads :
    (List.range 9).all (fun k =>
      match fRun tm2 k bridge9Start with
      | none => true
      | some f => inside9 f.head) = true := by decide

theorem bridge9_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside9 x = true →
      T (h+x) = decide (x ∈ bridge9Start.marked)) :
    run tm2 9 ⟨3,h,T⟩ = some (frameAt T h inside9 bridge9End) := by
  exact bridgeAt T h inside9 bridge9Start bridge9End 9 rfl
    bridge9_exact bridge9_heads hmatch

def inside6 : Int → Bool := inWindow (-1) 3
def bridge6Start : FConfig := ⟨3,0,[2,3]⟩
def bridge6End : FConfig := ⟨3,4,[1,0,-1]⟩

theorem bridge6_exact : fRun tm2 6 bridge6Start = some bridge6End := by decide

theorem bridge6_heads :
    (List.range 6).all (fun k =>
      match fRun tm2 k bridge6Start with
      | none => true
      | some f => inside6 f.head) = true := by decide

theorem bridge6_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside6 x = true →
      T (h+x) = decide (x ∈ bridge6Start.marked)) :
    run tm2 6 ⟨3,h,T⟩ = some (frameAt T h inside6 bridge6End) := by
  exact bridgeAt T h inside6 bridge6Start bridge6End 6 rfl
    bridge6_exact bridge6_heads hmatch

def inside30 : Int → Bool := inWindow (-3) 5
def bridge30Start : FConfig := ⟨3,0,[-3,0]⟩
def bridge30End : FConfig := ⟨3,-4,[-2,-1,0,3,4,5]⟩

theorem bridge30_exact :
    fRun tm2 30 bridge30Start = some bridge30End := by decide

theorem bridge30_heads :
    (List.range 30).all (fun k =>
      match fRun tm2 k bridge30Start with
      | none => true
      | some f => inside30 f.head) = true := by decide

theorem bridge30_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside30 x = true →
      T (h+x) = decide (x ∈ bridge30Start.marked)) :
    run tm2 30 ⟨3,h,T⟩ = some (frameAt T h inside30 bridge30End) := by
  exact bridgeAt T h inside30 bridge30Start bridge30End 30 rfl
    bridge30_exact bridge30_heads hmatch

/-- Exact arithmetic for the proposed ten-phase Rst1' itinerary. -/
theorem rst1Prime_cost_decomposition (L a b : Nat) :
    3*(3*a+1) + 8 + 3*(3*L+5) + 20 + 3*(L+1) + 9 +
      3*(a+1) + 6 + 3*b + 30 =
        97 + 12*(L+a) + 3*b := by omega

#print axioms bridge8_at
#print axioms bridge20_at
#print axioms bridge9_at
#print axioms bridge6_at
#print axioms bridge30_at
#print axioms rst1Prime_cost_decomposition

/-! Exact output-cell identities for the counted right sweep. These
complement `counted_right_sweep`: the last scanned three-cell block is
`1,0,0` in increasing tape order, hence `d0` in head-facing order. -/

/-- A right sweep leaves every cell at or to the left of its starting head
unchanged. -/
theorem rst1Prime_sweptRight_preserves_left
    (n : Nat) (T : Int → Bool) (h x : Int) (hx : x ≤ h) :
    sweptRight n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      simp only [sweptRight]
      have hx' : x ≤ h+3 := by omega
      have hrec := ih (afterRight3 T h) (h+3) hx'
      rw [hrec]
      have h1 : x ≠ h+1 := by omega
      have h2 : x ≠ h+2 := by omega
      simp [afterRight3, h1, h2]

/-- A right sweep leaves every cell at or beyond its endpoint unchanged. -/
theorem rst1Prime_sweptRight_preserves_after
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h + 3*(n:Int) ≤ x) :
    sweptRight n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      simp only [sweptRight]
      have hx' : (h+3) + 3*(n:Int) ≤ x := by omega
      have hrec := ih (afterRight3 T h) (h+3) hx'
      rw [hrec]
      have h1 : x ≠ h+1 := by omega
      have h2 : x ≠ h+2 := by omega
      simp [afterRight3, h1, h2]

/-- Every scanned three-cell block is transformed to `1,0,0` in
increasing tape order. Later blocks do not alter earlier blocks. -/
theorem rst1Prime_sweptRight_block
    (n : Nat) (T : Int → Bool) (h : Int) (i : Nat) (hi : i<n) :
    sweptRight n T h (h+3*(i:Int)) = T (h+3*(i:Int)) ∧
    sweptRight n T h (h+3*(i:Int)+1) = false ∧
    sweptRight n T h (h+3*(i:Int)+2) = false := by
  induction n generalizing T h i with
  | zero => omega
  | succ n ih =>
      by_cases hi0 : i=0
      · subst i
        have h0 := rst1Prime_sweptRight_preserves_left n
          (afterRight3 T h) (h+3) h (by omega)
        have h1 := rst1Prime_sweptRight_preserves_left n
          (afterRight3 T h) (h+3) (h+1) (by omega)
        have h2 := rst1Prime_sweptRight_preserves_left n
          (afterRight3 T h) (h+3) (h+2) (by omega)
        have hn1 : h ≠ h+1 := by omega
        have hn2 : h ≠ h+2 := by omega
        simp only [sweptRight]
        constructor
        · simpa [afterRight3,hn1,hn2] using h0
        constructor
        · simpa [afterRight3] using h1
        · simpa [afterRight3] using h2
      · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have hj : j<n := by omega
        have hrec := ih (afterRight3 T h) (h+3) j hj
        simp only [sweptRight]
        have e0 : h+3*((j+1:Int)) = (h+3)+3*(j:Int) := by omega
        have e1 : h+3*((j+1:Int))+1 = (h+3)+3*(j:Int)+1 := by omega
        have e2 : h+3*((j+1:Int))+2 = (h+3)+3*(j:Int)+2 := by omega
        have hn0 : h+3+3*(j:Int) ≠ h+1 := by omega
        have hn1 : h+3+3*(j:Int) ≠ h+2 := by omega
        have hn2 : h+3+3*(j:Int)+1 ≠ h+1 := by omega
        have hn3 : h+3+3*(j:Int)+1 ≠ h+2 := by omega
        have hn4 : h+3+3*(j:Int)+2 ≠ h+1 := by omega
        have hn5 : h+3+3*(j:Int)+2 ≠ h+2 := by omega
        rcases hrec with ⟨r0,r1,r2⟩
        constructor
        · simpa [e0,afterRight3,hn0,hn1] using r0
        constructor
        · simpa [e1,afterRight3,hn2,hn3] using r1
        · simpa [e2,afterRight3,hn4,hn5] using r2

#print axioms rst1Prime_sweptRight_block


/-- The final three cells of a positive-length right sweep are the final
scanned block, so this is an immediate instance of the general block lemma. -/
theorem rst1Prime_sweptRight_lastBlock
    (n : Nat) (T : Int → Bool) (h : Int) :
    sweptRight (n+1) T h (h+3*(n:Int)) = T (h+3*(n:Int)) ∧
    sweptRight (n+1) T h (h+3*(n:Int)+1) = false ∧
    sweptRight (n+1) T h (h+3*(n:Int)+2) = false := by
  exact rst1Prime_sweptRight_block (n+1) T h n (by omega)


#print axioms rst1Prime_sweptRight_preserves_left
#print axioms rst1Prime_sweptRight_preserves_after
#print axioms rst1Prime_sweptRight_lastBlock


/-! Closed-form source-word identities for the proposed Rst1' target.
These are independent of the still-unproved source-run composition. -/

/-- An all-ones binary counter is exactly a repeated d0 word. -/
theorem rst1Prime_binDec_ones (n : Nat) :
    binDec n (2^n-1) = d0pow n := by
  induction n with
  | zero =>
      simpa [d0pow,d1pow] using (binDec_zero 0)
  | succ n ih =>
      have hposN : 0 < 2^n := Nat.pow_pos (by decide)
      have hn : 2^n-1 < 2^n := by omega
      have harg : 2^(n+1)-1 = 2*(2^n-1)+1 := by
        rw [Nat.pow_succ]
        omega
      rw [harg,binDec_odd n (2^n-1) hn]
      simp [d0pow,ih]

/-- The new high counter in the Rst1' target has the exact digit word
d0^a, d1, d0^(L+1). -/
theorem rst1Prime_binDec_reset (L a : Nat) :
    binDec (L+a+2) (2^(L+a+2)-2^a-1) =
      d0pow a ++ d1 ++ d0pow (L+1) := by
  induction a with
  | zero =>
      have hlen : L+0+2 = (L+1)+1 := by omega
      have hpow : 2^(L+2) = 2*2^(L+1) := by
        rw [show L+2 = (L+1)+1 by omega,Nat.pow_succ]
        omega
      have hposL : 0 < 2^(L+1) := Nat.pow_pos (by decide)
      have harg : 2^(L+2)-2^0-1 = 2*(2^(L+1)-1) := by
        rw [hpow]
        simp only [Nat.pow_zero]
        omega
      have hbound : 2^(L+1)-1 < 2^(L+1) := by omega
      rw [show L+0+2 = L+2 by omega,harg]
      rw [binDec_even (L+1) (2^(L+1)-1) hbound]
      simp [rst1Prime_binDec_ones,d0pow]
  | succ a ih =>
      let R : Nat := 2^(L+a+2)-2^a-1
      have hExp : a+1 ≤ L+a+2 := by omega
      have hpow : 2^(a+1) ≤ 2^(L+a+2) :=
        Nat.pow_le_pow_right (show 0<2 by decide) hExp
      have hdouble : 2^(a+1) = 2*2^a := by
        rw [Nat.pow_succ]
        omega
      have hpos : 0 < 2^a := Nat.pow_pos (by decide)
      have hdouble_le : 2*2^a ≤ 2^(L+a+2) := by
        rw [← hdouble]
        exact hpow
      have hlarge : 2^a+1 ≤ 2^(L+a+2) := by
        omega
      have hbound : R < 2^(L+a+2) := by
        dsimp [R]
        omega
      have hlen : L+(a+1)+2 = (L+a+2)+1 := by omega
      have hpowN : 2^(L+(a+1)+2) = 2*2^(L+a+2) := by
        rw [hlen,Nat.pow_succ]
        omega
      have harg :
          2^(L+(a+1)+2)-2^(a+1)-1 = 2*R+1 := by
        dsimp [R]
        rw [hpowN,hdouble]
        omega
      rw [harg,hlen,binDec_odd (L+a+2) R hbound]
      rw [ih]
      simp [d0pow]

/-- The proposed target's complete head-facing word, reduced to the
three nested d0 blocks and the single d1 boundary. -/
theorem rst1Prime_target_leftFacing (L a b : Nat) :
    s1LeftFacing (L+a+2) (2^(L+a+2)-2^a-1) 2 b (2^b-1) =
      d0pow b ++ markerWord 2 ++ d0 ++ d0pow a ++ d1 ++
        d0pow (L+1) ++ lh := by
  simp [s1LeftFacing,rst1Prime_binDec_ones,rst1Prime_binDec_reset,
    List.append_assoc]

/-- The proposed target's right-facing word is the fixed S0 separator
followed by one three-one block. -/
theorem rst1Prime_target_rightFacing :
    s0RightFacing 0 = [false,true,true,true,false,false] ++ d1pow 1 := by
  rfl

#print axioms rst1Prime_binDec_ones
#print axioms rst1Prime_binDec_reset
#print axioms rst1Prime_target_leftFacing
#print axioms rst1Prime_target_rightFacing




/-- Within a repeated d0 word, precisely every third cell is true,
with the true cell at offset two in each block. -/
theorem rst1Prime_sideBit_d0pow_pattern
    (n i : Nat) (hi : i < 3*n) :
    sideBit (d0pow n) i = decide (i%3=2) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hsmall : i<3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with rfl | rfl | rfl <;> simp [d0pow,d0,sideBit]
      · have hlarge : 3≤i := by omega
        have htail : i-3 < 3*n := by omega
        rw [d0pow]
        rw [sideBit_append_right d0 (d0pow n) i (by simp [d0]; omega)]
        have hmod : (i-3)%3 = i%3 := by omega
        simpa [hmod] using ih (i-3) htail

/-- The first n blocks of a right sweep, read from their right edge
towards the left, form exactly d0pow n. The final scanned block is
deliberately excluded; it is supplied by the following bridge. -/
theorem rst1Prime_sweptRight_headFacing_d0pow
    (n : Nat) (T : Int → Bool) (h : Int)
    (hpre : rightOnes T h (n+1)) (k : Nat)
    (hk : k < 3*n) :
    sweptRight (n+1) T h
      (h+3*(n:Int)-1-(k:Int)) =
      sideBit (d0pow n) k := by
  let q : Nat := k/3
  let r : Nat := k%3
  let j : Nat := n-1-q
  have hdecomp : k = 3*q+r := by
    dsimp [q,r]
    omega
  have hr : r<3 := by
    dsimp [r]
    exact Nat.mod_lt _ (by decide)
  have hq : q<n := by
    dsimp [q]
    omega
  have hj : j<n+1 := by
    dsimp [j]
    omega
  have hcoord :
      h+3*(n:Int)-1-(k:Int) =
        h+3*(j:Int)+2-(r:Int) := by
    dsimp [q,r,j]
    omega
  have hblock := rst1Prime_sweptRight_block (n+1) T h j hj
  have hT : T (h+3*(j:Int)) = true := (hpre j hj).1
  have hside : sideBit (d0pow n) k = decide (r=2) := by
    simpa [r] using rst1Prime_sideBit_d0pow_pattern n k hk
  have hrcases : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hrcases with hr0 | hr1 | hr2
  · rw [hcoord,hr0]
    simpa [hside,hr0] using hblock.2.2
  · rw [hcoord,hr1]
    have hcoord1 : h+3*(j:Int)+2-1 = h+3*(j:Int)+1 := by omega
    rw [hcoord1]
    simpa [hside,hr1] using hblock.2.1
  · rw [hcoord,hr2]
    simpa [hside,hr2,hT] using hblock.1

/-- Repeated d0 blocks can be appended on either side without changing
the word; this form is convenient when the final block comes from a
bridge boundary. -/
theorem rst1Prime_d0pow_append_right (n : Nat) :
    d0pow n ++ d0 = d0pow (n+1) := by
  induction n with
  | zero => simp [d0pow]
  | succ n ih =>
      simp [d0pow,List.append_assoc,ih]

#print axioms rst1Prime_sideBit_d0pow_pattern
#print axioms rst1Prime_sweptRight_headFacing_d0pow
#print axioms rst1Prime_d0pow_append_right


/-- Length of a repeated d0 word. -/
theorem rst1Prime_d0pow_length (n : Nat) :
    (d0pow n).length = 3*n := by
  induction n with
  | zero => simp [d0pow]
  | succ n ih => simp [d0pow,d0,ih]

/-- Glue n scanned d0 blocks to a final bridge-supplied d0 block. The
resulting head-facing word is d0pow (n+1). -/
theorem rst1Prime_d0pow_segment
    (n : Nat) (T : Int → Bool) (h head : Int)
    (F : Int → Bool)
    (hpre : rightOnes T h (n+1))
    (hhead : head = h+3*(n:Int)-1)
    (hprefix : ∀ k, k<3*n →
      F (head-(k:Int)) =
        sweptRight (n+1) T h (head-(k:Int)))
    (hboundary : ∀ r, r<3 →
      F (head-((3*n+r:Int))) = sideBit d0 r) :
    ∀ k, k<3*(n+1) →
      F (head-(k:Int)) = sideBit (d0pow (n+1)) k := by
  intro k hk
  by_cases hsmall : k<3*n
  · have hsweep := rst1Prime_sweptRight_headFacing_d0pow n T h hpre k hsmall
    have hword : sideBit (d0pow (n+1)) k = sideBit (d0pow n) k := by
      rw [← rst1Prime_d0pow_append_right n]
      exact sideBit_append_left (d0pow n) d0 k (by
        rw [rst1Prime_d0pow_length]
        exact hsmall)
    calc
      F (head-(k:Int)) =
          sweptRight (n+1) T h (head-(k:Int)) := hprefix k hsmall
      _ = sideBit (d0pow n) k := hsweep
      _ = sideBit (d0pow (n+1)) k := hword.symm
  · have hlarge : 3*n≤k := by omega
    have hrem : k-3*n<3 := by omega
    have hkdecomp : k=3*n+(k-3*n) := by omega
    have hbound : (d0pow n).length ≤ k := by
      rw [rst1Prime_d0pow_length]
      exact hlarge
    have hword : sideBit (d0pow (n+1)) k =
        sideBit d0 (k-3*n) := by
      rw [← rst1Prime_d0pow_append_right n]
      exact sideBit_append_right (d0pow n) d0 k hbound
    have hbd := hboundary (k-3*n) hrem
    have hcoord : head-(k:Int) =
        head-((3*n+(k-3*n):Nat):Int) := by rw [hkdecomp]
    rw [hcoord,hbd]
    exact hword.symm

#print axioms rst1Prime_d0pow_length
#print axioms rst1Prime_d0pow_segment


end BB6Coverage.Agent8Rst1Prime
