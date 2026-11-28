import DiagonalCoordinates
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Canonical small-second anchor decomposition for the exact F321 source map.

The Equal, Middle-even and Middle-odd branches are precisely the live branches
whose output second counter is at most two. Between consecutive such anchors
only High/Far moves occur. This is the exact forward counterpart of the H/F
inverse-word machinery: every positive-time root run is a chain of completed
anchor epochs plus one trailing High/Far suffix.
-/

namespace BB6.Agent2F321AnchorEpoch
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal

def HFMove (a d A D : Nat) : Prop :=
  (d+2 ≤ a ∧ A=a-d-2 ∧ D=2*d+3) ∨
  (a<d ∧ 3*a+1≤d ∧ A=4*a+6 ∧ D=d-3*a)

inductive HFRun : Nat → Nat → Nat → Nat → Nat → Prop
  | nil (a d) : HFRun 0 a d a d
  | step {n a d A D B C} :
      HFRun n a d A D → HFMove A D B C →
      HFRun (n+1) a d B C

def AnchorMove (a d R c : Nat) : Prop :=
  (a=d ∧ R=2*a+4 ∧ c=1) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=0 ∧ R=4*a+6 ∧ c=2) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=1 ∧ R=4*a+6 ∧ c=1)

def AnchorEpoch (R c R' c' : Nat) : Prop :=
  ∃ n a d, HFRun n R c a d ∧ AnchorMove a d R' c'

theorem hfMove_source {a d A D : Nat}
    (h : HFMove a d A D) : CounterMove a d A D := by
  unfold HFMove at h
  rcases h with h | h
  · rcases h with ⟨hg,rfl,rfl⟩
    exact CounterMove.high d hg
  · rcases h with ⟨h1,h2,rfl,rfl⟩
    exact CounterMove.far d h1 h2

theorem anchorMove_source {a d R c : Nat}
    (h : AnchorMove a d R c) : CounterMove a d R c := by
  unfold AnchorMove at h
  rcases h with hE | hM
  · rcases hE with ⟨rfl,rfl,rfl⟩
    exact CounterMove.equal a
  · rcases hM with h2 | h1
    · rcases h2 with ⟨hlo,hhi,hp,rfl,rfl⟩
      exact CounterMove.middleEven d hlo hhi hp
    · rcases h1 with ⟨hlo,hhi,hp,rfl,rfl⟩
      exact CounterMove.middleOdd d hlo hhi hp

theorem move_hf_or_anchor {a d A D : Nat}
    (h : CounterMove a d A D) :
    HFMove a d A D ∨ AnchorMove a d A D := by
  cases h with
  | high a d hg =>
      left
      unfold HFMove
      exact Or.inl ⟨hg,rfl,rfl⟩
  | equal a =>
      right
      unfold AnchorMove
      exact Or.inl ⟨rfl,rfl,rfl⟩
  | far a d h1 h2 =>
      left
      unfold HFMove
      exact Or.inr ⟨h1,h2,rfl,rfl⟩
  | middleEven a d h1 h2 hp =>
      right
      unfold AnchorMove
      exact Or.inr (Or.inl ⟨h1,h2,hp,rfl,rfl⟩)
  | middleOdd a d h1 h2 hp =>
      right
      unfold AnchorMove
      exact Or.inr (Or.inr ⟨h1,h2,hp,rfl,rfl⟩)

theorem hfMove_X_bounds {a d A D : Nat}
    (h : HFMove a d A D) :
    X a d + 1 ≤ X A D ∧ X A D ≤ X a d + 6 := by
  unfold HFMove at h
  rcases h with h | h
  · rcases h with ⟨hg,rfl,rfl⟩
    have hx := (high_coordinates a d hg).1
    omega
  · rcases h with ⟨h1,h2,rfl,rfl⟩
    have hx := (far_coordinates a d h1 h2).1
    omega

theorem hfRun_first_step
    {n a d A D : Nat}
    (h : HFRun (n+1) a d A D) :
    ∃ B C, HFMove a d B C ∧ HFRun n B C A D := by
  induction n generalizing A D with
  | zero =>
      cases h with
      | step hp hm =>
          cases hp
          exact ⟨_,_,hm,HFRun.nil _ _⟩
  | succ n ih =>
      cases h with
      | @step _ _ _ X Y A D hp hm =>
          rcases ih hp with ⟨B,C,hfirst,htail⟩
          exact ⟨B,C,hfirst,HFRun.step htail hm⟩

theorem anchor_hfMove_is_high
    {R c A D : Nat}
    (hR : 6 ≤ R) (hc : c=1 ∨ c=2)
    (h : HFMove R c A D) :
    A = R-c-2 ∧ D = 2*c+3 := by
  unfold HFMove at h
  rcases h with hH | hF
  · exact ⟨hH.2.1,hH.2.2⟩
  · rcases hF with ⟨hlo,hhi,rfl,rfl⟩
    rcases hc with rfl | rfl <;> omega

theorem hfRun_X_bounds {n a d A D : Nat}
    (h : HFRun n a d A D) :
    X a d + n ≤ X A D ∧ X A D ≤ X a d + 6*n := by
  induction h with
  | nil => omega
  | step h hm ih =>
      have hs := hfMove_X_bounds hm
      omega

theorem anchorMove_bounds {a d R c : Nat}
    (h : AnchorMove a d R c) :
    (c=1 ∨ c=2) ∧ X a d ≤ R+1 ∧ R+c+5 ≥ X a d+5 := by
  unfold AnchorMove at h
  rcases h with hE | hM
  · rcases hE with ⟨rfl,rfl,rfl⟩
    unfold X
    omega
  · rcases hM with h2 | h1
    · rcases h2 with ⟨hlo,hhi,hp,rfl,rfl⟩
      unfold X
      omega
    · rcases h1 with ⟨hlo,hhi,hp,rfl,rfl⟩
      unfold X
      omega

theorem anchorEpoch_witness_growth
    {n R c a d R' c' : Nat}
    (hhf : HFRun n R c a d)
    (ha : AnchorMove a d R' c') :
    R + c + 4 + n ≤ R' := by
  have hx := (hfRun_X_bounds hhf).1
  have hb := (anchorMove_bounds ha).2.1
  unfold X at hx
  omega

theorem anchorEpoch_gain5 {R c R' c' : Nat}
    (h : AnchorEpoch R c R' c') (hc : 1 ≤ c) :
    R + 5 ≤ R' := by
  rcases h with ⟨n,a,d,hhf,ha⟩
  have hg := anchorEpoch_witness_growth hhf ha
  omega

/-- Pull any exact formal inverse path backward across a known H/F forward
    suffix.  Unlike the generic bounded inverse theorem, no large-second
    hypothesis is needed because the branch language is already known exactly. -/
theorem hfRun_pullback_formal
    {n a d A D : Nat} {seed : Int} {w : List InverseLetter}
    (h : HFRun n a d A D)
    (hp : FormalInversePath seed w (A:Int) (D:Int)) :
    ∃ w' : List InverseLetter,
      FormalInversePath seed w' (a:Int) (d:Int) ∧
      w'.length = w.length + n := by
  induction h generalizing w with
  | nil a d =>
      exact ⟨w,hp,by omega⟩
  | @step n a d A D B C h hm ih =>
      unfold HFMove at hm
      rcases hm with hH | hF
      · rcases hH with ⟨hg,rfl,rfl⟩
        have ha : 2*(A:Int) =
            2*(((A-D-2 : Nat):Int)) + ((2*D+3 : Nat):Int) + 1 := by omega
        have hd : 2*(D:Int) = ((2*D+3 : Nat):Int) - 3 := by omega
        have hp' : FormalInversePath seed (.high::w) (A:Int) (D:Int) :=
          FormalInversePath.stepH hp ha hd
        obtain ⟨w',hw',hlen⟩ := ih hp'
        refine ⟨w',hw',?_⟩
        simp at hlen ⊢
        omega
      · rcases hF with ⟨h1,h2,rfl,rfl⟩
        have ha : 4*(A:Int) = ((4*A+6 : Nat):Int) - 6 := by omega
        have hd : (D:Int) = (((D-3*A : Nat):Int)) + 3*(A:Int) := by omega
        have hp' : FormalInversePath seed (.far::w) (A:Int) (D:Int) :=
          FormalInversePath.stepF hp ha hd
        obtain ⟨w',hw',hlen⟩ := ih hp'
        refine ⟨w',hw',?_⟩
        simp at hlen ⊢
        omega

/-- A pure H/F suffix ending at a halting gate therefore carries an exact
    terminal-seeded formal inverse word all the way back to its anchor. -/
theorem hfRun_terminal_formal
    {m R c D : Nat}
    (h : HFRun m R c (D+1) D) :
    ∃ w : List InverseLetter,
      w.length = m ∧
      FormalInversePath (D:Int) w (R:Int) (c:Int) := by
  have hp0 : FormalInversePath (D:Int) [] ((D+1:Int)) (D:Int) :=
    FormalInversePath.nil
  obtain ⟨w,hw,hlen⟩ := hfRun_pullback_formal h hp0
  refine ⟨w,?_,hw⟩
  simpa using hlen

theorem hfRun_counterReach {n a d A D : Nat}
    (h : HFRun n a d A D) : CounterReach a d n A D := by
  induction h with
  | nil => exact CounterReach.nil
  | step h hm ih =>
      exact CounterReach.step ih (hfMove_source hm)

inductive AnchorChain : Nat → Nat → Nat → Nat → Nat → Prop
  | nil (R c) : AnchorChain 0 R c R c
  | step {q R c A e B f} :
      AnchorChain q R c A e → AnchorEpoch A e B f →
      AnchorChain (q+1) R c B f

def AnchorDecomposition (R c A D : Nat) : Prop :=
  ∃ q R0 c0 m,
    AnchorChain q R c R0 c0 ∧ HFRun m R0 c0 A D

theorem counterReach_anchor_decomposition
    {R c n A D : Nat}
    (h : CounterReach R c n A D) :
    AnchorDecomposition R c A D := by
  induction h with
  | nil =>
      exact ⟨0,R,c,0,AnchorChain.nil R c,HFRun.nil R c⟩
  | @step n a d A D h hm ih =>
      rcases ih with ⟨q,R0,c0,m,hchain,hhf⟩
      rcases move_hf_or_anchor hm with hnext | hanchor
      · exact ⟨q,R0,c0,m+1,hchain,HFRun.step hhf hnext⟩
      · refine ⟨q+1,A,D,0,?_,HFRun.nil A D⟩
        exact AnchorChain.step hchain ⟨m,a,d,hhf,hanchor⟩

theorem seed_only_equal {A D : Nat}
    (h : CounterMove 1 1 A D) : A=6 ∧ D=1 := by
  cases h <;> omega

theorem root_tail_from_six_one {n A D : Nat}
    (h : CounterReach 1 1 (n+1) A D) :
    CounterReach 6 1 n A D := by
  induction n generalizing A D with
  | zero =>
      cases h with
      | step hr hm =>
          cases hr
          rcases seed_only_equal hm with ⟨rfl,rfl⟩
          exact CounterReach.nil
  | succ n ih =>
      cases h with
      | step hr hm =>
          exact CounterReach.step (ih hr) hm

theorem root_anchor_decomposition {n A D : Nat}
    (h : CounterReach 1 1 (n+1) A D) :
    AnchorDecomposition 6 1 A D :=
  counterReach_anchor_decomposition (root_tail_from_six_one h)

theorem anchorChain_end_positive {q R c A e : Nat}
    (h : AnchorChain q R c A e) (hc : 1 ≤ c) : 1 ≤ e := by
  induction h with
  | nil => exact hc
  | step h he ih =>
      rcases he with ⟨n,a,d,hhf,ha⟩
      have hc' := (anchorMove_bounds ha).1
      omega

theorem anchorChain_linear_growth {q R c A e : Nat}
    (h : AnchorChain q R c A e) (hc : 1 ≤ c) :
    R + 5*q ≤ A := by
  induction h with
  | nil => omega
  | @step q R c A e B f h he ih =>
      have hi := ih hc
      have hepos := anchorChain_end_positive h hc
      have hg := anchorEpoch_gain5 he hepos
      omega

theorem terminal_has_last_anchor_HF
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c m,
      AnchorChain q 6 1 R c ∧
      HFRun m R c (D+1) D ∧
      (c=1 ∨ c=2) := by
  rcases root_anchor_decomposition h with ⟨q,R,c,m,hchain,hhf⟩
  refine ⟨q,R,c,m,hchain,hhf,?_⟩
  have hc := anchorChain_end_positive hchain (by decide)
  by_cases hq : q=0
  · subst q
    cases hchain
    exact Or.inl rfl
  · cases hchain with
    | step h0 he =>
        rcases he with ⟨j,a,d,hj,ha⟩
        exact (anchorMove_bounds ha).1

/-- Pure arithmetic identity for every compiled H/F inverse word.  High adds
    (sumDecrease,shift,length)=(1,1,1); Far adds (6,2,1). -/
theorem compile_cost_identity (w : List InverseLetter) :
    (compile w).sumDecrease + 4*w.length =
      5*(compile w).shift := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [compile, advance] at ih ⊢ <;> omega

/-- Any genuine terminal H/F suffix from a root anchor has positive length and
    begins with a High branch. -/
theorem terminal_last_anchor_first_high
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c j B C,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      HFMove R c B C ∧
      B = R-c-2 ∧ C = 2*c+3 ∧
      HFRun j B C (D+1) D := by
  rcases terminal_has_last_anchor_HF h with
    ⟨q,R,c,m,hchain,hhf,hc⟩
  have hR0 := anchorChain_linear_growth hchain (by decide)
  have hR : 6 ≤ R := by omega
  have hm : 0 < m := by
    by_contra hz
    have hm0 : m=0 := by omega
    subst m
    cases hhf
    rcases hc with rfl | rfl <;> omega
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rcases hfRun_first_step hhf with ⟨B,C,hfirst,htail⟩
  have hh := anchor_hfMove_is_high hR hc hfirst
  exact ⟨q,R,c,j,B,C,hchain,hc,hfirst,hh.1,hh.2,htail⟩

/-- Strengthening of the last-anchor formal normal form: the exact word can be
    chosen with a leading High letter. -/
theorem terminal_has_last_anchor_formal_word_head_high
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c j w,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      w.length = j ∧
      FormalInversePath (D:Int) (.high::w) (R:Int) (c:Int) := by
  rcases terminal_last_anchor_first_high h with
    ⟨q,R,c,j,B,C,hchain,hc,hfirst,hB,hC,htail⟩
  rcases hfRun_terminal_formal htail with ⟨w,hlen,hw⟩
  subst B
  subst C
  have ha : 2*(R:Int) =
      2*(((R-c-2 : Nat):Int)) + ((2*c+3 : Nat):Int) + 1 := by
    rcases hc with rfl | rfl <;> omega
  have hd : 2*(c:Int) = ((2*c+3 : Nat):Int) - 3 := by omega
  have hfull : FormalInversePath (D:Int) (.high::w) (R:Int) (c:Int) :=
    FormalInversePath.stepH hw ha hd
  exact ⟨q,R,c,j,w,hchain,hc,hlen,hfull⟩

/-- Exact last-anchor inverse-word normal form for any authentic positive-time
    halt.  The word ends at a genuine root-reachable anchor with second counter
    one or two, with no asymptotic or bounded-depth cutoff. -/
theorem terminal_has_last_anchor_formal_word
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c m w,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      w.length = m ∧
      FormalInversePath (D:Int) w (R:Int) (c:Int) := by
  rcases terminal_has_last_anchor_HF h with
    ⟨q,R,c,m,hchain,hhf,hc⟩
  rcases hfRun_terminal_formal hhf with ⟨w,hlen,hw⟩
  exact ⟨q,R,c,m,w,hchain,hc,hlen,hw⟩

/-- The formal word yields the exact odd-numerator dyadic equation at the
    authentic last anchor. -/
theorem terminal_last_anchor_compiled_equation
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c m w,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      w.length = m ∧
      (2:Int)^(compile w).shift * (R:Int) =
        ((compile w).u:Int)*(D:Int) + (compile w).v ∧
      (compile w).u % 2 = 1 := by
  rcases terminal_has_last_anchor_formal_word h with
    ⟨q,R,c,m,w,hchain,hc,hlen,hw⟩
  have hcert := formal_inverse_congruence hw
  exact ⟨q,R,c,m,w,hchain,hc,hlen,hcert.1,hcert.2⟩

/-- Exact Diophantine last-anchor law for any authentic halt.  Here m is
    the H/F suffix length and shift is the dyadic denominator exponent of its
    exact inverse word. -/
theorem terminal_last_anchor_cost_equation
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c m w,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      w.length = m ∧
      FormalInversePath (D:Int) w (R:Int) (c:Int) ∧
      R + c + 5*(compile w).shift =
        2*D + 1 + 4*m := by
  rcases terminal_has_last_anchor_formal_word h with
    ⟨q,R,c,m,w,hchain,hc,hlen,hw⟩
  have hs := (formal_inverse_path_certificate hw).2
  unfold sumAt at hs
  have hcost := compile_cost_identity w
  have hcostZ := congrArg (fun z : Nat => (z:Int)) hcost
  norm_num at hcostZ
  refine ⟨q,R,c,m,w,hchain,hc,hlen,hw,?_⟩
  omega

#print axioms compile_cost_identity
#print axioms terminal_last_anchor_cost_equation

#print axioms terminal_last_anchor_first_high
#print axioms terminal_has_last_anchor_formal_word_head_high
#print axioms terminal_has_last_anchor_formal_word
#print axioms terminal_last_anchor_compiled_equation

#print axioms move_hf_or_anchor
#print axioms anchorEpoch_witness_growth
#print axioms root_anchor_decomposition
#print axioms anchorChain_linear_growth
#print axioms terminal_has_last_anchor_HF
end BB6.Agent2F321AnchorEpoch
