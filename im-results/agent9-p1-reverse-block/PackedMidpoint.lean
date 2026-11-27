import HalfBlockMargin
import PackedRecover
import ReverseBlockJump

namespace BB6.Agent9PackedMidpoint
open BB6.Agent45.DelayedCarry
open BB6.Agent45ReverseBlock
open BB6.Agent9ReverseBlock (JumpCover walk_mem_prefix_live)
open BB6.Agent43PackedRecover (recoverFast recoverFast_exact)
open BB6.Agent43P1Complement (HalfCovered HalfCert MidpointCover AllBlockMargins half_midpoint_next)

/-- Delayed bits in a suffix of the original n-bit window can be read
    from the initial low word even after appending h selected bits. -/
theorem targetWord_fixed (n s h B R k : Nat) (hk : h+k≤n) :
    targetWord n (s+h) (B+2^s*R) k = targetWord n (s+h) B k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [targetWord]
    rw [ih (by omega),target_prefix n s (s+h+k) B R (by omega)]

/-- Only the n-h terminal portion of a fixed n-step window is rewound
    from all endpoints. A supplied list may over-approximate its image. -/
def MidpointLive (n s h : Nat) (ps : List Prefix) (mids : Nat → List Nat) : Prop :=
  ∀ B a, (B,a)∈ps → ∀ z c,
    Walk (n+(s+h)+3+(n-h)) z (targetWord n (s+h) B (n-h)) c →
    c∈mids B

/-- The modular first jump and fitted reverse blocks prove the suffix
    live cover. The final containment premise permits packed supersets
    of the mathematical blockFold output. -/
theorem midpointLive_of_jump (n s h : Nat) (ps : List Prefix)
    (parts : Nat → List (List Nat)) (tails ends mids : Nat → List Nat)
    (hflat : ∀ B a, (B,a)∈ps →
      (parts B).flatten ++ tails B = targetWord n (s+h) B (n-h))
    (hfit : ∀ B a, (B,a)∈ps → Fitted (n+(s+h)+3) (parts B))
    (hjump : ∀ B a, (B,a)∈ps →
      JumpCover (n+(s+h)+3+(n-h)) (tails B) (ends B))
    (hcontains : ∀ B a, (B,a)∈ps → ∀ c,
      c∈blockFold (n+(s+h)+3) (parts B) (ends B) → c∈mids B) :
    MidpointLive n s h ps mids := by
  intro B a hp z c hw
  have hf := hflat B a hp
  have hl : (parts B).flatten.length+(tails B).length=n-h := by
    have he := congrArg List.length hf
    simpa using he
  have hb : ∀ y∈(parts B).flatten ++ tails B, y≤1 := by
    rw [hf]
    exact targetWord_bits n (s+h) B (n-h)
  have hw' : Walk (n+(s+h)+3+(n-h)) z ((parts B).flatten ++ tails B) c := by
    rw [hf]
    exact hw
  exact hcontains B a hp c (walk_mem_prefix_live _ _ _ _ _ _ _ (by omega)
    hb (hfit B a hp) (hjump B a hp) hw')

/-- The actual packed algorithm recovers only candidate midpoint words.
    No exponential enumeration of all h-bit extensions is required. -/
def recoverMidpoints (n s h : Nat) (ps : List Prefix) (mids : Nat → List Nat) : List Prefix :=
  ps.flatMap fun p => (mids p.1).filterMap fun c =>
    let R := recoverFast n p.1 s h c
    if R.2=p.2 ∧ R.1%4=1 then some (R.1,c) else none

/-- Restrict the midpoint obligation to actual source traces. A sound
    over-approximate certificate need not prove all listed prefixes legal. -/
def TraceMidpointCover (n s h : Nat) (ps qs : List Prefix) : Prop :=
  ∀ B a C c, (B,a)∈ps → Trace n s B a → C%4=1 →
    Extend n s B a h C c →
    (∃ D d, Extend n (s+h) C c (n-h) D d) → (C,c)∈qs

/-- Every authentic extending midpoint occurs in the recovered list. -/
theorem traceMidpointCover_of_live (n s h : Nat) (ps : List Prefix)
    (mids : Nat → List Nat) (hhn : h≤n)
    (hLive : MidpointLive n s h ps mids) :
    TraceMidpointCover n s h ps (recoverMidpoints n s h ps mids) := by
  intro B a C c hp ht hcanon he htail
  obtain ⟨D,d,hsuf⟩ := htail
  have ht' := extend_trace n s B a h C c ht he
  obtain ⟨R,hR⟩ := extend_mod n s B a h C c he
  have hsame : targetWord n (s+h) C (n-h)=targetWord n (s+h) B (n-h) := by
    rw [hR]
    exact targetWord_fixed n s h B R (n-h) (by omega)
  have hw := extend_to_walk n (s+h) C c (n-h) D d ht' (by omega) hsuf
  rw [hsame] at hw
  have hc := hLive B a hp d c hw
  have hr := recoverFast_exact n s B a h C c ht he hhn
  unfold recoverMidpoints
  apply List.mem_flatMap.mpr
  refine ⟨(B,a),hp,?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨c,hc,?_⟩
  simp [hr,hcanon]

/-- The existing half-certificate induction also accepts the weaker
    trace-restricted midpoint property. The classical filter is only a
    proof device; no filtering is evaluated by the checker. -/
theorem half_midpoint_next_trace (n K s h : Nat) (ps qs : List Prefix)
    (hn : 1≤n) (heven : n%2=0) (hs : 1≤s) (hh : 1≤h) (hhn : h≤n)
    (hc : HalfCert n K s ps) (hm : TraceMidpointCover n s h ps qs)
    (hg : AllBlockMargins n K s h qs) : HalfCert n K (s+h) qs := by
  classical
  let ps' : List Prefix := ps.filter (fun p => decide (Trace n s p.1 p.2))
  have hc' : HalfCert n K s ps' := by
    refine ⟨?_,hc.margins⟩
    intro B a C c htr hmod he
    have hp := hc.cover B a C c htr hmod he
    simp [ps',hp,htr]
  have hm' : MidpointCover n s h ps' qs := by
    intro B a C c hp hcanon he htail
    change (B,a) ∈ ps.filter (fun p => decide (Trace n s p.1 p.2)) at hp
    obtain ⟨hp',ht⟩ := List.mem_filter.mp hp
    exact hm B a C c hp' (by simpa using ht) hcanon he htail
  exact half_midpoint_next n K s h ps' qs hn heven hs hh hhn hc' hm' hg

/-- Complete source induction for the two-stage packed midpoint algorithm.
    The proposed list can be larger than the exact recovered list. -/
theorem half_cert_from_midpoints (n K s h : Nat) (ps qs : List Prefix)
    (mids : Nat → List Nat)
    (hn : 1≤n) (heven : n%2=0) (hs : 1≤s) (hh : 1≤h) (hhn : h≤n)
    (hc : HalfCert n K s ps) (hLive : MidpointLive n s h ps mids)
    (hcontains : ∀ p∈recoverMidpoints n s h ps mids, p∈qs)
    (hg : AllBlockMargins n K s h qs) : HalfCert n K (s+h) qs := by
  apply half_midpoint_next_trace n K s h ps qs hn heven hs hh hhn hc _ hg
  intro B a C c hp ht hcanon he htail
  exact hcontains (C,c) (traceMidpointCover_of_live n s h ps mids hhn hLive
    B a C c hp ht hcanon he htail)

/-- Initialize the actual cost-one packed search without evaluating a
    huge closed exponent in a Boolean decision procedure. -/
theorem packed_half_first_prop (n K : Nat)
    (hgood : (n+K+2)*marginSize n K*2 < 6*2^n) :
    HalfCert n K 1 [(1,(n+2)/2)] := by
  refine ⟨?_,?_⟩
  · intro B a C c ht _ he
    exact covered_first n B a C c ht he
  · intro j hj hjs B a ht
    have hj' : j=1 := by omega
    subst j
    have ho := (trace_bounds n (n+1) B a ht).2.2.1
    have hm : (7*B)%2=1 := by omega
    simpa [resMin,hm] using hgood

/-- The true cost-one seed for the resumed n45 scan at K=450,000,000. -/
theorem packed_half_first_n45 :
    HalfCert 45352466 450000000 1 [(1,(45352466+2)/2)] := by
  apply packed_half_first_prop
  have hp : (2:Nat)^64 ≤ 2^45352466 := Nat.pow_le_pow_right (by decide) (by decide)
  have hsmall : (45352466+450000000+2)*marginSize 45352466 450000000*2 < 6*2^64 := by decide
  exact Nat.lt_of_lt_of_le hsmall (Nat.mul_le_mul_left 6 hp)

#print axioms targetWord_fixed
#print axioms midpointLive_of_jump
#print axioms traceMidpointCover_of_live
#print axioms half_midpoint_next_trace
#print axioms half_cert_from_midpoints
#print axioms packed_half_first_prop
#print axioms packed_half_first_n45

end BB6.Agent9PackedMidpoint
