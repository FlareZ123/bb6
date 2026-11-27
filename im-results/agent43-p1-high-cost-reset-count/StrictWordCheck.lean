import StrictWord64
namespace BB6.Agent43StrictWord
open BB6.Agent9BatchCarry (Interior Walk)
open BB6.Agent9FoldedProbe
open BB6.Agent43BirthLocate

/-- A packed chunk may have 0 to 64 bits. Arithmetic is on Nat, so the
    product of a 64-bit word and the clock has no machine-word overflow. -/
def stepChunk (q a k B : Nat) : Option Nat :=
  if 1≤a ∧ a+3≤q ∧ k≤64 ∧ B<2^k then
    let x := a+q*B+dw64 B
    if x%2^k=0 then some (x/2^k) else none
  else none

theorem stepChunk_sound {q a k B z : Nat} (h : stepChunk q a k B=some z) :
    Walk q a k z := by
  unfold stepChunk at h
  split at h
  next hc =>
    dsimp only at h
    split at h
    next he =>
      simp only [Option.some.injEq] at h
      have hd := Nat.div_add_mod (a+q*B+dw64 B) (2^k)
      rw [h,he,Nat.add_zero] at hd
      exact walk_of_word q a k z B ⟨hc.1,hc.2.1⟩ (by rw [weight_fast q k B hc.2.2.1 hc.2.2.2]; omega)
    next => contradiction
  next => contradiction

theorem stepChunk_complete {q a k B z : Nat} (ha : Interior q a)
    (hk : k≤64) (hb : B<2^k) (he : a+weight q k B=2^k*z) :
    stepChunk q a k B=some z := by
  have hh : 1≤a ∧ a+3≤q ∧ k≤64 ∧ B<2^k := ⟨ha.1,ha.2,hk,hb⟩
  rw [weight_fast q k B hk hb] at he
  have hx : a+q*B+dw64 B=2^k*z := by omega
  unfold stepChunk
  rw [if_pos hh]
  dsimp only
  rw [hx,Nat.mul_mod_right,if_pos rfl,Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- Balanced composition is important: a long checked witness need not
    construct either a giant wrap integer or a linearly deep proof term. -/
inductive WordTree where
  | leaf (bits word : Nat)
  | node (lo hi : WordTree)

def WordTree.span : WordTree → Nat
  | .leaf k _ => k
  | .node lo hi => lo.span+hi.span

def runTree (q a : Nat) : WordTree → Option Nat
  | .leaf k B => stepChunk q a k B
  | .node lo hi => (runTree q a lo).bind (fun b => runTree (q+lo.span) b hi)

theorem runTree_sound {q a z : Nat} {t : WordTree} (h : runTree q a t=some z) :
    Walk q a t.span z := by
  induction t generalizing q a z with
  | leaf k B => exact stepChunk_sound h
  | node lo hi ihl ihr =>
    simp only [runTree] at h
    cases hl : runTree q a lo with
    | none => simp [hl] at h
    | some b =>
      have hh : runTree (q+lo.span) b hi=some z := by simpa [hl] using h
      exact walk_append (ihl hl) (ihr hh)

/-- A certificate records a strict raw start, its clock, and a packed
    word tree taking it to the prescribed canonical endpoint. -/
structure Witness where
  clock : Nat
  carry : Nat
  tree : WordTree

def witnessCheck (q k z : Nat) (lower born : List Nat) (w : Witness) : Bool :=
  decide (w.clock+w.tree.span=q+k) &&
    (decide (runTree w.clock w.carry w.tree=some z)) &&
    ((decide (w.clock=q) && decide (fold q w.carry ∈ lower)) ||
     (decide (q<w.clock ∧ w.clock≤q+k) &&
      decide (fold w.clock w.carry=(w.clock-2)/2) && decide (w.clock ∈ born)))

theorem witnessCheck_sound {q k z : Nat} {lower born : List Nat} {w : Witness}
    (hz : Canon (q+k) z) (h : witnessCheck q k z lower born w=true) :
    (∃ a∈lower, FoldedWalk q a k z) ∨
    ∃ b∈born, q<b ∧ b≤q+k ∧ FoldedWalk b ((b-2)/2) (q+k-b) z := by
  simp only [witnessCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hclock,hrun⟩,hh⟩ := h
  have hw := runTree_sound hrun
  rcases hh with ⟨hq,ha⟩|⟨⟨hb,hfold⟩,hmem⟩
  · left
    have hspan : w.tree.span=k := by omega
    have hw' : Walk q w.carry k z := by simpa only [hq,hspan] using hw
    exact ⟨fold q w.carry,ha,w.carry,z,hw',rfl,hz.2⟩
  · right
    have hspan : w.tree.span=q+k-w.clock := by omega
    have hclock' : w.clock+(q+k-w.clock)=q+k := by omega
    refine ⟨w.clock,hmem,hb.1,hb.2,w.carry,z,?_,hfold,?_⟩
    · simpa only [hspan] using hw
    · simpa only [hclock'] using hz.2

/-- Check one positive witness per endpoint. A witness for every entry
    suffices even when the endpoint cover is only an overapproximation. -/
def checkBlock (q k : Nat) (lower born : List Nat) : List Nat → List Witness → Bool
  | [],[] => true
  | z::zs,w::ws => witnessCheck q k z lower born w && checkBlock q k lower born zs ws
  | _,_ => false

theorem checkBlock_sound (q k : Nat) (ends lower born : List Nat) (ws : List Witness)
    (he : ∀ z∈ends, Canon (q+k) z) (h : checkBlock q k lower born ends ws=true) :
    BlockCover q k ends lower born := by
  induction ends generalizing ws with
  | nil => intro z hz; simp at hz
  | cons z zs ih =>
    cases ws with
    | nil => simp [checkBlock] at h
    | cons w ws =>
      simp only [checkBlock,Bool.and_eq_true] at h
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact witnessCheck_sound (he x (by simp)) h.1
      · exact ih ws (fun y hy => he y (by simp [hy])) h.2 x hx

#print axioms stepChunk_sound
#print axioms stepChunk_complete
#print axioms runTree_sound
#print axioms witnessCheck_sound
#print axioms checkBlock_sound
end BB6.Agent43StrictWord
