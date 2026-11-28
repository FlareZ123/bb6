import M44Actions
import Init.Data.Nat.Bitwise.Lemmas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38M44
open BB6Coverage BB6Coverage.Agent31Pump

-- Low-bit-first immutable lookup tree. Bounds are enforced on reachable triples.
inductive Lookup (α : Type) where
  | leaf : α → Lookup α
  | branch : Lookup α → Lookup α → Lookup α

def Lookup.get : Lookup α → Nat → α
  | .leaf a, _ => a
  | .branch x y, i => if i % 2 == 0 then x.get (i/2) else y.get (i/2)

-- Enumerate only actual set bits; zero masks terminate immediately.
def checkMask (f : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0,_,_ => true
  | n+1,r,m =>
    if m = 0 then true else
      (if m.testBit 0 then f r else true) && checkMask f n (r+1) (m/2)

theorem checkMask_sound (f : Nat → Bool) (n r m i : Nat)
    (h : checkMask f n r m = true) (hi : i<n) (hm : m.testBit i = true) : f (r+i) = true := by
  induction n generalizing r m i with
  | zero => omega
  | succ n ih =>
    simp only [checkMask] at h
    have hn : m ≠ 0 := by
      intro he
      subst m
      simp at hm
    rw [if_neg hn,Bool.and_eq_true] at h
    cases i with
    | zero =>
      rw [hm,if_pos rfl] at h
      simpa only [Nat.add_zero] using h.1
    | succ i =>
      have hi' : i<n := by omega
      have hm' : (m/2).testBit i = true := by
        rw [← Nat.testBit_succ]
        exact hm
      have H := ih (r+1) (m/2) i h.2 hi' hm'
      rwa [show r+1+i = r+(i+1) by omega] at H

structure Graph where
  pred : Lookup (List (Nat × Nat))
  delta : Lookup Nat

-- A concrete list is represented bottom-up by actual inverse edges. The empty
-- word has state 0; no assumption that the DFA is total is needed.
inductive Represents (g : Graph) : List Nat → Nat → Prop where
  | nil : Represents g [] 0
  | cons {b s i j} : b < 17 → Represents g s i → (b,i) ∈ g.pred.get j → Represents g (b::s) j

def push (g : Graph) (i b : Nat) : Option Nat :=
  let k := (g.delta.get i >>> (11*b)) &&& 2047
  if k = 0 then none else
  let j := k-1
  if b < 17 ∧ (b,i) ∈ g.pred.get j then some j else none

def pushWord (g : Graph) : List Nat → Nat → Option Nat
  | [],i => some i
  | b::s,i => (pushWord g s i).bind (fun j => push g j b)

theorem push_sound (g : Graph) (s : List Nat) (i b j : Nat)
    (hs : Represents g s i) (h : push g i b = some j) : Represents g (b::s) j := by
  unfold push at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · rename_i hh
      cases h
      exact Represents.cons hh.1 hs hh.2
    · contradiction

theorem pushWord_sound (g : Graph) (w s : List Nat) (i j : Nat)
    (hs : Represents g s i) (h : pushWord g w i = some j) : Represents g (w++s) j := by
  induction w generalizing j with
  | nil =>
    simp only [pushWord,Option.some.injEq] at h
    subst j
    exact hs
  | cons b w ih =>
    simp only [pushWord] at h
    cases hp : pushWord g w i with
    | none => simp [hp] at h
    | some k =>
      rw [hp] at h
      exact push_sound g (w++s) k b j (ih k hp) h

structure Cert where
  nl : Nat
  nr : Nat
  left : Graph
  right : Graph
  rows : Lookup Nat

def Cert.getRow (c : Cert) (q l : Nat) := c.rows.get (q*c.nl+l)
def Cert.good (c : Cert) (q l r : Nat) : Bool :=
  q < 14 && l < c.nl && r < c.nr && (c.getRow q l).testBit r

def checkEdge (c : Cert) (q l r : Nat) (e : Nat × Nat) : Bool :=
  if e.1 > 17 then false else
  match action q e.1 with
  | none => false
  | some a =>
    let i := if isLeft q then e.2 else l
    let j := if isLeft q then r else e.2
    match pushWord c.left a.l i, pushWord c.right a.r j with
    | some i', some j' => c.good a.q i' j'
    | _, _ => false

def checkRow (c : Cert) (q l : Nat) : Bool :=
  checkMask (fun r =>
    let es := if isLeft q then c.left.pred.get l else c.right.pred.get r
    es.all (checkEdge c q l r)) c.nr 0 (c.getRow q l)

def checkQ (c : Cert) (q : Nat) := (List.range c.nl).all (checkRow c q)

def closed (c : Cert) : Prop := ∀ q < 14, checkQ c q = true

theorem good_bounds (c : Cert) (q l r : Nat) (h : c.good q l r = true) :
    q<14 ∧ l<c.nl ∧ r<c.nr ∧ (c.getRow q l).testBit r = true := by
  simp only [Cert.good,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq,hl⟩,hr⟩,hm⟩ := h
  exact ⟨hq,hl,hr,hm⟩

theorem edge_checked (c : Cert) (hc : closed c) (q l r : Nat)
    (h : c.good q l r = true) (e : Nat × Nat)
    (he : e ∈ (if isLeft q then c.left.pred.get l else c.right.pred.get r)) :
    checkEdge c q l r e = true := by
  obtain ⟨hq,hl,hr,hm⟩ := good_bounds c q l r h
  have H := hc q hq
  unfold checkQ at H
  have H1 := (List.all_eq_true.mp H) l (List.mem_range.mpr hl)
  unfold checkRow at H1
  have H2 := checkMask_sound _ c.nr 0 (c.getRow q l) r H1 hr hm
  simp only [Nat.zero_add] at H2
  exact (List.all_eq_true.mp H2) e he

theorem edge_success (c : Cert) (q l r : Nat) (e : Nat × Nat)
    (h : checkEdge c q l r e = true) :
    ∃ a i' j', e.1 ≤ 17 ∧ action q e.1 = some a ∧
      pushWord c.left a.l (if isLeft q then e.2 else l) = some i' ∧
      pushWord c.right a.r (if isLeft q then r else e.2) = some j' ∧
      c.good a.q i' j' = true := by
  unfold checkEdge at h
  split at h
  · contradiction
  · rename_i hb
    have hb' : e.1 ≤ 17 := by omega
    cases ha : action q e.1 with
    | none => simp [ha] at h
    | some a =>
      rw [ha] at h
      dsimp only at h
      cases hi : pushWord c.left a.l (if isLeft q then e.2 else l) with
      | none => simp [hi] at h
      | some i' =>
        cases hj : pushWord c.right a.r (if isLeft q then r else e.2) with
        | none => simp [hi,hj] at h
        | some j' =>
          rw [hi,hj] at h
          exact ⟨a,i',j',hb',rfl,hi,hj,h⟩

-- Obtain a real pop, including the exact empty-word sentinel.
theorem pop_sound (g : Graph) (h0 : (17,0) ∈ g.pred.get 0)
    (s : List Nat) (i : Nat) (h : Represents g s i) :
    ∃ b t j, b≤17 ∧ s = putBack b t ∧ (b=17 → t=[]) ∧ Represents g t j ∧ (b,j) ∈ g.pred.get i := by
  cases h with
  | nil => exact ⟨17,[],0,by decide,rfl,fun _ => rfl,.nil,h0⟩
  | @cons b s i j hb hs he =>
    refine ⟨b,s,i,by omega,?_,?_,hs,he⟩
    · unfold putBack
      split
      · rename_i h
        have : b=17 := beq_iff_eq.mp h
        omega
      · rfl
    · intro h
      omega

end BB6.Agent38M44
