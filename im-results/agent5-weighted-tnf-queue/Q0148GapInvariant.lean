import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent5Q0148GapInvariant

/-- Internal gap `u` denotes the physical gap `2*u+1`. -/
def chain : List Nat → Prop
  | [] => False
  | [x] => 1 ≤ x ∧ x ≤ 2
  | x::y::xs => (y ≤ x ∧ x ≤ y+1) ∧ chain (y::xs)

/-- `b` encodes the far-left gap 1 or 3. The final physical gap 4 is implicit.
The length of the internal gap list is `2*r`. -/
def first : List Nat → Nat
  | [] => 0
  | x::_ => x

def Good (b r : Nat) (xs : List Nat) : Prop :=
  b ≤ 1 ∧ 1 ≤ r ∧ xs.length = 2*r ∧ chain xs ∧
  (r+b = first xs ∨ r+b = first xs+1)

/-- On the high branch the new far gap is 3, otherwise 1. -/
def nextBit (b r : Nat) (xs : List Nat) : Nat :=
  if first xs = r+b then 1 else 0

def tailPad (b : Nat) : List Nat := if b = 0 then [2] else [2,1,1]

def nextGaps (b : Nat) (xs : List Nat) : List Nat :=
  xs.tail.map (·+1) ++ tailPad b

/-- Agent39's right-marker parameters, including the final zero. -/
def future (b : Nat) (xs : List Nat) : List Nat :=
  xs.tail.map (2*·) ++ (if b = 0 then [2,0] else [2,0,0,0])

theorem future_eq (b : Nat) (xs : List Nat) :
    future b xs = (nextGaps b xs).map (fun u => 2*(u-1)) ++ [0] := by
  by_cases hb : b=0 <;> simp [future,nextGaps,tailPad,hb,Function.comp_def,List.append_assoc]

theorem future_length (b r : Nat) (xs : List Nat) (h : Good b r xs) :
    (future b xs).length = 2*(r+b)+1 := by
  rcases h with ⟨hb,hr,hl,_,_⟩
  cases xs with
  | nil => simp at hl; omega
  | cons x xs =>
    simp only [List.length_cons] at hl
    by_cases hz : b=0
    · simp [future,hz]; omega
    · have hb' : b=1 := by omega
      simp [future,hb']; omega

/-- The exact head-height hypothesis for the original-source train. -/
theorem future_height (b r : Nat) (xs : List Nat) (h : Good b r xs) :
    (nextBit b r xs = 1 ∧ 2*first xs+1 = (future b xs).length) ∨
    (nextBit b r xs = 0 ∧ 2*first xs+3 = (future b xs).length) := by
  rw [future_length b r xs h]
  rcases h with ⟨_,_,_,_,hh⟩
  by_cases he : first xs = r+b
  · left; simp [nextBit,he]
  · right; simp [nextBit,he]; omega

theorem chain_extend (xs : List Nat) (b : Nat) (_hb : b ≤ 1)
    (h : chain xs) : chain (xs.map (·+1) ++ tailPad b) := by
  induction xs with
  | nil => simp [chain] at h
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [chain] at h
      by_cases hz : b=0
      · simp [tailPad,hz,chain]; omega
      · simp [tailPad,hz,chain]; omega
    | cons y ys =>
      simp only [chain] at h
      have ht := ih h.2
      simp only [List.map_cons,List.cons_append,chain]
      exact ⟨by omega,ht⟩

theorem good_next (b r : Nat) (xs : List Nat) (h : Good b r xs) :
    Good (nextBit b r xs) (r+b) (nextGaps b xs) := by
  rcases h with ⟨hb,hr,hlen,hchain,hhead⟩
  cases xs with
  | nil => simp at hlen; omega
  | cons x xs =>
    cases xs with
    | nil => simp at hlen; omega
    | cons y ys =>
      simp only [chain] at hchain
      have ht := chain_extend (y::ys) b hb hchain.2
      have hl : (tailPad b).length = 2*b+1 := by
        by_cases hz : b=0
        · simp [tailPad,hz]
        · have : b=1 := by omega
          simp [tailPad,this]
      have hx : r+b = x ∨ r+b = x+1 := by simpa [first] using hhead
      simp only [Good,nextBit,nextGaps,first,List.tail_cons,
        List.map_cons,List.cons_append,List.length_cons,List.length_append,List.length_map]
      refine ⟨?_,by omega,?_,ht,?_⟩
      · by_cases he : x = r+b <;> simp [he] <;> omega
      · simp only [List.length_cons] at hlen
        omega
      · by_cases he : x = r+b <;> simp [he] <;> omega

theorem base_good : Good 1 1 [1,1] := by simp [Good,chain,first]

/-- An infinite certified positive-step return relation on these gap states. -/
structure GapState where
  b : Nat
  r : Nat
  xs : List Nat

def valid (g : GapState) : Prop := Good g.b g.r g.xs

def next (g : GapState) : GapState :=
  ⟨nextBit g.b g.r g.xs, g.r+g.b, nextGaps g.b g.xs⟩

theorem next_valid (g : GapState) (h : valid g) : valid (next g) :=
  good_next g.b g.r g.xs h

/-- Generic composition interface: the source may use any canonical tape
encoding. The source theorem needs only a positive defined return, not
minimality of the epoch or an exact least-return-time proof. -/
theorem live_of_returns {S : Type} (run : Nat → S → Option S)
    (encode : GapState → S)
    (join : ∀ {a b x y z}, run a x = some y → run b y = some z →
      run (a+b) x = some z)
    (prefixRun : ∀ {a b x z}, a ≤ b → run b x = some z → run a x ≠ none)
    (ret : ∀ g, valid g → ∃ k, 0 < k ∧ run k (encode g) = some (encode (next g)))
    (g : GapState) (hg : valid g) (n : Nat) : run n (encode g) ≠ none := by
  have reach : ∀ n, ∃ k g', n ≤ k ∧ valid g' ∧ run k (encode g) = some (encode g') := by
    intro n
    induction n with
    | zero =>
      obtain ⟨k,hk,hr⟩ := ret g hg
      exact ⟨k,next g,by omega,next_valid g hg,hr⟩
    | succ n ih =>
      obtain ⟨k,g',hk,hg',hr⟩ := ih
      obtain ⟨t,ht,hs⟩ := ret g' hg'
      exact ⟨k+t,next g',by omega,next_valid g' hg',join hr hs⟩
  obtain ⟨k,g',hk,_,hr⟩ := reach n
  exact prefixRun hk hr

#print axioms live_of_returns
#print axioms good_next
#print axioms next_valid
#print axioms future_eq
#print axioms future_height
end BB6.Agent5Q0148GapInvariant
