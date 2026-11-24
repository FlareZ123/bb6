import Lean
namespace BB6.Agent43ReverseSet

def extract (base bits : Nat) : Nat → List Nat
  | 0 => if bits.testBit 0 then [base] else []
  | L+1 => if bits=0 then [] else
      extract base (bits % 2^(2^L)) L ++ extract (base+2^L) (bits >>> 2^L) L

theorem extract_iff (base bits L c : Nat) :
    c ∈ extract base bits L ↔ base≤c ∧ c<base+2^L ∧ bits.testBit (c-base)=true := by
  induction L generalizing base bits with
  | zero =>
    by_cases h : c=base
    · subst c; simp [extract]
    · simp [extract,h]; omega
  | succ L ih =>
    by_cases hz : bits=0
    · simp [extract,hz]
    · rw [extract,if_neg hz,List.mem_append,ih,ih,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,Nat.pow_succ]
      constructor
      · rintro (⟨h1,h2,h3⟩|⟨h1,h2,h3⟩)
        · rw [Bool.and_eq_true] at h3
          exact ⟨h1,by omega,h3.2⟩
        · have he : 2^L+(c-(base+2^L))=c-base := by omega
          rw [he] at h3
          exact ⟨by omega,by omega,h3⟩
      · rintro ⟨h1,h2,h3⟩
        by_cases h : c<base+2^L
        · left; exact ⟨h1,h,by simp [show c-base<2^L by omega,h3]⟩
        · right
          have he : 2^L+(c-(base+2^L))=c-base := by omega
          exact ⟨by omega,by omega,by rwa [he]⟩

/-- Sorted set union; membership soundness does not require sortedness. -/
def mergeUnique : Nat → List Nat → List Nat → List Nat
  | 0,xs,ys => xs++ys
  | _+1,[],ys => ys
  | _+1,xs,[] => xs
  | f+1,a::xs,b::ys =>
      if a<b then a::mergeUnique f xs (b::ys)
      else if b<a then b::mergeUnique f (a::xs) ys
      else a::mergeUnique f xs ys

theorem mem_mergeUnique (f : Nat) (xs ys : List Nat) (c : Nat) :
    c∈mergeUnique f xs ys ↔ c∈xs ∨ c∈ys := by
  induction f generalizing xs ys with
  | zero => simp [mergeUnique,List.mem_append]
  | succ f ih =>
    cases xs with
    | nil => simp [mergeUnique]
    | cons a xs =>
      cases ys with
      | nil => simp [mergeUnique]
      | cons b ys =>
        simp only [mergeUnique]
        split
        · simp only [List.mem_cons,ih,or_assoc,or_left_comm]
        · split
          · simp only [List.mem_cons,ih,or_assoc,or_left_comm]
          · have hab : a=b := by omega
            subst b
            simp only [List.mem_cons,ih,or_assoc,or_left_comm]
            by_cases hc : c=a <;> simp [hc]

/-- Reverse carry map is monotone separately on the two branches for
bounded carry lists. Membership soundness does not depend on that bound. -/
def backStep (C y : Nat) (cs : List Nat) : List Nat :=
  let lo := cs.filterMap fun c => if 2*c+y<C then some ((2*c+y)%C) else none
  let hi := cs.filterMap fun c => if 2*c+y<C then none else some ((2*c+y)%C)
  mergeUnique (lo.length+hi.length) lo hi

theorem backStep_sound (C y c : Nat) (cs : List Nat) (h : c∈cs) :
    (2*c+y)%C ∈ backStep C y cs := by
  unfold backStep
  apply (mem_mergeUnique _ _ _ _).2
  by_cases hh : 2*c+y<C
  · left; exact List.mem_filterMap.mpr ⟨c,h,by simp [hh]⟩
  · right; exact List.mem_filterMap.mpr ⟨c,h,by simp [hh]⟩

/-- Generic backward map with weights and target bits depending on position. -/
def rewind (C y : Nat → Nat) (s : Nat) : Nat → Nat → Nat
  | 0,c => c
  | k+1,c => rewind C y s k ((2*c+y (s+k))%C (s+k))

def rewindSet (C y : Nat → Nat) (s : Nat) : Nat → List Nat → List Nat
  | 0,cs => cs
  | _+1,[] => []
  | k+1,[c] => [rewind C y s (k+1) c]
  | k+1,c::d::cs => rewindSet C y s k (backStep (C (s+k)) (y (s+k)) (c::d::cs))

theorem rewindSet_sound (C y : Nat → Nat) (s k c : Nat) (cs : List Nat) (h : c∈cs) :
    rewind C y s k c ∈ rewindSet C y s k cs := by
  induction k generalizing c cs with
  | zero => exact h
  | succ k ih =>
    cases cs with
    | nil => simp at h
    | cons a as =>
      cases as with
      | nil => simp at h; subst c; simp [rewindSet]
      | cons b bs => exact ih _ _ (backStep_sound _ _ _ _ h)

/-- Coverage of bitset union does not need disjointness. -/
def unionBits (xs : List Nat) : Nat := xs.foldr (· ||| ·) 0

theorem bit_union (xs : List Nat) (c : Nat) (h : (unionBits xs).testBit c=true) :
    ∃ b∈xs, b.testBit c=true := by
  induction xs with
  | nil => simp [unionBits] at h
  | cons a as ih =>
    simp only [unionBits,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true_iff] at h
    rcases h with h|h
    · exact ⟨a,by simp,h⟩
    · obtain ⟨b,hb,hbit⟩ := ih h
      exact ⟨b,by simp [hb],hbit⟩

#print axioms extract_iff
#print axioms rewindSet_sound
#print axioms bit_union
end BB6.Agent43ReverseSet
