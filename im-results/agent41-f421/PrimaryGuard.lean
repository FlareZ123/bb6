import Std

namespace F421PrimaryGuard

structure Cell where
  p : Nat
  q : Nat
  deriving Repr, DecidableEq

/-- Cells are ordered from the far end toward the head. B is the current
    positional power of two; C is the positional power after deletions. -/
def Good (B : Nat) : List Cell → Prop
  | [] => True
  | c :: cs => (∃ l : Nat, 0 < l ∧ c.p = l * (2*B)) ∧ B+2 ≤ c.q ∧ Good (2*B) cs

def reduce (B C carry : Nat) : List Cell → List Cell × Nat × Nat
  | [] => ([], C, carry)
  | c :: cs =>
    if c.p = 2*B then
      reduce (2*B) C (carry+c.q+B) cs
    else
      let (ys,D,r) := reduce (2*B) (2*C) 0 cs
      (⟨c.p-2*B,c.q+B+carry-C⟩ :: ys, D, r)

/-- Every all-marked A cell uses precisely the standard number of carry events,
    even when its P run disappears at the terminal visit. -/
theorem cellCount (B H p : Nat) (hb : 0 < B) (hh : H+1=B)
    (hp : 2*B ≤ p) :
    min (p-1) (2*H+1)=2*B-1 ∧ (min (p-1) (2*H+1)+1)/2=B ∧
    H+(min (p-1) (2*H+1)+1)/2+1=2*B := by
  have he : 2*H+1=2*B-1 := by omega
  have hm : 2*H+1 ≤ p-1 := by omega
  rw [Nat.min_eq_right hm, he]
  omega

/-- One surviving cell meets both odd-crossing guards. -/
theorem survivorGuard (B C carry p q : Nat)
    (hb : 2 ≤ B) (hc : C ≤ B) (hp : 2*B+3 ≤ p) (hq : B+2 ≤ q) :
    3 ≤ p-2*B ∧ 2*C+2 ≤ q+B+carry ∧ C+2 ≤ q+B+carry-C := by
  omega

/-- The reduced head preserves divisibility and Q lower bounds. The final
    survivor scale lies between the entering scale and the original final
    scale. B=C*t gives divisibility after farther deletions. -/
theorem reduceGood (xs : List Cell) (B C carry : Nat)
    (hb : 2 ≤ B) (hc : 2 ≤ C) (hcb : C ≤ B)
    (hd : ∃ t : Nat, B = C*t) (hg : Good B xs) :
    let (ys,D,r) := reduce B C carry xs
    Good C ys ∧ D = C*2^ys.length ∧ D ≤ B*2^xs.length := by
  induction xs generalizing B C carry with
  | nil =>
    simp [reduce,Good,hcb]
  | cons c cs ih =>
    rcases hg with ⟨⟨l,hl,hp⟩,hq,ht⟩
    obtain ⟨t,he⟩ := hd
    by_cases hz : c.p=2*B
    · have hd' : ∃ t : Nat, 2*B=C*t := ⟨2*t,by rw [he]; ac_rfl⟩
      have hi := ih (2*B) C (carry+c.q+B) (by omega) hc (by omega) hd' ht
      simp only [reduce,if_pos hz,List.length_cons]
      have he' : 2*B*2^cs.length=B*2^(cs.length+1) := by rw [Nat.pow_succ]; ac_rfl
      rw [← he']
      exact hi
    · have hl2 : 2 ≤ l := by
        by_cases h : l=1
        · subst l
          simp at hp
          exact False.elim (hz hp)
        · omega
      have hd' : ∃ t : Nat, 2*B=(2*C)*t := ⟨t,by rw [he]; ac_rfl⟩
      have hi := ih (2*B) (2*C) 0 (by omega) (by omega) (by omega) hd' ht
      rcases hred : reduce (2*B) (2*C) 0 cs with ⟨ys,D,r⟩
      rw [hred] at hi
      rcases hi with ⟨hy,hD,hbound⟩
      simp only [reduce,if_neg hz,hred,List.length_cons]
      constructor
      · change (∃ l' : Nat, 0 < l' ∧ c.p-2*B=l'*(2*C)) ∧ C+2 ≤ c.q+B+carry-C ∧ Good (2*C) ys
        refine ⟨⟨(l-1)*t,?_,?_⟩,by omega,hy⟩
        · have htpos : 0 < t := by
            by_cases h : t=0
            · simp [h] at he
              omega
            · omega
          exact Nat.mul_pos (by omega) htpos
        · calc
            c.p-2*B = l*(2*B)-1*(2*B) := by simp [hp]
            _ = (l-1)*(2*B) := (Nat.sub_mul l 1 (2*B)).symm
            _ = (l-1)*t*(2*C) := by rw [he]; ac_rfl
      · constructor
        · rw [hD,Nat.pow_succ]; ac_rfl
        · calc
            D ≤ (2*B)*2^cs.length := hbound
            _ = B*2^(cs.length+1) := by rw [Nat.pow_succ]; ac_rfl

theorem goodAppend (xs ys : List Cell) (B : Nat) (hx : Good B xs)
    (hy : Good (B*2^xs.length) ys) : Good B (xs++ys) := by
  induction xs generalizing B with
  | nil => simpa using hy
  | cons c cs ih =>
    rcases hx with ⟨hp,hq,ht⟩
    refine ⟨hp,hq,ih (2*B) ht ?_⟩
    simpa only [List.length_cons,Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hy

/-- Closed primary-cycle arithmetic, after the two odd crossings cancel. -/
def advanceHead (B : Nat) (xs : List Cell) : List Cell :=
  let (ys,D,r) := reduce B B 0 xs
  let M := B*2^xs.length
  ys++[⟨4*M,4*M-1+r-D⟩]

theorem advanceHeadGood (B : Nat) (xs : List Cell)
    (hb : 2 ≤ B) (hx : Good B xs) : Good B (advanceHead B xs) := by
  have h := reduceGood xs B B 0 hb hb (Nat.le_refl B) ⟨1,by simp⟩ hx
  rcases hr : reduce B B 0 xs with ⟨ys,D,r⟩
  rw [hr] at h
  rcases h with ⟨hy,hD,hbound⟩
  let M := B*2^xs.length
  have hDM : D ≤ M := hbound
  have hdvd : D ∣ M := by
    have hlen : ys.length ≤ xs.length := by
      by_cases hl : ys.length ≤ xs.length
      · exact hl
      · have hlt := Nat.pow_lt_pow_right (a:=2) (by decide) (show xs.length < ys.length by omega)
        have hp := Nat.le_of_mul_le_mul_left (show B*2^ys.length ≤ B*2^xs.length by simpa [hD] using hbound) (show 0<B by omega)
        omega
    rw [hD]
    exact Nat.mul_dvd_mul_left B (Nat.pow_dvd_pow 2 hlen)
  have hDpos : 2 ≤ D := by
    have hp : 0 < 2^ys.length := Nat.pow_pos (by decide)
    have hh : B ≤ B*2^ys.length := by
      have hh := Nat.mul_le_mul_left B (show 1 ≤ 2^ys.length by omega)
      simpa using hh
    omega
  obtain ⟨t,ht⟩ := hdvd
  have htpos : 0 < t := by
    by_cases hz : t=0
    · simp [hz] at ht
      omega
    · omega
  have hgnew : Good D [⟨4*M,4*M-1+r-D⟩] := by
    change (∃ l : Nat, 0<l ∧ 4*M=l*(2*D)) ∧ D+2 ≤ 4*M-1+r-D ∧ True
    refine ⟨⟨2*t,by omega,?_⟩,by omega,trivial⟩
    rw [ht]; ac_rfl
  unfold advanceHead
  rw [hr]
  exact goodAppend ys _ B hy (by rw [← hD]; exact hgnew)

def iterateHead (B : Nat) : Nat → List Cell → List Cell
  | 0,xs => xs
  | k+1,xs => iterateHead B k (advanceHead B xs)

theorem iterateHeadGood (B k : Nat) (xs : List Cell)
    (hb : 2 ≤ B) (hx : Good B xs) : Good B (iterateHead B k xs) := by
  induction k generalizing xs with
  | zero => exact hx
  | succ k ih => exact ih _ (advanceHeadGood B xs hb hx)

theorem suffixBudget (B p k : Nat) (h : (k+1)*(2*B)+3 ≤ p) :
    2*B+3 ≤ p ∧ k*(2*B)+3 ≤ p-2*B := by
  rw [Nat.succ_mul] at h
  omega

#print axioms reduceGood
#print axioms advanceHeadGood
#print axioms iterateHeadGood
#print axioms suffixBudget
end F421PrimaryGuard
