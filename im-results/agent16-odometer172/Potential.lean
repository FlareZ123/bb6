import Std
namespace Odometer172

inductive Phase where | d | l | h deriving DecidableEq, Repr
inductive Boundary where | empty | zero | one deriving DecidableEq, Repr
abbrev Cell := Phase × Nat

def a : Cell → Int
  | (.d,g) => 3*(g:Int)-1
  | (.l,g) => 3*(g:Int)-2
  | (.h,g) => 3*(g:Int)

def b : Cell → Int
  | (.d,g) => -(g:Int)-1
  | (.l,g) => -(g:Int)-1
  | (.h,g) => -(g:Int)-2

def score : Bool → List Cell → Int
  | _, [] => 0
  | false, x::xs => a x + score true xs
  | true, x::xs => max 0 (b x + score false xs)

def pot (p : Bool) (xs : List Cell) : Int := 3*(xs.length:Int) + score p xs

theorem score_true_nonneg (xs : List Cell) : 0 ≤ score true xs := by
  cases xs <;> simp [score] <;> omega

theorem pot_true_nonneg (xs : List Cell) : 0 ≤ pot true xs := by
  have h := score_true_nonneg xs
  unfold pot
  omega

theorem pot_false_pos (x : Cell) (xs : List Cell) : 1 ≤ pot false (x::xs) := by
  have h := score_true_nonneg xs
  obtain ⟨p,g⟩ := x
  cases p <;> simp [pot, score, a] <;> omega

-- A projected carry with no new particle birth. The output increment e
-- is added to the gap immediately before the suffix.
inductive Carry : List Cell → Boundary → List Cell → Boundary → Nat → Prop where
  | wrapEmpty : Carry [] .empty [] .empty 0
  | wrapOne : Carry [] .one [] .zero 0
  | d (g : Nat) (xs : List Cell) (z : Boundary) :
      Carry ((.d,g)::xs) z ((.l,g)::xs) z 0
  | l (g : Nat) (xs : List Cell) (z : Boundary) :
      Carry ((.l,g+1)::xs) z ((.h,g)::xs) z 0
  | pair (g : Nat) (xs : List Cell) (z : Boundary) :
      Carry ((.l,0)::(.l,g)::xs) z xs z (g+1)
  | pairBoundary : Carry [(.l,0),(.d,0)] .empty [] .zero 1
  | drainEmpty : Carry [(.l,0)] .empty [] .zero 0
  | drainZero : Carry [(.l,0)] .zero [] .one 0
  | drainOne : Carry [(.l,0)] .one [] .empty 1
  | h (g : Nat) {xs ys : List Cell} {z z' : Boundary} {e : Nat} :
      Carry xs z ys z' e → Carry ((.h,g)::xs) z ((.d,g+e)::ys) z' 0

-- One simultaneous induction controls both parities. P0 bounds the required
-- incoming exceptional gap; P1 absorbs the increment of an exterior gap.
theorem carry_bounds {xs ys : List Cell} {z z' : Boundary} {e : Nat}
    (h : Carry xs z ys z' e) :
    ys.length ≤ xs.length ∧
    (xs ≠ [] → pot false ys ≤ pot false xs + (e:Int) - 1) ∧
    pot true ys ≤ pot true xs - 3*(e:Int) := by
  induction h with
  | wrapEmpty | wrapOne => simp [pot, score]
  | d g xs z => simp [pot, score, a, b] <;> omega
  | l g xs z => simp [pot, score, a, b] <;> omega
  | pair g xs z =>
    simp [pot, score, a, b]
    omega
  | pairBoundary | drainEmpty | drainZero | drainOne => decide
  | @h g xs ys z z' e hc ih =>
    obtain ⟨hlen,h0,h1⟩ := ih
    constructor
    · simpa using hlen
    constructor
    · intro _
      simp [pot, score, a] at h1 ⊢
      omega
    · cases xs with
      | nil =>
        cases hc <;> simp [pot, score, b] <;> omega
      | cons x xs =>
        have hh := h0 (by simp)
        simp [pot, score, b] at hh ⊢
        simp at hlen
        omega

-- External birth changes the last gap, or removes the last particle and
-- adds a cell to the previous gap. All particles are H at birth.
inductive BirthTail : List Cell → List Cell → Prop where
  | dec (g : Nat) : BirthTail [(.h,g+1)] [(.h,g)]
  | remove : BirthTail [(.h,0)] []
  | replace (g : Nat) : BirthTail [(.h,g),(.h,0)] [(.h,g+1)]
  | cons (g : Nat) {xs ys : List Cell} : ys ≠ [] → BirthTail xs ys →
      BirthTail ((.h,g)::xs) ((.h,g)::ys)

theorem birth_tail_bounds {xs ys : List Cell} (h : BirthTail xs ys) :
    ys.length ≤ xs.length ∧ pot false ys ≤ pot false xs ∧ pot true ys ≤ pot true xs := by
  induction h with
  | dec g => simp [pot, score, a, b] <;> omega
  | remove => decide
  | replace g => simp [pot, score, a, b] <;> omega
  | @cons g xs ys hne ht ih =>
    obtain ⟨hlen,h0,h1⟩ := ih
    simp [pot, score, a, b] at h0 h1 ⊢
    omega

def phaseFlag : Phase → Int
  | .h => 0
  | _ => 1

def Protected (g : Nat) (p : Phase) (xs : List Cell) : Prop :=
  pot false xs + phaseFlag p ≤ (g:Int)

theorem protected_positive {g : Nat} {p : Phase} {x : Cell} {xs : List Cell}
    (h : Protected g p (x::xs)) : 0 < g := by
  have hp := pot_false_pos x xs
  cases p <;> simp [Protected, phaseFlag] at h <;> omega

theorem protected_d {g : Nat} {xs : List Cell} (h : Protected g .d xs) :
    Protected g .l xs := h

theorem protected_l {g : Nat} {xs : List Cell} (h : Protected (g+1) .l xs) :
    Protected g .h xs := by
  simp [Protected,phaseFlag] at h ⊢
  omega

theorem protected_h {g e : Nat} {xs ys : List Cell} {z z' : Boundary}
    (hne : xs ≠ []) (hc : Carry xs z ys z' e) (hp : Protected g .h xs) :
    Protected (g+e) .d ys := by
  have h := (carry_bounds hc).2.1 hne
  simp [Protected,phaseFlag] at hp ⊢
  omega

theorem protected_merge_left {g e : Nat} {p q : Phase} {xs : List Cell}
    (hp : Protected g p xs) : Protected (g+e+1) q xs := by
  cases p <;> cases q <;> simp [Protected,phaseFlag] at hp ⊢ <;> omega

theorem protected_birth_tail {g : Nat} {p : Phase} {xs ys : List Cell}
    (hb : BirthTail xs ys) (hp : Protected g p xs) : Protected g p ys := by
  have h := (birth_tail_bounds hb).2.1
  unfold Protected at hp ⊢
  omega

def digit : Phase → Nat
  | .d => 0
  | .l => 1
  | .h => 2

def charge (x y : Cell) : Nat := (x.2 + digit y.1 + (if x.1 = .h then 1 else 0)) % 3

def good (x : Cell) : List Cell → Prop
  | [] => True
  | y::ys => charge x y = 1 ∨ Protected x.2 x.1 (y::ys)

def safe : List Cell → Prop
  | [] => True
  | x::xs => good x xs ∧ safe xs

theorem good_d {g : Nat} {xs : List Cell} (h : good (.d,g) xs) : good (.l,g) xs := by
  cases xs with
  | nil => trivial
  | cons y ys =>
    rcases h with h | h
    · exact Or.inl (by simpa [charge] using h)
    · exact Or.inr (protected_d h)

theorem good_l {g : Nat} {xs : List Cell} (h : good (.l,g+1) xs) : good (.h,g) xs := by
  cases xs with
  | nil => trivial
  | cons y ys =>
    rcases h with h | h
    · left
      simp [charge] at h ⊢
      omega
    · exact Or.inr (protected_l h)

-- At a carrying H, the incoming charge is preserved by an ordinary
-- transition; pair deletion combines the two exterior charges modulo 3.
theorem good_h {g e : Nat} {xs ys : List Cell} {z z' : Boundary}
    (hc : Carry xs z ys z' e) (hg : good (.h,g) xs) (hs : safe xs) :
    good (.d,g+e) ys := by
  have hp : xs ≠ [] → Protected g .h xs → Protected (g+e) .d ys :=
    fun hne h => protected_h hne hc h
  cases hc with
  | wrapEmpty | wrapOne | pairBoundary | drainEmpty | drainZero | drainOne => trivial
  | d k rs z =>
    rcases hg with hg | hg
    · left
      simpa [charge,digit] using hg
    · exact Or.inr (hp (by simp) hg)
  | l k rs z =>
    rcases hg with hg | hg
    · left
      simpa [charge,digit] using hg
    · exact Or.inr (hp (by simp) hg)
  | pair k =>
    cases ys with
    | nil => trivial
    | cons y rs =>
      rcases hg with hg | hg
      · have hj : good (.l,k) (y::rs) := hs.2.1
        rcases hj with hj | hj
        · left
          simp [charge,digit] at hg hj ⊢
          omega
        · right
          have h := protected_merge_left (e:=g) (q:=.d) hj
          simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
      · exact Or.inr (hp (by simp) hg)
  | @h k rs ts z z' f hc =>
    rcases hg with hg | hg
    · left
      simp [charge,digit] at hg ⊢
      omega
    · exact Or.inr (hp (by simp) hg)

theorem carry_safe {xs ys : List Cell} {z z' : Boundary} {e : Nat}
    (hc : Carry xs z ys z' e) (hs : safe xs) : safe ys := by
  induction hc with
  | wrapEmpty | wrapOne | pairBoundary | drainEmpty | drainZero | drainOne => trivial
  | d g xs z => exact ⟨good_d hs.1,hs.2⟩
  | l g xs z => exact ⟨good_l hs.1,hs.2⟩
  | pair g xs z => exact hs.2.2
  | @h g xs ys z z' e hc ih => exact ⟨good_h hc hs.1 hs.2,ih hs.2⟩

theorem good_birth_tail {x : Cell} {xs ys : List Cell} (hb : BirthTail xs ys)
    (hg : good x xs) : good x ys := by
  have hp : Protected x.2 x.1 xs → Protected x.2 x.1 ys := protected_birth_tail hb
  cases hb with
  | remove => trivial
  | dec k =>
    rcases hg with hg | hg
    · left
      exact hg
    · exact Or.inr (hp hg)
  | replace k =>
    rcases hg with hg | hg
    · left
      exact hg
    · exact Or.inr (hp hg)
  | cons k hne ht =>
    rcases hg with hg | hg
    · left
      exact hg
    · exact Or.inr (hp hg)

theorem birth_tail_safe {xs ys : List Cell} (hb : BirthTail xs ys) (hs : safe xs) : safe ys := by
  induction hb with
  | remove | dec | replace => simp [safe,good]
  | cons k hne ht ih => exact ⟨good_birth_tail ht hs.1,ih hs.2⟩

-- An exhausted internal gap in a safe state forces the next phase L.
theorem exhausted_safe {y : Cell} {ys : List Cell} (hg : good (.l,0) (y::ys)) : y.1 = .l := by
  rcases hg with hg | hg
  · obtain ⟨p,g⟩ := y
    cases p <;> simp [charge,digit] at hg ⊢
  · have h := protected_positive hg
    omega

def allH : List Cell → Prop
  | [] => True
  | x::xs => x.1 = .h ∧ allH xs

theorem carry_or_birth (xs : List Cell) (z : Boundary) (hs : safe xs) :
    (∃ ys z' e, Carry xs z ys z' e) ∨ (z = .zero ∧ allH xs) := by
  induction xs generalizing z with
  | nil =>
    cases z with
    | empty => exact Or.inl ⟨[],.empty,0,.wrapEmpty⟩
    | zero => exact Or.inr ⟨rfl,trivial⟩
    | one => exact Or.inl ⟨[],.zero,0,.wrapOne⟩
  | cons x xs ih =>
    obtain ⟨p,g⟩ := x
    cases p with
    | d => exact Or.inl ⟨(.l,g)::xs,z,0,.d g xs z⟩
    | l =>
      cases g with
      | succ g => exact Or.inl ⟨(.h,g)::xs,z,0,.l g xs z⟩
      | zero =>
        cases xs with
        | nil =>
          cases z with
          | empty => exact Or.inl ⟨[],.zero,0,.drainEmpty⟩
          | zero => exact Or.inl ⟨[],.one,0,.drainZero⟩
          | one => exact Or.inl ⟨[],.empty,1,.drainOne⟩
        | cons y ys =>
          obtain ⟨q,k⟩ := y
          have hq := exhausted_safe hs.1
          simp at hq
          subst q
          exact Or.inl ⟨ys,z,k+1,.pair k ys z⟩
    | h =>
      rcases ih z hs.2 with ⟨ys,z',e,hc⟩ | ⟨hz,hh⟩
      · exact Or.inl ⟨(.d,g+e)::ys,z',0,.h g hc⟩
      · exact Or.inr ⟨hz,rfl,hh⟩

-- Every all-H nonempty suffix has a birth-tail transformation.
theorem birth_tail_exists (xs : List Cell) (hh : allH xs) (hne : xs ≠ []) :
    ∃ ys, BirthTail xs ys := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨p,g⟩ := x
    obtain ⟨hp,ht⟩ := hh
    simp at hp
    subst p
    cases xs with
    | nil =>
      cases g with
      | zero => exact ⟨[],.remove⟩
      | succ g => exact ⟨[(.h,g)],.dec g⟩
    | cons y ys =>
      obtain ⟨out,hout⟩ := ih ht (by simp)
      cases out with
      | nil =>
        cases hout
        exact ⟨[(.h,g+1)],.replace g⟩
      | cons u us => exact ⟨(.h,g)::u::us,.cons g (by simp) hout⟩

def mass : List Cell → Nat
  | [] => 0
  | x::xs => x.2 + mass xs

theorem score_le_mass (xs : List Cell) :
    score false xs ≤ 3*(mass xs:Int) ∧ score true xs ≤ 3*(mass xs:Int) := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    obtain ⟨h0,h1⟩ := ih
    obtain ⟨p,g⟩ := x
    cases p <;> simp [score, mass, a, b] <;> omega

theorem pot_le_mass (xs : List Cell) :
    pot false xs ≤ 3*((xs.length+mass xs:Nat):Int) := by
  have h := (score_le_mass xs).1
  unfold pot
  omega

-- Exact distance drop at an L,L pair deletion, including the reset prefix.
-- p=3^j, x=p*(3^(m-j-2)-suffixValue), so x≥p>0.
theorem pair_distance_drop (p x : Nat) (hp : 0 < p) (hx : p ≤ x) :
    1 + (x-1) ≤ 9*x - 5*p := by omega

#print axioms carry_safe
#print axioms birth_tail_safe
#print axioms carry_or_birth
#print axioms birth_tail_exists
#print axioms carry_bounds
#print axioms birth_tail_bounds
#print axioms protected_h
#print axioms pot_le_mass
#print axioms pair_distance_drop
end Odometer172
