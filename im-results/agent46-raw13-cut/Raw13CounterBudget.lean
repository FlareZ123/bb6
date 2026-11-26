import Raw13RightCounter

namespace BB6.Agent46Raw13CounterBudget
open BB6.Agent46Raw13RightCounter

structure Caps where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def caps : List Bool → Caps
  | [] => ⟨0,0,0⟩
  | b::W => let p := caps W; ⟨1-b.toNat+2*p.c,p.a,p.b⟩

def enough (W : List Bool) (n : Nat) : Prop :=
  n ≤ (caps W).a ∧ n ≤ (caps W).b ∧ n ≤ (caps W).c

theorem enough_mono {W : List Bool} {n m : Nat} (h : enough W n) (hm : m≤n) : enough W m := by
  unfold enough at *; omega

theorem enough_prepend (P W : List Bool) (n : Nat) (h : enough W n) : enough (P++W) n := by
  induction P with
  | nil => exact h
  | cons b P ih =>
    unfold enough at *
    simp only [List.cons_append,caps]
    omega

theorem caps_word_cons (t : Triple) (ts : List Triple) (R : List Bool) :
    caps (word (t::ts) R) =
      ⟨1-t.a.toNat+2*(caps (word ts R)).a,
       1-t.b.toNat+2*(caps (word ts R)).b,
       1-t.c.toNat+2*(caps (word ts R)).c⟩ := rfl

theorem caps_inc (ts us : List Triple) (R : List Bool) (hi : inc ts = some us) :
    (caps (word ts R)).a ≤ (caps (word us R)).a ∧
    (caps (word ts R)).b ≤ (caps (word us R)).b ∧
    (caps (word ts R)).c = (caps (word us R)).c+1 := by
  induction ts generalizing us with
  | nil => simp [inc] at hi
  | cons t ts ih =>
    obtain ⟨a,b,c⟩ := t
    cases c with
    | false =>
      simp [inc] at hi; subst us
      simp only [caps_word_cons,Bool.toNat_false,Bool.toNat_true,Nat.sub_zero,Nat.sub_self]
      omega
    | true =>
      simp only [inc,ite_true] at hi
      cases e : inc ts with
      | none => simp [e] at hi
      | some vs =>
        simp [e] at hi; subst us
        obtain ⟨ha,hb,hc⟩ := ih vs e
        simp only [caps_word_cons,Bool.toNat_false,Bool.toNat_true,Nat.sub_zero,Nat.sub_self]
        omega

theorem caps_add (ts us : List Triple) (R : List Bool) (d : Nat) (h : add ts d = some us) :
    (caps (word ts R)).a ≤ (caps (word us R)).a ∧
    (caps (word ts R)).b ≤ (caps (word us R)).b ∧
    (caps (word ts R)).c = (caps (word us R)).c+d := by
  induction d generalizing us with
  | zero => simp [add_zero] at h; subst us; simp
  | succ d ih =>
    rw [← add_add] at h
    simp only [add_one] at h
    cases e : add ts d with
    | none => simp [e] at h
    | some vs =>
      simp only [e,Option.bind_some] at h
      obtain ⟨h1,h2,h3⟩ := ih vs e
      obtain ⟨h4,h5,h6⟩ := caps_inc vs us R h
      omega

def split : List Bool → List Triple × List Bool
  | a::b::c::R => let p := split R; (⟨a,b,c⟩::p.1,p.2)
  | R => ([],R)

theorem word_split (W : List Bool) : word (split W).1 (split W).2 = W := by
  induction W using split.induct with
  | case1 a b c R ih => simp only [split,word,ih]
  | case2 R h =>
    cases R with
    | nil => rfl
    | cons a R => cases R with
      | nil => rfl
      | cons b R => cases R with
        | nil => rfl
        | cons c R => exact False.elim (h a b c R rfl)

theorem split_short (W : List Bool) : (split W).2.length < 3 := by
  induction W using split.induct with
  | case1 a b c R ih => exact ih
  | case2 R h =>
    cases R with
    | nil => decide
    | cons a R => cases R with
      | nil => simp [split]
      | cons b R => cases R with
        | nil => simp [split]
        | cons c R => exact False.elim (h a b c R rfl)

theorem cap_short (R : List Bool) (h : R.length < 3) : (caps R).c = 0 := by
  cases R with
  | nil => rfl
  | cons a R => cases R with
    | nil => rfl
    | cons b R => cases R with
      | nil => rfl
      | cons c R => simp at h; omega

theorem cap_value (ts : List Triple) (R : List Bool) (hr : R.length<3) :
    (caps (word ts R)).c + value ts + 1 = 2^ts.length := by
  induction ts with
  | nil => simp [word,value,cap_short R hr]
  | cons t ts ih =>
    have hb : t.c.toNat ≤ 1 := by cases t.c <;> decide
    simp only [caps_word_cons,value,List.length_cons,Nat.pow_succ]
    omega

theorem word_append (ts : List Triple) (R V : List Bool) :
    word ts (R++V) = word ts R ++ V := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [word,ih]

/-- Spend d units without touching any suffix beyond the protected prefix P. -/
theorem spend (P : List Bool) (b d : Nat) (hb : enough P b) (hd : d≤b) :
    ∃ ts us R, word ts R = P ∧ add ts d = some us ∧ enough (word us R) (b-d) := by
  let ts := (split P).1
  let R := (split P).2
  have hp : word ts R = P := word_split P
  have hcap := cap_value ts R (split_short P)
  rw [hp] at hcap
  have hs : value ts+d < 2^ts.length := by unfold enough at hb; omega
  have hsome : (add ts d).isSome := by rw [add_spec]; exact hs
  cases e : add ts d with
  | none => simp [e] at hsome
  | some us =>
    refine ⟨ts,us,R,hp,e,?_⟩
    obtain ⟨ha,hb',hc⟩ := caps_add ts us R d e
    rw [hp] at ha hb' hc
    unfold enough at *
    omega

theorem scan_inc_suffix (ts us : List Triple) (R : List Bool) (h : inc ts = some us) :
    ∃ j T, (∀ V, scan (true::word ts (R++V)) = (6*(j+1),T++V)) ∧
      word us R = zeros (3*j+2) ++ true::T := by
  induction ts generalizing us with
  | nil => simp [inc] at h
  | cons t ts ih =>
    obtain ⟨a,b,c⟩ := t
    cases c with
    | false =>
      simp [inc] at h; subst us
      refine ⟨0,word ts R,?_,rfl⟩
      intro V
      simp only [word,scan,word_append]
    | true =>
      simp only [inc,ite_true] at h
      cases ht : inc ts with
      | none => simp [ht] at h
      | some vs =>
        simp [ht] at h; subst us
        obtain ⟨j,T,hs,hv⟩ := ih vs ht
        refine ⟨j+1,T,?_,?_⟩
        · intro V
          simp only [word,scan,hs V]
          congr 1 <;> omega
        · change false::false::false::word vs R = _
          rw [hv,show 3*(j+1)+2=3+(3*j+2) by omega,zeros_add 3 (3*j+2)]
          rfl

/-- Exact one-increment scan with protected suffix, and a budget lower bound. -/
theorem scan_spend (P V : List Bool) (b : Nat) (hb : enough P (b+1)) :
    ∃ j T P', scan (true::(P++V)) = (6*(j+1),T++V) ∧
      P' = zeros (3*j+2) ++ true::T ∧ enough P' b := by
  obtain ⟨ts,us,R,hp,ha,hnew⟩ := spend P (b+1) 1 hb (by omega)
  rw [add_one] at ha
  obtain ⟨j,T,hs,hw⟩ := scan_inc_suffix ts us R ha
  refine ⟨j,T,word us R,?_,hw,?_⟩
  · rw [← hp,← word_append]
    exact hs V
  · simpa using hnew

#print axioms spend
#print axioms scan_spend
end BB6.Agent46Raw13CounterBudget
