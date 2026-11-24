import F418Rules
import F418Episodes

namespace BB6.Agent32F418.TapeEncoding
open BB6Coverage BB6.Agent32FiniteSource
open Arithmetic EventSystem

/-- Equality of blank-padded finite words. -/
def WordEq (l r : List Bool) : Prop := ∀ i : Nat, l[i]?.getD false = r[i]?.getD false

theorem word_refl (l : List Bool) : WordEq l l := fun _ => rfl

theorem word_symm {l r : List Bool} (h : WordEq l r) : WordEq r l := fun i => (h i).symm

theorem word_trans {l m r : List Bool} (h : WordEq l m) (g : WordEq m r) : WordEq l r := fun i => (h i).trans (g i)

theorem word_cons {l r : List Bool} (b : Bool) (h : WordEq l r) : WordEq (b::l) (b::r) := by
  intro i; cases i with
  | zero => rfl
  | succ i => exact h i

theorem word_prefix (p : List Bool) {l r : List Bool} (h : WordEq l r) : WordEq (p++l) (p++r) := by
  induction p with
  | nil => exact h
  | cons b p ih => exact word_cons b ih

theorem word_zero (k : Nat) : WordEq (zeros k) [] := by
  intro i
  simp [zeros,List.getElem?_replicate]; split <;> rfl

theorem word_pad (l : List Bool) (k : Nat) : WordEq (l++zeros k) l := by
  simpa using word_prefix l (word_zero k)

/-- Finite configurations may have different lengths of explicit blanks. -/
structure TapeEq (c d : FiniteCfg) : Prop where
  state : c.state = d.state
  cur : c.cur = d.cur
  left : WordEq c.left d.left
  right : WordEq c.right d.right

theorem tape_refl (c : FiniteCfg) : TapeEq c c := ⟨rfl,rfl,word_refl _,word_refl _⟩

theorem tape_symm {c d : FiniteCfg} (h : TapeEq c d) : TapeEq d c :=
  ⟨h.state.symm,h.cur.symm,word_symm h.left,word_symm h.right⟩

theorem tape_trans {c d e : FiniteCfg} (h : TapeEq c d) (g : TapeEq d e) : TapeEq c e :=
  ⟨h.state.trans g.state,h.cur.trans g.cur,word_trans h.left g.left,word_trans h.right g.right⟩

theorem tape_query {c d : FiniteCfg} (h : TapeEq c d) : query c = query d := by
  unfold query; rw [h.state,h.cur]

theorem tape_move {c d : FiniteCfg} (h : TapeEq c d) (mv : Move) : TapeEq (move c mv) (move d mv) := by
  cases hr : mv.right
  · simp only [move,hr,Bool.false_eq_true,ite_false]
    refine ⟨rfl,?_,?_,word_cons _ h.right⟩
    · rw [get_head,get_head]; exact h.left 0
    · intro i; rw [get_tail,get_tail]; exact h.left (i+1)
  · simp only [move,hr,ite_true]
    refine ⟨rfl,?_,word_cons _ h.left,?_⟩
    · rw [get_head,get_head]; exact h.right 0
    · intro i; rw [get_tail,get_tail]; exact h.right (i+1)

theorem tape_step {m : Machine} {c d c' : FiniteCfg} (h : TapeEq c d) (hc : step m c = some c') :
    ∃ d', step m d = some d' ∧ TapeEq c' d' := by
  unfold step at hc ⊢
  rw [← tape_query h]
  cases he : m (query c) with
  | none => simp [he] at hc
  | some mv =>
    simp [he] at hc
    subst c'
    exact ⟨move d mv,rfl,tape_move h mv⟩

theorem tape_halt {m : Machine} {c d : FiniteCfg} (h : TapeEq c d) (hc : step m c = none) : step m d = none := by
  unfold step at hc ⊢; rw [← tape_query h]
  cases he : m (query c) <;> simp_all

theorem tape_run {m : Machine} {c d c' : FiniteCfg} {k : Nat} (h : TapeEq c d)
    (hc : finiteRun m k c = some c') : ∃ d', finiteRun m k d = some d' ∧ TapeEq c' d' := by
  induction k generalizing c d with
  | zero => simp [finiteRun] at hc; subst c'; exact ⟨d,rfl,h⟩
  | succ k ih =>
    cases he : step m c with
    | none => simp [finiteRun,he] at hc
    | some t =>
      obtain ⟨u,hu,ht⟩ := tape_step h he
      obtain ⟨d',hd',heq⟩ := ih ht (by simpa [finiteRun,he] using hc)
      exact ⟨d',by simpa [finiteRun,hu] using hd',heq⟩

/-- A counted run whose final word is canonical only up to trailing blanks. -/
def RunEq (k : Nat) (c d : FiniteCfg) : Prop := ∃ e, Run k c e ∧ TapeEq e d

theorem runEq_of_run {k : Nat} {c d : FiniteCfg} (h : Run k c d) : RunEq k c d := ⟨d,h,tape_refl d⟩

theorem runEq_input {k : Nat} {c d c' : FiniteCfg} (h : TapeEq c c') (hr : RunEq k c d) : RunEq k c' d := by
  obtain ⟨e,he,hEq⟩ := hr
  obtain ⟨e',he',hg⟩ := tape_run h he
  exact ⟨e',he',tape_trans (tape_symm hg) hEq⟩

theorem runEq_output {k : Nat} {c d d' : FiniteCfg} (hr : RunEq k c d) (h : TapeEq d d') : RunEq k c d' := by
  obtain ⟨e,he,hEq⟩ := hr
  exact ⟨e,he,tape_trans hEq h⟩

theorem runEq_trans {k l : Nat} {c d e : FiniteCfg} (h : RunEq k c d) (g : RunEq l d e) : RunEq (k+l) c e := by
  obtain ⟨c',hc,hc'⟩ := h
  obtain ⟨e',he,he'⟩ := runEq_input (tape_symm hc') g
  exact ⟨e',hc.trans he,he'⟩

theorem cfg_eq (q : Fin 6) (b : Bool) {l l' r r' : List Bool}
    (hl : WordEq l l') (hr : WordEq r r') : TapeEq (cfg q l b r) (cfg q l' b r') := ⟨rfl,rfl,hl,hr⟩

def digit (n : Nat) : Bool := n%2=1

/-- Left register digits, five cells per binary digit, low bit first. -/
def sparseDigits (N : Nat) : List Bool :=
  if _h : N=0 then [] else [digit N,false,false,false,false] ++ sparseDigits (N/2)
termination_by N
decreasing_by omega

def leftWord (d N : Nat) : List Bool := zeros d ++ sparseDigits N

theorem sparse_zero : sparseDigits 0 = [] := by rw [sparseDigits]; simp

theorem sparse_factor (j Q : Nat) :
    sparseDigits (2^j*(2*Q+1)) = zeros (5*j) ++ [true,false,false,false,false] ++ sparseDigits Q := by
  induction j with
  | zero =>
    simp only [Nat.pow_zero,Nat.one_mul,Nat.mul_zero]
    rw [sparseDigits]
    simp [digit,zeros,show (2*Q+1)/2=Q by omega]
  | succ j ih =>
    have hp : 0 < 2^j*(2*Q+1) := Nat.mul_pos (Nat.two_pow_pos j) (by omega)
    have he : 2^(j+1)*(2*Q+1) = 2*(2^j*(2*Q+1)) := by rw [Nat.pow_succ]; ac_rfl
    rw [he,sparseDigits]
    simp [show 2*(2^j*(2*Q+1)) ≠ 0 by omega,digit,ih]
    rw [show 5*(j+1)=5+5*j by omega,zeros_add]
    rfl

/-- Fixed-width left digits, stopping immediately after the last bit.
    The arbitrary suffix starts at the following cell. -/
def field : Nat → Nat → List Bool → List Bool
  | 0,_,tail => tail
  | 1,x,tail => [false,false,false,digit x] ++ tail
  | k+2,x,tail => [false,false,false,digit x,false] ++ field (k+1) (x/2) tail

/-- Fixed-width right register pairs, low digit first. -/
def pairs : Nat → Nat → List Bool
  | 0,_ => []
  | k+1,n => true :: digit n :: pairs k (n/2)

def rightWord (a n w : Nat) : List Bool := [true,false,true,digit a] ++ pairs w n

theorem field_zero (k : Nat) (tail : List Bool) : field (k+1) 0 tail = zeros (5*k+4) ++ tail := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show k+1+1=k+2 by omega,field]
    change [false,false,false,false,false] ++ field (k+1) 0 tail = _
    rw [ih,show 5*(k+1)+4=5+(5*k+4) by omega,zeros_add 5 (5*k+4)]
    simp only [List.append_assoc]
    rfl

theorem field_inc (k x : Nat) (tail : List Bool) (hx : x+1<2^k) :
    ∃ j l, field k x tail = carryWord j ++ [false,false,false,false] ++ l ∧
      field k (x+1) tail = zeros (5*j+3) ++ true::l := by
  induction k generalizing x with
  | zero => simp at hx
  | succ k ih =>
    cases k with
    | zero =>
      have h : x=0 := by omega
      subst x
      exact ⟨0,tail,rfl,rfl⟩
    | succ k =>
      by_cases he : x%2=0
      · refine ⟨0,false::field (k+1) (x/2) tail,?_,?_⟩
        · simp [field,carryWord,digit,show ¬x%2=1 by omega]
        · simp [field,zeros,digit,show (x+1)%2=1 by omega,show (x+1)/2=x/2 by omega]
      · have ho : x%2=1 := by omega
        have hdiv : x/2+1<2^(k+1) := by rw [Nat.pow_succ] at hx; omega
        obtain ⟨j,l,h1,h2⟩ := ih (x/2) hdiv
        refine ⟨j+1,l,?_,?_⟩
        · simp [field,digit,ho,carryWord,h1,List.append_assoc]
        · have hx' : (x+1)/2=x/2+1 := by omega
          have he' : (x+1)%2=0 := by omega
          simp only [field,digit,he',show ¬(0:Nat)=1 by decide,decide_false,hx',h2]
          rw [show 5*(j+1)+3=5+(5*j+3) by omega,zeros_add 5 (5*j+3)]
          rfl

theorem pairs_inc (w n : Nat) (hn : n+1<2^w) :
    ∃ j r, pairs w n = ones (2*j) ++ [true,false] ++ r ∧
      pairs w (n+1) = word0 j ++ [true,true] ++ r := by
  induction w generalizing n with
  | zero => simp at hn
  | succ w ih =>
    by_cases he : n%2=0
    · refine ⟨0,pairs w (n/2),?_,?_⟩
      · simp [pairs,digit,ones,show ¬n%2=1 by omega]
      · simp [pairs,digit,word0,show (n+1)%2=1 by omega,show (n+1)/2=n/2 by omega]
    · have ho : n%2=1 := by omega
      have hdiv : n/2+1<2^w := by rw [Nat.pow_succ] at hn; omega
      obtain ⟨j,r,h1,h2⟩ := ih (n/2) hdiv
      refine ⟨j+1,r,?_,?_⟩
      · rw [show 2*(j+1)=2+2*j by omega,ones_add 2 (2*j)]
        simp [pairs,digit,ho,h1,ones,List.append_assoc]
      · simp [pairs,digit,word0,show ¬(n+1)%2=1 by omega,show (n+1)/2=n/2+1 by omega,h2]

theorem pairs_full (w n : Nat) (hn : n+1=2^w) : pairs w n = ones (2*w) := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    have hp := Nat.two_pow_pos w
    rw [Nat.pow_succ] at hn
    have ho : n%2=1 := by omega
    have hdiv : n/2+1=2^w := by omega
    rw [show 2*(w+1)=2+2*w by omega,ones_add 2 (2*w)]
    simp [pairs,digit,ho,ih _ hdiv,ones]

theorem pairs_shift (e w n : Nat) : pairs (e+w) (2^e*n) = word0 e ++ pairs w n := by
  induction e with
  | zero => simp [word0]
  | succ e ih =>
    rw [Nat.succ_add,Nat.pow_succ]
    have he : 2^e*2*n=2*(2^e*n) := by ac_rfl
    rw [he]
    simp [pairs,digit,word0,ih]

theorem pairs_pow (W : Nat) : pairs (W+1) (2^W) = word0 W ++ [true,true] := by
  simpa [pairs,digit] using pairs_shift W 1 1

theorem pairs_reset (a n e w : Nat) (ha : a≤1) :
    pairs (w+e+2) (resetRight a n e) = word0 e ++ [true,true,true,digit a] ++ pairs w n := by
  have h : resetRight a n e=2^e*(4*n+1+2*a) := by unfold resetRight; ac_rfl
  rw [h,show w+e+2=e+(w+2) by omega,pairs_shift]
  have h1 : digit (4*n+1+2*a)=true := by simp [digit]; omega
  have h2 : (4*n+1+2*a)/2=2*n+a := by omega
  have h3 : digit (2*n+a)=digit a := by simp [digit]
  have h4 : (2*n+a)/2=n := by omega
  simp [pairs,h1,h2,h3,h4,List.append_assoc]

def fixedSparse : Nat → Nat → List Bool
  | 0,_ => []
  | k+1,x => [digit x,false,false,false,false] ++ fixedSparse k (x/2)

theorem fixed_zero (k : Nat) : fixedSparse k 0 = zeros (5*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 5*(k+1)=5+5*k by omega,zeros_add 5 (5*k)]
    simp [fixedSparse,digit,ih,zeros]

theorem fixed_sparse_eq (k x : Nat) (hx : x<2^k) : WordEq (fixedSparse k x) (sparseDigits x) := by
  induction k generalizing x with
  | zero =>
    have h : x=0 := by omega
    subst x
    rw [sparse_zero]
    exact word_refl _
  | succ k ih =>
    by_cases h : x=0
    · subst x; rw [fixed_zero,sparse_zero]; exact word_zero _
    · have hdiv : x/2<2^k := by rw [Nat.pow_succ] at hx; omega
      rw [fixedSparse,sparseDigits]
      simp only [h]
      exact word_prefix _ (ih _ hdiv)

theorem field_fixed (k x : Nat) : field (k+1) x (zeros 4) = zeros 3 ++ fixedSparse (k+1) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [show k+1+1=k+2 by omega,field,ih]
    rfl

theorem field_canonical (k x : Nat) (hx : x<2^(k+1)) :
    WordEq (field (k+1) x (zeros 4)) (leftWord 3 x) := by
  rw [field_fixed,leftWord]
  exact word_prefix _ (fixed_sparse_eq _ _ hx)

def shiftedTail (k : Nat) (tail : List Bool) : List Bool := if k=0 then tail else false::tail

theorem field_full (k x : Nat) (tail : List Bool) (hx : x+1=2^(k+1)) :
    field (k+1) x tail = carryWord k ++ [false,false,false,true] ++ tail := by
  induction k generalizing x with
  | zero =>
    have h : x=1 := by omega
    subst x
    rfl
  | succ k ih =>
    have hp := Nat.two_pow_pos (k+1)
    rw [Nat.pow_succ] at hx
    have ho : x%2=1 := by omega
    have hdiv : x/2+1=2^(k+1) := by omega
    simp [field,carryWord,digit,ho,ih _ hdiv,List.append_assoc]

theorem shifted_field_zero (k : Nat) (tail : List Bool) :
    field k 0 (shiftedTail k tail) = zeros (5*k) ++ tail := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [field_zero]
    simp only [shiftedTail,Nat.succ_ne_zero,ite_false]
    rw [show 5*(k+1)=(5*k+4)+1 by omega,zeros_add (5*k+4) 1]
    simp only [List.append_assoc]
    rfl

theorem carryWord_snoc (k : Nat) : carryWord k ++ [false,false,false,true,false] = carryWord (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [carryWord,ih]

theorem shifted_field_full (k x : Nat) (tail : List Bool) (hx : x+1=2^k) :
    field k x (shiftedTail k tail) = carryWord k ++ tail := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [field_full k x _ hx]
    simp only [shiftedTail,Nat.succ_ne_zero,ite_false]
    rw [← carryWord_snoc k]
    simp [List.append_assoc]

end BB6.Agent32F418.TapeEncoding
