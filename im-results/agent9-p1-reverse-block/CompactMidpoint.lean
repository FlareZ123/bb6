import CompactCover
import ReverseBlockJump
import LagReverse

namespace BB6.Agent9CompactMidpoint

open BB6.Agent45.DelayedCarry
open BB6.Agent9CompactState
open BB6.Agent9CompactCover
open BB6.Agent45ReverseBlock
open BB6.Agent9ReverseBlock (JumpCover walk_mem_prefix_live)

theorem qextend_word (n s Q a k R c : Nat) (he : QExtend n s Q a k R c) :
    ∃ X, X<2^k ∧ R=(Q+total n*X)/2^k := by
  induction he with
  | nil => exact ⟨0,by simp,by simp⟩
  | step k R c x d he hx hh ih =>
    obtain ⟨X,hX,hR⟩ := ih
    refine ⟨X+2^k*x,?_,?_⟩
    · rw [Nat.pow_succ]
      rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp <;> omega
    · rw [hR,Nat.pow_succ,←Nat.div_div_eq_div_mul]
      have hEq : Q+total n*(X+2^k*x)=(Q+total n*X)+2^k*(total n*x) := by
        rw [Nat.mul_add]; ac_rfl
      rw [hEq,Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]

/-- All delayed bits through the original window are fixed, even for
    abstract queues not known to lift to an authentic selected word. -/
def qTarget (Q j : Nat) : Nat := (Q/2^j)%2

theorem qtarget_shift (n s Q a k R c j : Nat) (he : QExtend n s Q a k R c)
    (hj : k+j<n) : qTarget R j=qTarget Q (k+j) := by
  obtain ⟨X,hX,hR⟩ := qextend_word n s Q a k R c he
  unfold qTarget
  rw [hR,Nat.div_div_eq_div_mul,←Nat.pow_add]
  have hp : (2:Nat)^n=2^(k+j+1)*2^(n-(k+j+1)) := by
    rw [←Nat.pow_add]; congr 1; omega
  have h : total n*X=2^(k+j)*(2*(7*2^(n-(k+j+1))*X)) := by
    unfold total
    rw [hp,Nat.pow_succ]
    ac_rfl
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  omega

theorem qextend_carry_lt (n s Q a k R c : Nat) (ha : a<n+s+3)
    (he : QExtend n s Q a k R c) : c<n+s+k+3 := by
  induction he with
  | nil => omega
  | step k R c x d he hx hh ih =>
    rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp at hh <;> omega

def qWord (Q j : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => qWord Q j k ++ [qTarget Q (j+k)]

@[simp] theorem qWord_length (Q j k : Nat) : (qWord Q j k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [qWord,ih]

theorem qWord_bits (Q j k : Nat) : ∀ y ∈ qWord Q j k,y≤1 := by
  induction k with
  | zero => simp [qWord]
  | succ k ih =>
    intro y hy
    simp only [qWord,List.mem_append,List.mem_singleton] at hy
    rcases hy with h|rfl
    · exact ih y h
    · unfold qTarget; omega

theorem qword_shift (n s Q a k R c j : Nat) (he : QExtend n s Q a k R c)
    (hj : k+j≤n) : qWord R 0 j=qWord Q k j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [qWord,Nat.zero_add]
    rw [ih (by omega),qtarget_shift n s Q a k R c j he (by omega)]

theorem qextend_walk (n s Q a k R c : Nat) (ha : a<n+s+3)
    (hk : k≤n) (he : QExtend n s Q a k R c) :
    Walk (n+s+3+k) c (qWord Q 0 k) a := by
  induction he with
  | nil => exact Walk.nil (by omega)
  | step k R c x d he hx hh ih =>
    have hc := qextend_carry_lt n s Q a k R c ha he
    have hd : d<n+s+k+3 := by
      rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp at hh <;> omega
    have hy : R%2=qTarget Q k := by
      have h := qtarget_shift n s Q a k R c 0 he (by omega)
      simpa [qTarget] using h
    rw [hy] at hh
    have hclock : n+s+3+(k+1)-(0+1)=n+s+k+3 := by omega
    have hsingle : Walk (n+s+3+(k+1)) d [qTarget Q k] c := by
      refine Walk.step [] d (qTarget Q k) x c (Walk.nil (by omega))
        (by unfold qTarget; omega) hx ?_ ?_ ?_
      · simpa [List.length_nil,hclock] using hd
      · simpa [List.length_nil,hclock] using hc
      · rw [List.length_nil,hclock]
        simpa [Nat.mul_comm,Nat.add_assoc] using hh
    have hcomp := walk_append hsingle (ih (by omega))
    simpa [qWord,Nat.add_assoc] using hcomp

/-- Recover the selected h-bit word and predecessor from a midpoint,
    using only the original queue's fixed target digits. -/
def qCode (n s Q : Nat) : Nat → Nat → Nat × Nat
  | 0,c => (0,c)
  | k+1,c =>
    let F := n+(s+k)+3
    let z := 2*c+qTarget Q k
    let r := qCode n s Q k (z%F)
    (r.1+2^k*(z/F),r.2)

theorem qcode_exact (n s Q a k R c : Nat) (ha : a<n+s+3)
    (hk : k≤n) (he : QExtend n s Q a k R c) :
    (qCode n s Q k c).2=a ∧ R=(Q+total n*(qCode n s Q k c).1)/2^k := by
  induction he with
  | nil => simp [qCode]
  | step k R c x d he hx hh ih =>
    have hc := qextend_carry_lt n s Q a k R c ha he
    have hy : R%2=qTarget Q k := by
      simpa [qTarget] using qtarget_shift n s Q a k R c 0 he (by omega)
    rw [hy] at hh
    obtain ⟨hp,hd⟩ := inverse_digit (n+(s+k)+3) c x d (qTarget Q k) (by omega) (by omega) hh
    obtain ⟨hi,hr⟩ := ih (by omega)
    simp only [qCode,hp,hd,hi,true_and]
    rw [hr,Nat.pow_succ,←Nat.div_div_eq_div_mul]
    have hEq : Q+total n*((qCode n s Q k c).1+2^k*x)=
        (Q+total n*(qCode n s Q k c).1)+2^k*(total n*x) := by
      rw [Nat.mul_add]; ac_rfl
    rw [hEq,Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]

def QLive (n s h : Nat) (ps : List QPrefix) (mids : Nat → List Nat) : Prop :=
  ∀ Q a, (Q,a)∈ps → ∀ z c,
    Walk (n+(s+h)+3+(n-h)) z (qWord Q h (n-h)) c → c∈mids Q

theorem qlive_of_jump (n s h : Nat) (ps : List QPrefix)
    (parts : Nat → List (List Nat)) (tails ends mids : Nat → List Nat)
    (hflat : ∀ Q a, (Q,a)∈ps → (parts Q).flatten++tails Q=qWord Q h (n-h))
    (hfit : ∀ Q a, (Q,a)∈ps → Fitted (n+(s+h)+3) (parts Q))
    (hjump : ∀ Q a, (Q,a)∈ps → JumpCover (n+(s+h)+3+(n-h)) (tails Q) (ends Q))
    (hcontains : ∀ Q a, (Q,a)∈ps → ∀ c,
      c∈blockFold (n+(s+h)+3) (parts Q) (ends Q) → c∈mids Q) :
    QLive n s h ps mids := by
  intro Q a hp z c hw
  have hf := hflat Q a hp
  have hl : (parts Q).flatten.length+(tails Q).length=n-h := by
    have he := congrArg List.length hf
    simpa using he
  have hb : ∀ y∈(parts Q).flatten++tails Q,y≤1 := by
    rw [hf]
    exact qWord_bits Q h (n-h)
  have hw' : Walk (n+(s+h)+3+(n-h)) z ((parts Q).flatten++tails Q) c := by
    rw [hf]; exact hw
  exact hcontains Q a hp c (walk_mem_prefix_live _ _ _ _ _ _ _ (by omega)
    hb (hfit Q a hp) (hjump Q a hp) hw')

def qRecoverMidpoints (n s h : Nat) (ps : List QPrefix) (mids : Nat → List Nat) : List QPrefix :=
  ps.flatMap fun p => (mids p.1).filterMap fun c =>
    let r := qCode n s p.1 h c
    if r.2=p.2 then some ((p.1+total n*r.1)/2^h,c) else none

theorem qmidpoint_cover_of_live (n s h : Nat) (ps : List QPrefix)
    (mids : Nat → List Nat) (hhn : h≤n)
    (hbound : ∀ p∈ps,p.2<n+s+3) (hLive : QLive n s h ps mids) :
    QMidpointCover n s h ps (qRecoverMidpoints n s h ps mids) := by
  intro Q a R c hp hpre htail
  obtain ⟨S,d,hsuf⟩ := htail
  have ha := hbound (Q,a) hp
  have hc := qextend_carry_lt n s Q a h R c ha hpre
  have hw := qextend_walk n (s+h) R c (n-h) S d (by omega) (by omega) hsuf
  rw [qword_shift n s Q a h R c (n-h) hpre (by omega)] at hw
  have hm := hLive Q a hp d c hw
  obtain ⟨hr,hR⟩ := qcode_exact n s Q a h R c ha hhn hpre
  unfold qRecoverMidpoints
  apply List.mem_flatMap.mpr
  refine ⟨(Q,a),hp,?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨c,hm,?_⟩
  simp only [hr,ite_true,Option.some.injEq,Prod.mk.injEq,and_true]
  exact hR.symm

theorem qcert_from_live (n K s h : Nat) (ps qs : List QPrefix)
    (mids : Nat → List Nat) (hn : 1≤n) (heven : n%2=0)
    (hs : 1≤s) (hhn : h≤n)
    (hbound : ∀ p∈ps,p.2<n+s+3) (hc : QHalfCert n K s ps)
    (hLive : QLive n s h ps mids)
    (hcontains : ∀ p∈qRecoverMidpoints n s h ps mids,p∈qs)
    (hg : ∀ p∈ps,QueueMargin n K s h p.1) :
    QHalfCert n K (s+h) qs := by
  apply qcert_next n K s h ps qs hn heven hs hhn hc _ hg
  intro Q a R c hp hpre htail
  exact hcontains (R,c) (qmidpoint_cover_of_live n s h ps mids hhn hbound hLive Q a R c hp hpre htail)

#print axioms qextend_word
#print axioms qtarget_shift
#print axioms qword_shift
#print axioms qextend_walk
#print axioms qcode_exact
#print axioms qlive_of_jump
#print axioms qmidpoint_cover_of_live
#print axioms qcert_from_live
end BB6.Agent9CompactMidpoint
