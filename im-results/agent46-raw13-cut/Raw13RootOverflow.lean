import Raw13DrainAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13RootOverflow
open BB6.Agent46Raw13RightCounter
open BB6.Agent46Raw13CounterBudget
open BB6.Agent46Raw13DrainCore
open BB6.Agent46Raw13CoupledDrain (ones_add)
open BB6.Agent46Raw13TapeValue (F Reach reach_trans path_reach F_pad)
open BB6.Agent46Raw13CoupledJump (jump firstRule)

theorem maxRun (m x : Nat) (ts : List Triple) (R : List Bool)
    (hx : x+2*(2^ts.length-1-value ts)<2^m) :
    ∃ us : List Triple, us.length=ts.length ∧ value us=2^ts.length-1 ∧
      Steps (F (encode m x) (word ts R))
        (F (encode m (x+2*(2^ts.length-1-value ts))) (word us R)) := by
  let d := 2^ts.length-1-value ts
  have hv := value_lt ts
  have hs : (add ts d).isSome := by rw [add_spec]; dsimp [d]; omega
  cases e : add ts d with
  | none => simp [e] at hs
  | some us =>
    obtain ⟨hv',hl⟩ := add_value ts us d e
    refine ⟨us,hl,by dsimp [d] at hv'; omega,?_⟩
    by_cases hd : d=0
    · rw [hd,add_zero] at e; injection e with e; subst us
      exact Or.inl (by change F (encode m x) _ = F (encode m (x+2*d)) _; simp [hd])
    · have hr := path_reach (jump m x d [] R ts us (by omega) hx e)
      exact Or.inr (by simpa only [F, List.append_nil] using hr)

theorem scan_full (ts : List Triple) (R : List Bool) (hv : value ts=2^ts.length-1) :
    scan (true::word ts R) = (6*ts.length+(scan (true::R)).1,(scan (true::R)).2) := by
  induction ts with
  | nil => simp only [word,List.length_nil,Nat.mul_zero,Nat.zero_add]
  | cons t ts ih =>
    have hv' := value_lt ts
    simp only [value,List.length_cons,Nat.pow_succ] at hv
    obtain ⟨a,b,c⟩ := t
    cases c with
    | false => simp at hv; omega
    | true =>
      simp at hv
      have he : value ts=2^ts.length-1 := by omega
      simp only [word,scan,ih he,List.length_cons]
      congr 1 <;> omega

theorem fullCarry (m x : Nat) (ts : List Triple) (R : List Bool)
    (hx : x+1<2^m) (hv : value ts=2^ts.length-1) :
    Reach (F (encode m x) (word ts R))
      (F (ones (6*ts.length+(scan (true::R)).1)++encode m (x+1)) (scan (true::R)).2) := by
  obtain ⟨n,L,h1,h2⟩ := left_carry m x [] hx
  simp only [List.append_nil] at h1 h2
  have h := path_reach (firstRule n L (word ts R))
  change Reach (F _ _) (F (ones (scan (true::word ts R)).1++zeros (4*n)++true::L) (scan (true::word ts R)).2) at h
  rw [scan_full ts R hv,← h1,List.append_assoc,← h2] at h
  exact h

theorem scan_short (R : List Bool) (h : R.length≤1) : scan (true::R)=(3,[]) := by
  cases R with
  | nil => rfl
  | cons a R => cases R with
    | nil => rfl
    | cons b R => simp at h

theorem scan_long (R : List Bool) (h : R.length=2) : scan (true::R)=(6,[]) := by
  cases R with
  | nil => simp at h
  | cons a R => cases R with
    | nil => simp at h
    | cons b R => cases R with
      | nil => rfl
      | cons c R => simp at h

theorem shortOverflow (m y : Nat) (ts : List Triple) (R : List Bool)
    (hy : 0<y) (hx : 2*y<2^(m+1)) (hv : value ts=2^ts.length-1) (hR : R.length≤1) :
    Reach (F (encode (m+1) (2*y-1)) (word ts R))
      (F (zeros 4++true::encode m y) (zeros (3*ts.length)++[true])) := by
  have h1 := fullCarry (m+1) (2*y-1) ts R (by omega) hv
  rw [scan_short R hR,show 2*y-1+1=2*y by omega,encode_even m (2*y) (by omega),show 2*y/2=y by omega] at h1
  have h2 := mainPos (3*ts.length) 1 (encode m y) []
  have hl : ones (6*ts.length+3)++false::false::false::false::encode m y =
      ones (2*(3*ts.length+1))++oneBlocks 1++false::encode m y := by
    rw [show 6*ts.length+3=2*(3*ts.length+1)+1 by omega,ones_add,List.append_assoc]
    simp only [List.append_assoc]
    rfl
  rw [hl] at h1
  exact reach_trans h1 h2

theorem longOverflow (m x : Nat) (ts : List Triple) (R : List Bool)
    (hx : x+2<2^m) (hv : value ts=2^ts.length-1) (hR : R.length=2) :
    Reach (F (encode m x) (word ts R))
      (F (encode m (x+2)) (zeros (3*(ts.length+1)-1)++[true])) := by
  have h1 := fullCarry m x ts R (by omega) hv
  rw [scan_long R hR,show 6*ts.length+6=6*(ts.length+1) by omega] at h1
  have h2 := positiveCarry (ts.length+1) m (x+1) [] [] (by omega) (by omega)
  simp only [List.append_nil,show x+1+1=x+2 by omega] at h2
  exact reach_trans h1 h2

theorem startEncode (m : Nat) (W : List Bool) : F (encode (m+1) 1) W = F [true] W := by
  rw [encode_one]
  have he : true::false::false::false::zeros (4*m) = [true]++zeros (4*m+3) := by
    rw [show 4*m+3=3+4*m by omega,zeros_add 3 (4*m)]; rfl
  rw [he]
  exact F_pad [true] W (4*m+3)

theorem rootShort (m : Nat) (ts : List Triple) (R : List Bool)
    (hR : R.length≤1) (hv : 0<value ts) (hx : 2*(2^ts.length-value ts)<2^(m+1)) :
    Reach (F [true] (word ts R))
      (F (zeros 4++true::encode m (2^ts.length-value ts)) (zeros (3*ts.length)++[true])) := by
  let y := 2^ts.length-value ts
  have ht := value_lt ts
  have hy : 0<y := by dsimp [y]; omega
  have he : 1+2*(2^ts.length-1-value ts)=2*y-1 := by dsimp [y]; omega
  obtain ⟨us,hl,hv',h1⟩ := maxRun (m+1) 1 ts R (by omega)
  rw [startEncode,he] at h1
  have h2 := shortOverflow m y us R hy hx (by rw [hl]; exact hv') hR
  rw [hl] at h2
  exact steps_reach h1 h2

def zeroTriple : Triple := ⟨false,false,false⟩
def lastTriple : Triple := ⟨false,false,true⟩
def extendTriples (n : Nat) : List Triple := List.replicate n zeroTriple++[lastTriple]

theorem extend_len (n : Nat) : (extendTriples n).length=n+1 := by simp [extendTriples]
theorem extend_value (n : Nat) : value (extendTriples n)=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 0+2*value (extendTriples n)=2^(n+1)
    rw [ih,Nat.pow_succ]; omega

theorem extend_word (n : Nat) : word (extendTriples n) []=zeros (3*(n+1)-1)++[true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false::false::false::word (extendTriples n) [] = _
    rw [ih,show 3*(n+1+1)-1=3+(3*(n+1)-1) by omega,zeros_add 3 (3*(n+1)-1)]
    rfl

theorem rootLong (m : Nat) (ts : List Triple) (R : List Bool)
    (hR : R.length=2) (hv : 0<value ts) (hx : 2*(2^(ts.length+1)-value ts)<2^(m+1)) :
    Reach (F [true] (word ts R))
      (F (zeros 4++true::encode m (2^(ts.length+1)-value ts)) (zeros (3*(ts.length+1))++[true])) := by
  let n := ts.length
  let v := value ts
  let x := 1+2*(2^n-1-v)
  let y := 2^(n+1)-v
  have ht := value_lt ts
  change v<2^n at ht
  change 2*y<2^(m+1) at hx
  have hp : 2^(n+1)=2*2^n := by rw [Nat.pow_succ,Nat.mul_comm]
  have hxy : x+2≤2*y := by dsimp [x,y]; omega
  obtain ⟨us,hl,hv',h1⟩ := maxRun (m+1) 1 ts R (by change x<2^(m+1); omega)
  rw [startEncode] at h1
  change Steps (F [true] (word ts R)) (F (encode (m+1) x) (word us R)) at h1
  have h2 := longOverflow (m+1) x us R (by omega) (by rw [hl]; exact hv') hR
  rw [hl,← extend_word] at h2
  have h3bound : x+2+2*(2^(extendTriples n).length-1-value (extendTriples n))=2*y-1 := by
    rw [extend_len,extend_value]; dsimp [x,y]; omega
  obtain ⟨ws,hw,hv'',h3⟩ := maxRun (m+1) (x+2) (extendTriples n) [] (by rw [h3bound]; omega)
  rw [h3bound] at h3
  have h4 := shortOverflow m y ws [] (by omega) hx (by rw [hw]; exact hv'') (by decide)
  rw [hw,extend_len] at h4
  exact reach_trans (reach_steps (steps_reach h1 h2) h3) h4

#print axioms rootShort
#print axioms rootLong
end BB6.Agent46Raw13RootOverflow
