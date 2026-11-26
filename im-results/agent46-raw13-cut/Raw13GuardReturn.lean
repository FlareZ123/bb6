import Raw13RootOverflow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13GuardReturn
open BB6.Agent46Raw13RightCounter
open BB6.Agent46Raw13CounterBudget
open BB6.Agent46Raw13DrainCore
open BB6.Agent46Raw13DrainAll
open BB6.Agent46Raw13RootOverflow
open BB6.Agent46Raw13TapeValue (F Reach reach_trans path_reach)
open BB6.Agent46Raw13CoupledJump (firstRule)

def V := zeros 9 ++ [true]

def digits : Nat → Nat → List Bool
  | 0,_ => []
  | n+1,x => (x%2==1)::digits n (x/2)

theorem digits_len (n x : Nat) : (digits n x).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [digits,ih]

theorem encode_digits (n x : Nat) : encode n x = encBits (digits n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [encode,digits,encBits,ih]

theorem digits_high (k x : Nat) (hx : x<2^k) :
    digits (k+3) (x+7*2^k)=digits k x++[true,true,true] := by
  induction k generalizing x with
  | zero =>
    have : x=0 := by simpa using hx
    subst x
    rfl
  | succ k ih =>
    rw [Nat.pow_succ] at hx ⊢
    have h1 : x/2<2^k := by omega
    have h2 : (x+7*(2^k*2))/2=x/2+7*2^k := by omega
    have h3 : (x+7*(2^k*2))%2=x%2 := by omega
    change ( (x+7*(2^k*2))%2==1)::digits (k+3) ((x+7*(2^k*2))/2) = _
    rw [h2,h3,ih _ h1]
    rfl

theorem zeros_cap (n : Nat) : caps (zeros (3*n))=⟨2^n-1,2^n-1,2^n-1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,zeros_add 3 (3*n)]
    change (let p := caps (zeros (3*n)); Caps.mk (1+2*p.a) (1+2*p.b) (1+2*p.c)) = _
    rw [ih,Nat.pow_succ]
    have h := Nat.two_pow_pos n
    simp only [Caps.mk.injEq]
    omega

theorem entryBudget (p : Nat) : enough (zeros 2++true::zeros (3*p)) (2^(p+1)-2) := by
  change enough (false::false::true::zeros (3*p)) _
  unfold enough
  simp only [caps, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self, Nat.zero_add]
  rw [zeros_cap,Nat.pow_succ]
  simp only
  have h := Nat.two_pow_pos p
  omega

theorem zeroCount_le (xs : List Bool) : zeroCount xs≤xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp [zeroCount] <;> omega

theorem cost_bound (xs : List Bool) (K p : Nat) (hl : xs.length=K) (hp : K≤p) :
    cost (zeroCount xs)≤2^(p+1)-2 := by
  by_cases h : zeroCount xs=0
  · simp [cost,h]
  have hz := zeroCount_le xs
  have hpow : 2^(zeroCount xs)≤2^p := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 := two_le_pow (zeroCount xs) (by omega)
  simp only [cost,h,ite_false,Nat.pow_succ]
  omega

theorem drainEntry (p : Nat) (bs : List Bool) :
    Reach (F (zeros 4++true::true::false::false::false::encBits bs) (zeros (3*(p+1))++V))
      (D 1 bs ((zeros 2++true::zeros (3*p))++V)) := by
  have h1 := path_reach (firstRule 0 ([false,false,false,true,true,false,false,false]++encBits bs) (zeros (3*(p+1))++V))
  rw [show 3*(p+1)=3+3*p by omega,zeros_add 3 (3*p),List.append_assoc] at h1
  change Reach (F (zeros 4++true::true::false::false::false::encBits bs) (zeros 3++(zeros (3*p)++V)))
    (F (ones 6++oneBlocks 1++true::true::false::false::false::encBits bs) (zeros (3*p)++V)) at h1
  have h2 := mixedStep 3 0 ([false,false]++encBits bs) (zeros (3*p)++V)
  change Reach (F (ones 6++oneBlocks 1++true::true::false::false::false::encBits bs) (zeros (3*p)++V))
    (D 1 bs ((zeros 2++true::zeros (3*p))++V)) at h2
  rw [← List.append_assoc,← zeros_add,show 3+3*p=3*(p+1) by omega] at h1
  exact reach_trans h1 h2

theorem ready (K p low : Nat) (hp : K≤p) (hlow : low<2^K) :
    ∃ Q, Reach (F (zeros 4++true::encode (K+4) (2*(low+7*2^K)+1)) (zeros (3*(p+4))++[true]))
      (F [true] ([true,true,true]++Q++V)) := by
  let xs := digits K low
  have henc : encode (K+4) (2*(low+7*2^K)+1) = true::false::false::false::encBits (xs++[true,true,true]) := by
    rw [show K+4=(K+3)+1 by omega,encode_odd _ _ (by omega),show (2*(low+7*2^K)+1)/2=low+7*2^K by omega,encode_digits,digits_high K low hlow]
  have hW : zeros (3*(p+4))++[true]=zeros (3*(p+1))++V := by
    rw [V,← List.append_assoc,← zeros_add]; congr 2 <;> omega
  rw [henc,hW]
  have h1 := drainEntry p (xs++[true,true,true])
  obtain ⟨Q,h2⟩ := finishDrain 1 xs (zeros 2++true::zeros (3*p)) V (enough_mono (entryBudget p) (cost_bound xs K p (digits_len _ _) hp))
  exact ⟨true::Q,reach_trans h1 h2⟩


theorem word_concat (ts us : List Triple) (R : List Bool) : word (ts++us) R=word ts (word us R) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [word,ih]

theorem value_append (ts us : List Triple) : value (ts++us)=value ts+2^ts.length*value us := by
  induction ts with
  | nil => simp [value]
  | cons t ts ih => simp [value,ih,Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc]

theorem ys (K a : Nat) (ha : 0<a) (hb : a≤2^K) :
    let y := 2^(K+4)-(2*a-1)
    y=2*(2^K-a+7*2^K)+1 ∧ 2*y<2^(K+4+1) := by
  simp only [Nat.pow_add]
  omega

theorem returnSplit (ts : List Triple) (R : List Bool) (hr : R.length<3) :
    ∃ Q, Reach (F [true] (word (⟨true,true,true⟩::ts) (R++V))) (F [true] ([true,true,true]++Q++V)) := by
  let k := ts.length
  let a := value ts+1
  have ha : 0<a := by dsimp [a]; omega
  have hb : a≤2^k := by dsimp [a,k]; have h := value_lt ts; omega
  have hv : value (⟨true,true,true⟩::ts)=2*a-1 := by simp [value,a]; omega
  have hl : (⟨true,true,true⟩::ts : List Triple).length=k+1 := rfl
  cases R with
  | nil =>
    let us := (⟨true,true,true⟩::ts)++[zeroTriple,zeroTriple,zeroTriple]
    have hw : word us [true]=word (⟨true,true,true⟩::ts) ([]++V) := by rw [word_concat]; rfl
    have hu : us.length=k+4 := by simp [us,k]
    have huv : value us=2*a-1 := by rw [show us=(⟨true,true,true⟩::ts)++[zeroTriple,zeroTriple,zeroTriple] from rfl,value_append,hv]; simp [value,zeroTriple]
    obtain ⟨hy,hbound⟩ := ys k a ha hb
    have h1 := rootShort (k+4) us [true] (by decide) (by omega) (by rw [hu,huv]; exact hbound)
    rw [hw,hu,huv,hy] at h1
    obtain ⟨Q,h2⟩ := ready k k (2^k-a) (by omega) (by omega)
    exact ⟨Q,reach_trans h1 h2⟩
  | cons b R => cases R with
    | nil =>
      let us := (⟨true,true,true⟩::ts)++[⟨b,false,false⟩,zeroTriple,zeroTriple]
      have hw : word us [false,true]=word (⟨true,true,true⟩::ts) ([b]++V) := by rw [word_concat]; rfl
      have hu : us.length=k+4 := by simp [us,k]
      have huv : value us=2*a-1 := by rw [show us=(⟨true,true,true⟩::ts)++[⟨b,false,false⟩,zeroTriple,zeroTriple] from rfl,value_append,hv]; simp [value,zeroTriple]
      have hb' : a≤2^(k+1) := by rw [Nat.pow_succ]; omega
      obtain ⟨hy,hbound⟩ := ys (k+1) a ha hb'
      have h1 := rootLong (k+1+4) us [false,true] (by decide) (by omega) (by rw [hu,huv]; exact hbound)
      rw [hw,hu,huv,show k+4+1=k+1+4 by omega,hy] at h1
      obtain ⟨Q,h2⟩ := ready (k+1) (k+1) (2^(k+1)-a) (by omega) (by omega)
      exact ⟨Q,reach_trans h1 h2⟩
    | cons c R => cases R with
      | nil =>
        let us := (⟨true,true,true⟩::ts)++[⟨b,c,false⟩,zeroTriple,zeroTriple,lastTriple]
        have hw : word us []=word (⟨true,true,true⟩::ts) ([b,c]++V) := by rw [word_concat]; rfl
        have hu : us.length=k+5 := by simp [us,k]
        have huv : value us=2*a-1+2^(k+4) := by
          rw [show us=(⟨true,true,true⟩::ts)++[⟨b,c,false⟩,zeroTriple,zeroTriple,lastTriple] from rfl,value_append,hv,hl]
          rw [show value [⟨b,c,false⟩,zeroTriple,zeroTriple,lastTriple]=8 by rfl]; simp only [Nat.pow_add]; omega
        have hsub : 2^us.length-value us=2^(k+4)-(2*a-1) := by
          rw [hu,huv,show k+5=(k+4)+1 by omega,Nat.pow_succ]; omega
        obtain ⟨hy,hbound⟩ := ys k a ha hb
        have h1 := rootShort (k+4) us [] (by decide) (by omega) (by rw [hsub]; exact hbound)
        rw [hw,hsub,hy,hu] at h1
        obtain ⟨Q,h2⟩ := ready k (k+1) (2^k-a) (by omega) (by omega)
        exact ⟨Q,reach_trans h1 h2⟩
      | cons d R => simp at hr; omega

theorem guardReturn (X : List Bool) :
    ∃ Q, Reach (F [true] ([true,true,true]++X++V)) (F [true] ([true,true,true]++Q++V)) := by
  obtain ⟨Q,h⟩ := returnSplit (split X).1 (split X).2 (split_short X)
  rw [word_append] at h
  change Reach (F [true] ([true,true,true]++word (split X).1 (split X).2++V)) _ at h
  rw [word_split] at h
  exact ⟨Q,h⟩

#print axioms guardReturn
end BB6.Agent46Raw13GuardReturn
