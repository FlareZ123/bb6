import Init

namespace BB6.Agent32F418.RecoveryCore

/-- A nonempty low-first word of odd collision valuations, represented by their half-indices. -/
inductive Word where
  | last (r : Nat)
  | more (r : Nat) (t : Word)

namespace Word

def L : Word → Nat
  | last r => 2*r+2
  | more r t => 2*r+2+t.L

def U : Word → Nat
  | last _ => 1
  | more r t => 5*r+5+t.U

def e : Word → Nat
  | last r => 5*r+3
  | more _ t => t.e

def E (b : Word) := b.e+b.U+1

def D : Word → Nat
  | last r => 2^(2*r+2)
  | more r t => (2^(2*r+3)-1)*2^(5*r+3+t.U)+t.D

def C : Word → Nat
  | last r => (2^(2*r+3)-1)*2^(5*r+3)
  | more r t => (2^(2*r+3)-1)*2^(5*r+3+t.E)+t.C

def value : Word → Nat
  | last r => 2^(2*r+1)
  | more r t => 2^(2*r+1)*(2*t.value+1)

theorem L_ge (b : Word) : 2≤b.L := by cases b <;> simp [L] <;> omega
theorem U_ge (b : Word) : 1≤b.U := by cases b <;> simp [U] <;> omega
theorem D_pos (b : Word) : 0<b.D := by
  induction b with
  | last r => exact Nat.two_pow_pos _
  | more r t ih => simp [D]; omega

theorem value_ge (b : Word) : 2^(b.L-1)≤b.value := by
  induction b with
  | last r => simp [L,value]
  | more r t ih =>
    have h := L_ge t
    simp only [L,value]
    rw [show 2*r+2+t.L-1=(2*r+1)+1+(t.L-1) by omega,Nat.pow_add,Nat.pow_succ,Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    omega

theorem width {b : Word} {W : Nat} (h : b.value<2^W) : b.L≤W := by
  have h1 := value_ge b
  have h2 := L_ge b
  have h3 := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (show 2^(b.L-1)<2^W by omega)
  omega

theorem E_length (b : Word) : 2*b.E=5*b.L := by
  induction b with
  | last r => simp [E,e,U,L]; omega
  | more r t ih => simp [E,e,U,L] at *; omega

theorem correction_factor (b : Word) : b.C=2^b.e*(2*b.D-1) := by
  induction b with
  | last r =>
    simp only [C,e,D]
    rw [show 2*r+3=(2*r+2)+1 by omega,Nat.pow_succ,Nat.mul_comm (2^(2*r+2)) 2,Nat.mul_comm]
  | more r t ih =>
    simp only [C,e,D]
    rw [ih]
    have hp : 2^(5*r+3+t.E)=2^t.e*(2*2^(5*r+3+t.U)) := by
      rw [show 5*r+3+t.E=t.e+(5*r+3+t.U)+1 by simp [E]; omega,Nat.pow_succ,Nat.pow_add]; ac_rfl
    rw [hp]
    have ht := D_pos t
    have hf : 2*((2^(2*r+3)-1)*2^(5*r+3+t.U)+t.D)-1 = 2*((2^(2*r+3)-1)*2^(5*r+3+t.U))+(2*t.D-1) := by omega
    rw [hf,Nat.mul_add]
    congr 1
    ac_rfl

theorem D_bounds (b : Word) : b.D≤2^(b.U+b.L-1) := by
  induction b with
  | last r => simp [D,U,L]
  | more r t ih =>
    let X := 2^(2*r+3)
    let K := 2^(5*r+3+t.U)
    let Y := 2^(t.L-2)
    have hy : 0<Y := Nat.two_pow_pos _
    have hx : 0<X := Nat.two_pow_pos _
    have hL := L_ge t
    have hK : t.D<Y*K := by
      apply Nat.lt_of_le_of_lt ih
      dsimp [Y,K]
      rw [←Nat.pow_add]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    have hXY : X-1+Y≤X*Y := by
      have h1 : X-1≤(X-1)*Y := by simpa using Nat.mul_le_mul_left (X-1) hy
      have h2 : X*Y=(X-1)*Y+Y := by
        calc
          X*Y=(X-1+1)*Y := by congr 1; omega
          _=(X-1)*Y+Y := by rw [Nat.add_mul,Nat.one_mul]
      omega
    have hsum : (X-1)*K+t.D<(X-1+Y)*K := by rw [Nat.add_mul]; omega
    have hlt := Nat.lt_of_lt_of_le hsum (Nat.mul_le_mul_right K hXY)
    have hpow : X*Y*K=2^((more r t).U+(more r t).L-3) := by
      dsimp [X,Y,K]
      rw [←Nat.pow_add,←Nat.pow_add]
      congr 1
      simp [U,L]; omega
    have h' : (more r t).D<2^((more r t).U+(more r t).L-3) := by rw [←hpow]; exact hlt
    exact Nat.le_trans (Nat.le_of_lt h') (Nat.pow_le_pow_right (by decide) (by omega))

theorem D_more_strict (r : Nat) (t : Word) : (more r t).D<2^((more r t).U+(more r t).L-3) := by
  let X := 2^(2*r+3)
  let K := 2^(5*r+3+t.U)
  let Y := 2^(t.L-2)
  have hy : 0<Y := Nat.two_pow_pos _
  have hx : 0<X := Nat.two_pow_pos _
  have hL := L_ge t
  have hK : t.D<Y*K := by
    apply Nat.lt_of_le_of_lt (D_bounds t)
    dsimp [Y,K]
    rw [←Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hXY : X-1+Y≤X*Y := by
    have h1 : X-1≤(X-1)*Y := by simpa using Nat.mul_le_mul_left (X-1) hy
    have h2 : X*Y=(X-1)*Y+Y := by
      calc
        X*Y=(X-1+1)*Y := by congr 1; omega
        _=(X-1)*Y+Y := by rw [Nat.add_mul,Nat.one_mul]
    omega
  have hsum : (X-1)*K+t.D<(X-1+Y)*K := by rw [Nat.add_mul]; omega
  have hlt := Nat.lt_of_lt_of_le hsum (Nat.mul_le_mul_right K hXY)
  have hpow : X*Y*K=2^((more r t).U+(more r t).L-3) := by
    dsimp [X,Y,K]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    simp [U,L]; omega
  rw [←hpow]
  exact hlt

def Q (b : Word) (W : Nat) := 2^(W+b.U)-b.D

theorem Q_pos {b : Word} {W : Nat} (h : b.L≤W) : 0<b.Q W := by
  have hd := D_bounds b
  have hu := U_ge b
  have hb : 2^(b.U+b.L-1)<2^(W+b.U) := Nat.pow_lt_pow_right (by decide) (by omega)
  unfold Q; omega

theorem gap_factor {b : Word} {W : Nat} (h : b.L≤W) :
    2^(W+b.E)-b.C=2^b.e*(2*b.Q W+1) := by
  have hd := D_bounds b
  have hu := U_ge b
  have hb : 2^(b.U+b.L-1)≤2^(W+b.U) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp := D_pos b
  rw [correction_factor,show W+b.E=b.e+(W+b.U)+1 by simp [E]; omega,Nat.pow_succ,Nat.pow_add]
  rw [show 2^b.e*2^(W+b.U)*2=2^b.e*(2*2^(W+b.U)) by ac_rfl,←Nat.mul_sub]
  congr 1
  unfold Q
  omega

theorem Q_has_even {b : Word} {W : Nat} (h : b.L≤W) :
    ∃ i : Nat, i%2=0 ∧ (b.Q W).testBit i=true := by
  cases b with
  | last r =>
    let k := 2*r+2
    have hk : k≤W := h
    have he : 2^(W+1)=2^k*2^(W+1-k) := by rw [←Nat.pow_add]; congr 1; omega
    have hh : 0<W+1-k := by omega
    have hp : 2^(W+1-k)%2=0 := by
      rw [show W+1-k=(W+1-k-1)+1 by omega,Nat.pow_succ]; omega
    refine ⟨k,by dsimp [k]; omega,?_⟩
    change (2^(W+1)-2^k).testBit k=true
    rw [he,show 2^k*2^(W+1-k)-2^k=2^k*(2^(W+1-k)-1) by rw [Nat.mul_sub,Nat.mul_one],Nat.testBit_eq_decide_div_mod_eq,Nat.mul_comm,Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    have hpos := Nat.two_pow_pos (W+1-k)
    simp only [decide_eq_true_eq]
    omega
  | more r t =>
    let H := W+(more r t).U
    have hh : 3≤H := by have := L_ge (more r t); have := U_ge (more r t); omega
    have hd : (more r t).D<2^(H-3) := Nat.lt_of_lt_of_le (D_more_strict r t) (Nat.pow_le_pow_right (by decide) (by dsimp [H]; omega))
    have hp : 2^H=4*2^(H-2) := by rw [←Nat.pow_add (a:=2) (m:=2) (n:=H-2)]; congr 1; omega
    have hp' : 2^(H-3)≤2^(H-2) := Nat.pow_le_pow_right (by decide) (by omega)
    have hdpos := D_pos (more r t)
    have hl : 3*2^(H-2)≤(more r t).Q W := by unfold Q; change 3*2^(H-2)≤2^H-(more r t).D; omega
    have hu : (more r t).Q W<4*2^(H-2) := by unfold Q; change 2^H-(more r t).D<4*2^(H-2); omega
    have hdiv : (more r t).Q W/2^(H-2)=3 := Nat.div_eq_of_lt_le hl hu
    have hpow : 2^(H-2+1)=2*2^(H-2) := by rw [Nat.pow_succ,Nat.mul_comm]
    have hdiv' : (more r t).Q W/2^(H-2+1)=1 := by
      apply Nat.div_eq_of_lt_le
      · rw [hpow]; omega
      · rw [hpow]; omega
    by_cases he : (H-2)%2=0
    · exact ⟨H-2,he,by simp [Nat.testBit_eq_decide_div_mod_eq,hdiv]⟩
    · exact ⟨H-2+1,by omega,by simp [Nat.testBit_eq_decide_div_mod_eq,hdiv']⟩

#print axioms correction_factor
#print axioms gap_factor
#print axioms Q_has_even

end Word
end BB6.Agent32F418.RecoveryCore
