import FatalFamilyWindow

namespace BB6.Agent41FatalInverse

def ow (k t : Nat) : Nat := 2*(ordinary k t).1+(ordinary k t).2

def bw (k t : Nat) : Nat := (balanced k t).1+2*(balanced k t).2

def leftIndex (k t : Nat) : Int := 3*(t:Int)-1-ow k t

def rightIndex (k t : Nat) : Int := 3*(t:Int)+bw k t+1

private theorem ow_step (k : Nat) : ∀ t, ow k (t+1)≤ow k t+2 := by
  induction k with
  | zero => intro t; simp [ow,ordinary]
  | succ k ih =>
    intro t
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    have hh := ih (t/3)
    rcases hr with hr|hr|hr
    · have h1 : (t+1)%3=1 := by omega
      have h2 : (t+1)/3=t/3 := by omega
      simp [ow,ordinary,hr,h1,h2] <;> omega
    · have h1 : (t+1)%3=2 := by omega
      have h2 : (t+1)/3=t/3 := by omega
      simp [ow,ordinary,hr,h1,h2] <;> omega
    · have h1 : (t+1)%3=0 := by omega
      have h2 : (t+1)/3=t/3+1 := by omega
      simp [ow,ordinary,hr,h1,h2] at * <;> omega

private theorem bw_step (k : Nat) : ∀ t, bw k t≤bw k (t+1)+2 := by
  induction k with
  | zero => intro t; simp [bw,balanced]
  | succ k ih =>
    intro t
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    have hh := ih ((t+1)/3)
    rcases hr with hr|hr|hr
    · have h1 : (t+1)%3=1 := by omega
      have h2 : (t+1+1)/3=(t+1)/3 := by omega
      simp [bw,balanced,hr,h1,h2] <;> omega
    · have h1 : (t+1)%3=2 := by omega
      have h2 : (t+1+1)/3=(t+1)/3+1 := by omega
      simp [bw,balanced,hr,h1,h2] at * <;> omega
    · have h1 : (t+1)%3=0 := by omega
      have h2 : (t+1+1)/3=(t+1)/3 := by omega
      simp [bw,balanced,hr,h1,h2] <;> omega

theorem leftIndex_step (k t : Nat) : leftIndex k t < leftIndex k (t+1) := by
  have h := ow_step k t
  unfold leftIndex
  omega

theorem rightIndex_step (k t : Nat) : rightIndex k t < rightIndex k (t+1) := by
  have h := bw_step k t
  unfold rightIndex
  omega

private theorem strict_of_step (f : Nat → Int) (h : ∀ t, f t<f (t+1)) (a b : Nat) (hab : a<b) : f a<f b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hh : a=b
    · subst a; exact h b
    · have hab' : a<b := by omega
      exact Int.lt_trans (ih hab') (h b)

private theorem gap_excluded (f : Nat → Int) (h : ∀ t, f t<f (t+1)) (s : Nat) (p : Int)
    (hlo : f s<p) (hhi : p<f (s+1)) : ∀ t, f t≠p := by
  intro t he
  by_cases hlt : t<s
  · have h1 := strict_of_step f h t s hlt; omega
  · by_cases hh : t=s
    · subst t; omega
    · by_cases hh' : t=s+1
      · subst t; omega
      · have h1 := strict_of_step f h (s+1) t (by omega); omega

private theorem ordinary_shift (n r a : Nat) : ordinary (n+r) (a*3^r)=ordinary n a := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.pow_succ,←Nat.mul_assoc]
    rw [show n+(r+1)=n+r+1 by omega,ordinary]
    have hh : (a*3^r*3)/3=a*3^r := by omega
    have hm : (a*3^r*3)%3=0 := by omega
    simp [hh,hm,ih]

private theorem balanced_shift (n r a : Nat) : balanced (n+r) (a*3^r)=balanced n a := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.pow_succ,←Nat.mul_assoc]
    rw [show n+(r+1)=n+r+1 by omega,balanced]
    have hh : (a*3^r*3+1)/3=a*3^r := by omega
    have hm : (a*3^r*3)%3=0 := by omega
    simp [hh,hm,ih]

private theorem ordinary_two (n : Nat) (hn : 1≤n) : ordinary n 2=(0,1) := by
  have hz : ∀ n, ordinary n 0=(0,0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [ordinary,ih]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp [ordinary,hz]

private theorem balanced_two (n : Nat) (hn : 2≤n) : balanced n 2=(1,1) := by
  have hz : ∀ n, balanced n 0=(0,0) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [balanced,ih]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  simp [balanced,hz]

private theorem ordinary_near_two (k r : Nat) (hr : 1≤r) (hk : r+1≤k) :
    ordinary k (2*3^r+1)=(1,1) ∧ ordinary k (2*3^r+2)=(0,2) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hn : 1≤k-r := by omega
  have hbase : ordinary k (2*3^r)=(0,1) := by
    rw [show k=(k-r)+r by omega,ordinary_shift]
    exact ordinary_two _ hn
  have he1 : 2*3^(r+1)+1=2*3^r*3+1 := by rw [Nat.pow_succ,←Nat.mul_assoc]
  have he2 : 2*3^(r+1)+2=2*3^r*3+2 := by rw [Nat.pow_succ,←Nat.mul_assoc]
  rw [he1,he2]
  simp [ordinary,show (2*3^r*3+1)/3=2*3^r by omega,
    show (2*3^r*3+2)/3=2*3^r by omega,
    show (2*3^r*3+1)%3=1 by omega,show (2*3^r*3+2)%3=2 by omega,hbase]

private theorem balanced_near_two (k r : Nat) (hr : 1≤r) (hk : r+3≤k) :
    balanced k (2*3^(r+1)-3)=(1,2) ∧ balanced k (2*3^(r+1)-2)=(2,2) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hn : 2≤k-r := by omega
  have hbase : balanced k (2*3^r)=(1,1) := by
    rw [show k=(k-r)+r by omega,balanced_shift]
    exact balanced_two _ hn
  have hp : 0<3^r := Nat.pow_pos (by decide)
  have he1 : 2*3^(r+1+1)-3=3*(3*(2*3^r)-1) := by
    rw [Nat.pow_succ,Nat.pow_succ]; omega
  have he2 : 2*3^(r+1+1)-2=3*(3*(2*3^r)-1)+1 := by
    rw [Nat.pow_succ,Nat.pow_succ]; omega
  have hq : balanced (k+1) (3*(2*3^r)-1)=(1,2) := by
    rw [balanced]
    simp [show (3*(2*3^r)-1+1)/3=2*3^r by omega,
      show (3*(2*3^r)-1)%3=2 by omega,hbase]
  rw [he1,he2]
  constructor <;> rw [balanced] <;>
    simp [show (3*(3*(2*3^r)-1)+1)/3=3*(2*3^r)-1 by omega,
    show (3*(3*(2*3^r)-1)+1+1)/3=3*(2*3^r)-1 by omega,
    show (3*(3*(2*3^r)-1))%3=0 by omega,
    show (3*(3*(2*3^r)-1)+1)%3=1 by omega,hq]

/-- For every r>=1, the even exponent p=6*3^r misses both inverse digit gates. -/
theorem power_three_gates_excluded (r : Nat) (hr : 1≤r) :
    let k := 6*3^r-1
    (∀ t, ¬ LeftParameter k t) ∧ (∀ t, ¬ RightParameter k t) := by
  dsimp only
  let p := 6*3^r
  let k := p-1
  have hpow_all : ∀ r : Nat, r+1≤3^r := by
    intro r
    induction r with
    | zero => decide
    | succ r ih => rw [Nat.pow_succ]; omega
  have hpow := hpow_all r
  have hp : p=2*3^(r+1) := by dsimp [p]; rw [Nat.pow_succ]; omega
  have hk : r+3≤k := by dsimp [k,p]; omega
  have hpk : k+1=p := by dsimp [k,p]; omega
  obtain ⟨hL1,hL2⟩ := ordinary_near_two k r hr (by omega)
  obtain ⟨hR1,hR2⟩ := balanced_near_two k r hr hk
  have h1 : leftIndex k (2*3^r+1) < (p:Int) := by
    unfold leftIndex ow; rw [hL1]; dsimp [p]; omega
  have h2 : (p:Int) < leftIndex k (2*3^r+1+1) := by
    rw [show 2*3^r+1+1=2*3^r+2 by omega]
    unfold leftIndex ow; rw [hL2]; dsimp [p]; omega
  have h3 : rightIndex k (p-3) < 3*(p:Int) := by
    rw [hp]
    unfold rightIndex bw
    rw [hR1]
    omega
  have h4 : 3*(p:Int) < rightIndex k (p-3+1) := by
    have he : p-3+1=p-2 := by dsimp [p]; omega
    rw [he,hp]
    unfold rightIndex bw
    rw [hR2]
    omega
  have hl := gap_excluded (leftIndex k) (leftIndex_step k) _ _ h1 h2
  have hh := gap_excluded (rightIndex k) (rightIndex_step k) _ _ h3 h4
  change (∀ t, ¬ LeftParameter k t) ∧ (∀ t, ¬ RightParameter k t)
  constructor
  · intro t ht
    apply hl t
    unfold LeftParameter at ht
    unfold leftIndex ow
    omega
  · intro t ht
    apply hh t
    unfold RightParameter at ht
    unfold rightIndex bw
    omega

#print axioms leftIndex_step
#print axioms rightIndex_step
#print axioms power_three_gates_excluded
end BB6.Agent41FatalInverse
