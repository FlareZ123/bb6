import ThreeAdicG2
namespace ThreeAdic

private theorem mod_sub_two (m a b x y : Nat) (hm : 0<m)
    (hx : x≤a) (hy : y≤b) (ha : a%m=b%m) (hc : x%m=y%m) :
    (a-x)%m=(b-y)%m := by
  apply mod_add_cancel m (a-x) (b-y) y hm
  have hstart : ((a-x)+y)%m=((a-x)+x)%m := by
    calc
     _ = ((a-x)%m+y%m)%m := Nat.add_mod _ _ _
     _ = ((a-x)%m+x%m)%m := by rw [←hc]
     _ = _ := (Nat.add_mod _ _ _).symm
  calc
    ((a-x)+y)%m = ((a-x)+x)%m := hstart
    _ = a%m := by rw [Nat.sub_add_cancel hx]
    _ = b%m := ha
    _ = ((b-y)+y)%m := by rw [Nat.sub_add_cancel hy]

theorem shift_two_power_multiple (e t k : Nat) :
    2^(t+(2*3^e)*k)%(3^(e+1))=2^t%(3^(e+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
       _ = 2^((t+(2*3^e)*k)+(2*3^e))%(3^(e+1)) := by
         simp only [Nat.mul_succ]
         congr 2 <;> omega
       _ = 2^(t+(2*3^e)*k)%(3^(e+1)) := shift_two_power e _
       _ = _ := ih

def N (c : Nat) : Nat := 4*2^c+c-10
def H0 (c : Nat) : Nat := (4*2^(N c)+13)-(8*2^c+c)

private theorem pow_growth_multiply (c : Nat) (hc : 2≤c) :
     8*2^c+c ≤ 4*2^(N c)+13 := by
  have hsmall := pow_two_growth c
  have hN : c+2 ≤ N c := by
    simp only [N]
    omega
  have hpow : 2^(c+2)≤2^(N c) := Nat.pow_le_pow_right (by omega) hN
  rw [Nat.pow_add] at hpow
  simp only [show 2^2=4 by decide] at hpow
  omega

private theorem N_shift (e c : Nat) (hc : 2≤c) :
    ∃ q, N (c+2*3^e)=N c + (2*3^e)*q := by
  let p := 2*3^e
  let M := 3^(e+1)
  let Q := 2^p/M
  have hp : 2^p=1+M*Q := by
    calc
      2^p = 2^p%M+M*(2^p/M) := (Nat.mod_add_div _ _).symm
      _ = 1+M*Q := by rw [power_period e]
  have hN0 : N c +10=4*2^c+c := by
    simp only [N]
    have hc2 : 10≤4*2^c+c := by
      have h := pow_two_growth c
      omega
    omega
  have hN1 : N (c+p)+10=4*2^(c+p)+(c+p) := by
    simp only [N]
    have hc2 : 10≤4*2^(c+p)+(c+p) := by
      have h := pow_two_growth (c+p)
      omega
    omega
  have hpow : 2^(c+p)=2^c*2^p := Nat.pow_add _ _ _
  have hring :
       4*(2^c*(1+M*Q))+(c+p) =
         (4*2^c+c)+p*(6*2^c*Q+1) := by
    dsimp [p,M]
    simp only [Nat.pow_succ]
    grind +ring
  refine ⟨6*2^c*Q+1,?_⟩
  change N (c+p)=N c+p*(6*2^c*Q+1)
  rw [hpow,hp] at hN1
  omega

private theorem H0_shift (e c : Nat) (hc : 2≤c) :
    (H0 (c+2*3^e)+2*3^e)%(3^(e+1))=H0 c%(3^(e+1)) := by
  let p := 2*3^e
  let M := 3^(e+1)
  obtain ⟨q,hN⟩ := N_shift e c hc
  have hpex : (2^(N (c+p)))%M=(2^(N c))%M := by
    rw [hN]
    exact shift_two_power_multiple e (N c) q
  have hpc : (2^(c+p))%M=(2^c)%M := shift_two_power e c
  have hA : (4*2^(N (c+p))+13)%M=(4*2^(N c)+13)%M := by
    have hm : (4*2^(N (c+p)))%M=(4*2^(N c))%M := by
      calc
       _ = (4%M*(2^(N (c+p))%M))%M := Nat.mul_mod _ _ _
       _ = (4%M*(2^(N c)%M))%M := by rw [hpex]
       _ = _ := (Nat.mul_mod _ _ _).symm
    calc
      _ = ((4*2^(N (c+p)))%M+13%M)%M := Nat.add_mod _ _ _
      _ = ((4*2^(N c))%M+13%M)%M := by rw [hm]
      _ = _ := (Nat.add_mod _ _ _).symm
  have hB : (8*2^(c+p)+c)%M=(8*2^c+c)%M := by
    have hm : (8*2^(c+p))%M=(8*2^c)%M := by
      calc
       _ = (8%M*(2^(c+p)%M))%M := Nat.mul_mod _ _ _
       _ = (8%M*(2^c)%M))%M := by rw [hpc]
       _ = _ := (Nat.mul_mod _ _ _).symm
    calc
      _ = ((8*2^(c+p))%M+c%M)%M := Nat.add_mod _ _ _
      _ = ((8*2^c)%M+c%M)%M := by rw [hm]
      _ = _ := (Nat.add_mod _ _ _).symm
  have hlow : (8*2^c+c)≤4*2^(N c)+13 := pow_growth_multiply c hc
  have hlp : (8*2^(c+p)+(c+p))≤4*2^(N (c+p))+13 :=
    pow_growth_multiply (c+p) (by omega)
  have hlow' : (8*2^(c+p)+c)≤4*2^(N (c+p))+13 := by omega
  have hbasic :
       ((4*2^(N (c+p))+13)-(8*2^(c+p)+c))%M=
       ((4*2^(N c)+13)-(8*2^c+c))%M :=
    mod_sub_two M _ _ _ _ (Nat.pow_pos (by omega)) hlow' hlow hA hB
  have hbal : H0 (c+p)+p=(4*2^(N (c+p))+13)-(8*2^(c+p)+c) := by
    dsimp [H0]
    omega
  change (H0 (c+p)+p)%M=H0 c%M
  rw [hbal]
  exact hbasic

theorem H0_all_residues (E r:Nat) :
    ∃ c, 2≤c ∧ c≤2+2*(3^E-1) ∧ H0 c%(3^E)=r%(3^E) := by
  have hshift : ∀ e n,
      (H0 ((n+2)+2*3^e)+2*3^e)%(3^(e+1))=H0 (n+2)%(3^(e+1)) := by
    intro e n
    exact H0_shift e (n+2) (by omega)
  have hs : ∀ e n,
      (H0 ((n+2*3^e)+2)+2*3^e)%(3^(e+1))=H0 (n+2)%(3^(e+1)) := by
    intro e n
    have heq : (n+2*3^e)+2=(n+2)+2*3^e := by omega
    rw [heq]
    exact hshift e n
  obtain ⟨n,hn0,hbound,hres⟩ :=
    all_residues (fun z => H0 (z+2)) 0 hs E r
  exact ⟨n+2,by omega,by omega,hres⟩

private theorem high_pow (c : Nat) (hc : 2≤c) :
    8*2^c ≤4*2^(N c) := by
  have hN : c+2≤N c := by
    simp only [N]
    have h := pow_two_growth c
    omega
  have hpow : 2^(c+2)≤2^(N c) := Nat.pow_le_pow_right (by omega) hN
  rw [Nat.pow_add] at hpow
  simp only [show 2^2=4 by decide] at hpow
  omega

/-- Exact agreement with Agent6's synthetically halting class-zero formula. -/
theorem H0_eq_paper (c : Nat) (hc : 2≤c) :
    H0 c = 4*2^(N c)-8*2^c+13-c := by
  have hlow := pow_growth_multiply c hc
  have hhigh := high_pow c hc
  dsimp [H0]
  omega

#print axioms H0_eq_paper
#print axioms H0_all_residues
#print axioms H0_shift
end ThreeAdic
