import CarryBudget
import BitCarry
namespace BB6.Agent28CarryBudget
open BB6.Agent43CarryCert BB6.Agent28BitCarry
theorem half_dvd (k a b : Nat) (h : 2^(k+1) ∣ a+b)
    (ha : a%2=0) (hb : b%2=0) : 2^k ∣ a/2+b/2 := by
  have he : a+b=2*(a/2+b/2) := by omega
  rw [he,Nat.pow_succ,Nat.mul_comm (2^k) 2] at h
  exact Nat.dvd_of_mul_dvd_mul_left (by decide) h
theorem even_of_pow_dvd (k a : Nat) (h : 2^(k+1)∣a) : a%2=0 := by
  have hp := Nat.dvd_trans (Nat.pow_dvd_pow 2 (show 1≤k+1 by omega)) h
  simpa [Nat.dvd_iff_mod_eq_zero] using hp
theorem coupled_step (Q r j k c p u : Nat)
    (hcoeff : 2^(k+1) ∣ (Q-j)+(r+3+j))
    (hpair : 2^(k+1) ∣ c+p)
    (hu : u ∈ step Q j [c]) :
    ∃ v ∈ listStep (r+3+j) [p], 2^k ∣ u+v := by
  simp only [step, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at hu
  rcases hu with hu | hu
  · by_cases he : c%2=0
    · simp [he] at hu
      subst u
      have hp : p%2=0 := by have := even_of_pow_dvd k (c+p) hpair; omega
      refine ⟨p/2,by simp [listStep,hp],half_dvd k c p hpair he hp⟩
    · simp [he] at hu
  · by_cases he : (c+(Q-j))%2=0
    · simp [he] at hu
      subst u
      have hsum : 2^(k+1)∣(c+(Q-j))+(p+(r+3+j)) := by
        have hs := Nat.dvd_add hpair hcoeff
        rwa [show (c+p)+((Q-j)+(r+3+j)) =
          (c+(Q-j))+(p+(r+3+j)) by ac_rfl] at hs
      have hp : (p+(r+3+j))%2=0 := by
        have := even_of_pow_dvd k _ hsum
        omega
      refine ⟨(p+(r+3+j))/2,by simp [listStep,hp],half_dvd k _ _ hsum he hp⟩
    · simp [he] at hu
theorem coupled_run (Q r j k : Nat) (cs ps : List Nat)
    (hcoeff : ∀ i<k, 2^k∣(Q-(j+i))+(r+3+(j+i)))
    (hrel : ∀ c∈cs, ∃ p∈ps, 2^k∣c+p)
    (hempty : listRun r j ps k=[]) :
    states Q j cs k=[] := by
  induction k generalizing j cs ps with
  | zero =>
      simp [listRun] at hempty
      subst ps
      cases cs with
      | nil => rfl
      | cons c cs =>
          obtain ⟨p,hp,_⟩ := hrel c (by simp)
          simp at hp
  | succ k ih =>
      simp only [states, listRun] at hempty ⊢
      apply ih (j+1) (step Q j cs) (listStep (r+3+j) ps)
      · intro i hi
        have hd := hcoeff (i+1) (by omega)
        have hsmall := Nat.dvd_trans (Nat.pow_dvd_pow 2 (show k≤k+1 by omega)) hd
        simpa only [show j+(i+1)=j+1+i by omega] using hsmall
      · intro u hu
        simp only [step, List.mem_flatMap] at hu
        obtain ⟨c,hc,hu⟩ := hu
        obtain ⟨p,hp,hpair⟩ := hrel c hc
        have hc0 := hcoeff 0 (by omega)
        simp only [Nat.add_zero] at hc0
        have hu0 : u∈step Q j [c] := by simpa [step] using hu
        obtain ⟨v,hv,hdiv⟩ := coupled_step Q r j k c p u hc0 hpair hu0
        refine ⟨v, ?_, hdiv⟩
        simp only [listStep, List.mem_flatMap]
        exact ⟨p,hp,by simpa [listStep] using hv⟩
      · exact hempty
theorem full_empty_of_modular_certificate (n r k t : Nat)
    (hn : 2*n+3≤7*2^n) (hkn : k+1≤n)
    (hN : n=r+2^(k+1)*t) (hr : r%2=0)
    (hempty : listRun r 1 [((r+2)/2)] k=[]) :
    states (7*2^n-(n+3)) 0 [1] (k+1)=[] := by
  let Q := 7*2^n-(n+3)
  have hQ : n≤Q := by dsimp [Q]; omega
  have hcoeff : 2^(k+1)∣Q+(r+3) := by
    have hp := Nat.dvd_trans (Nat.pow_dvd_pow 2 hkn) (Nat.dvd_mul_left (2^n) 7)
    have he : Q+(r+3)+2^(k+1)*t=7*2^n := by dsimp [Q]; omega
    rw [← he] at hp
    exact (Nat.dvd_add_iff_left (Nat.dvd_mul_right (2^(k+1)) t)).mpr hp
  change states Q 0 [1] (k+1)=[]
  simp only [states, Nat.zero_add]
  apply coupled_run Q r 1 k (step Q 0 [1]) [((r+2)/2)]
  · intro i hi
    have hEq : (Q-(1+i))+(r+3+(1+i))=Q+(r+3) := by omega
    rw [hEq]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (show k≤k+1 by omega)) hcoeff
  · intro c hc
    simp only [step, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Nat.sub_zero] at hc
    simp at hc
    by_cases he : (1+Q)%2=0
    · simp [he] at hc
      subst c
      have hsum : 2^(k+1)∣(1+Q)+(r+2) := by
        rwa [show (1+Q)+(r+2)=Q+(r+3) by omega]
      exact ⟨(r+2)/2,by simp,half_dvd k (1+Q) (r+2) hsum he (by omega)⟩
    · simp [he] at hc
  · exact hempty
theorem margin_of_modular_certificate (n r k t : Nat)
    (hn : 2*n+3≤7*2^n) (hkn : k+1≤n)
    (hN : n=r+2^(k+1)*t) (hr : r%2=0)
    (hbudget : 2^k*requiredMargin n (k+1)≤7*2^n-(n+3)+1)
    (hempty : listRun r 1 [((r+2)/2)] k=[]) :
    MarginSafe (7*2^n-(n+3)) (requiredMargin n (k+1)) 0 [1] (k+1) [] := by
  apply margin_of_early_empty
  · omega
  · unfold requiredMargin; omega
  · simpa using hbudget
  · exact full_empty_of_modular_certificate n r k t hn hkn hN hr hempty
#print axioms coupled_step
#print axioms coupled_run
#print axioms full_empty_of_modular_certificate
#print axioms margin_of_modular_certificate
end BB6.Agent28CarryBudget
