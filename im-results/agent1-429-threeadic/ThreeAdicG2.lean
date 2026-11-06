import ThreeAdicLifting
namespace ThreeAdic
private theorem mod_lt2 (m x : Nat) (hm:0<m) (h:x<2*m) :
   (x<m ∧ x%m=x) ∨ (m≤x ∧ x%m=x-m) := by
  by_cases hx : x<m
  · exact Or.inl ⟨hx,Nat.mod_eq_of_lt hx⟩
  · right
    constructor
    · omega
    · rw [Nat.mod_eq_sub_mod (by omega : x≥m)]
      exact Nat.mod_eq_of_lt (by omega : x-m<m)

theorem mod_add_cancel (m x y k:Nat) (hm:0<m)
   (h:(x+k)%m=(y+k)%m) : x%m=y%m := by
  have ha : (x%m+k%m)%m=(y%m+k%m)%m := by
    exact (Nat.add_mod x k m).symm.trans (h.trans (Nat.add_mod y k m))
  have hx : x%m<m := Nat.mod_lt _ hm
  have hy : y%m<m := Nat.mod_lt _ hm
  have hk : k%m<m := Nat.mod_lt _ hm
  rcases mod_lt2 m (x%m+k%m) hm (by omega) with h1 | h1 <;>
  rcases mod_lt2 m (y%m+k%m) hm (by omega) with h2 | h2 <;>
  omega

theorem mod_sub_congr (m a b k:Nat) (hm:0<m)
  (ha:k≤a) (hb:k≤b) (h:a%m=b%m) :
  (a-k)%m=(b-k)%m := by
  apply mod_add_cancel m (a-k) (b-k) k hm
  simpa [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] using h

theorem pow_two_growth : ∀ t : Nat, t+1≤2^t := by
  intro t
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Nat.pow_succ]
      omega

def G2 (t:Nat) : Nat := 4*2^t-t

theorem G2_shift (e t : Nat) :
    (G2 (t+2*3^e)+2*3^e)%(3^(e+1))=G2 t%(3^(e+1)) := by
  let p := 2*3^e
  let M := 3^(e+1)
  have ha : t+p≤4*2^(t+p) := by
    have h := pow_two_growth (t+p)
    omega
  have hb : t≤4*2^t := by
    have h := pow_two_growth t
    omega
  have hp : (2^(t+p))%M=2^t%M := shift_two_power e t
  have hmul : (4*2^(t+p))%M=(4*2^t)%M := by
    calc
      _ = (4%M * ((2^(t+p))%M))%M := Nat.mul_mod _ _ _
      _ = (4%M * (2^t%M))%M := by rw [hp]
      _ = (4*2^t)%M := (Nat.mul_mod _ _ _).symm
  have hsub : (4*2^(t+p)-t)%M=(4*2^t-t)%M :=
    mod_sub_congr M (4*2^(t+p)) (4*2^t) t (Nat.pow_pos (by omega))
       (by omega) hb hmul
  have heq : 4*2^(t+p)-(t+p)+p=4*2^(t+p)-t := by omega
  simpa only [G2, p, M, heq] using hsub

theorem G2_all_residues (E r:Nat) :
    ∃ t, 1≤t ∧ t≤1+2*(3^E-1) ∧ G2 t%3^E=r%3^E :=
  all_residues G2 1 G2_shift E r

theorem shift_sixteen_power (e q : Nat) :
    (16^(q+2*3^e))%(3^(e+1))=16^q%(3^(e+1)) := by
  have hp : 16^(2*3^e)%(3^(e+1))=1 := by
    have heq : 16^(2*3^e)=(2^(2*3^e))^4 := by
      calc
        _ = (2^4)^(2*3^e) := by rw [show (16:Nat)=2^4 by decide]
        _ = 2^(4*(2*3^e)) := (Nat.pow_mul 2 4 (2*3^e)).symm
        _ = 2^((2*3^e)*4) := by congr 1; omega
        _ = (2^(2*3^e))^4 := Nat.pow_mul 2 (2*3^e) 4
    rw [heq, Nat.pow_mod, power_period e]
    have hm : 0<3^e := Nat.pow_pos (by omega)
    exact Nat.mod_eq_of_lt (by simp only [Nat.pow_add_one]; omega)
  rw [Nat.pow_add,Nat.mul_mod,hp]
  simp

def G1 (q : Nat) : Nat := 16^q-q

theorem G1_shift (e q : Nat) :
    (G1 (q+2*3^e)+2*3^e)%(3^(e+1))=G1 q%(3^(e+1)) := by
  let p := 2*3^e
  let M := 3^(e+1)
  have ha : q+p≤16^(q+p) := by
    have h := pow_two_growth (q+p)
    have hh : 2^(q+p)≤16^(q+p) := by
      exact Nat.pow_le_pow_left (by omega) _
    omega
  have hb : q≤16^q := by
    have h := pow_two_growth q
    have hh : 2^q≤16^q := Nat.pow_le_pow_left (by omega) _
    omega
  have hp : (16^(q+p))%M=16^q%M := shift_sixteen_power e q
  have hsub : (16^(q+p)-q)%M=(16^q-q)%M :=
    mod_sub_congr M (16^(q+p)) (16^q) q (Nat.pow_pos (by omega))
       (by omega) hb hp
  have heq : 16^(q+p)-(q+p)+p=16^(q+p)-q := by omega
  simpa only [G1,p,M,heq] using hsub

theorem G1_all_residues (E r:Nat) :
    ∃ q, 1≤q ∧ q≤1+2*(3^E-1) ∧ G1 q%3^E=r%3^E :=
  all_residues G1 1 G1_shift E r

#print axioms G1_all_residues
#print axioms G2_all_residues
#print axioms G2_shift
end ThreeAdic
