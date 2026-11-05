import Std
set_option maxRecDepth 4096

namespace Agent17SheepH3

private theorem pow_mod_reduce (m p n : Nat) (_hm : 0 < m) (_hp : 0 < p)
    (hperiod : (2:Nat)^p % m = 1) :
    (2:Nat)^n % m = (2:Nat)^(n%p) % m := by
  have he : n = n % p + p * (n / p) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div n p).symm
  calc
    (2:Nat)^n % m = 2^(n%p+p*(n/p))%m := congrArg (fun x => (2:Nat)^x %m) he
    _ = (2^(n%p) * (2^p)^(n/p))%m := by rw [Nat.pow_add, Nat.pow_mul]
    _ = ((2^(n%p)%m) * (((2^p)^(n/p))%m))%m := by rw [Nat.mul_mod]
    _ = ((2^(n%p)%m) * (((2^p%m)^(n/p))%m))%m := by
      exact congrArg (fun v : Nat => ((2^(n%p)%m)*v)%m) (Nat.pow_mod (2^p) (n/p) m)
    _ = (2:Nat)^(n%p)%m := by simp [hperiod]

theorem pow135_eq124 (n : Nat) :
    (2:Nat)^n % 135 = 124 ↔ n%36=22 := by
  have hp : (2:Nat)^36%135=1 := by decide
  have hred := pow_mod_reduce 135 36 n (by decide) (by decide) hp
  have hlt : n%36<36 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 36, ((2:Nat)^r.val%135=124 ↔ r.val=22) := by decide
  rw [hred]
  exact hfinite ⟨n%36,hlt⟩

theorem pow243_eq43 (n : Nat) :
    (2:Nat)^n % 243 = 43 ↔ n%162=130 := by
  have hp : (2:Nat)^162%243=1 := by decide
  have hred := pow_mod_reduce 243 162 n (by decide) (by decide) hp
  have hlt : n%162<162 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 162, ((2:Nat)^r.val%243=43 ↔ r.val=130) := by decide
  rw [hred]
  exact hfinite ⟨n%162,hlt⟩

theorem pow17_ne12 (n : Nat) : (2:Nat)^n % 17 ≠ 12 := by
  have hp : (2:Nat)^8%17=1 := by decide
  have hred := pow_mod_reduce 17 8 n (by decide) (by decide) hp
  have hlt : n%8<8 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 8, (2:Nat)^r.val%17≠12 := by decide
  rw [hred]
  exact hfinite ⟨n%8,hlt⟩

theorem pow33_ne19 (n : Nat) : (2:Nat)^n % 33 ≠ 19 := by
  have hp : (2:Nat)^10%33=1 := by decide
  have hred := pow_mod_reduce 33 10 n (by decide) (by decide) hp
  have hlt : n%10<10 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 10, (2:Nat)^r.val%33≠19 := by decide
  rw [hred]
  exact hfinite ⟨n%10,hlt⟩

theorem pow5_ne0 (n : Nat) : (2:Nat)^n % 5 ≠ 0 := by
  have hp : (2:Nat)^4%5=1 := by decide
  have hred := pow_mod_reduce 5 4 n (by decide) (by decide) hp
  have hlt : n%4<4 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 4, (2:Nat)^r.val%5≠0 := by decide
  rw [hred]
  exact hfinite ⟨n%4,hlt⟩

theorem pow81_eq16 (n : Nat) : (2:Nat)^n % 81 = 16 ↔ n%54=4 := by
  have hp : (2:Nat)^54%81=1 := by decide
  have hred := pow_mod_reduce 81 54 n (by decide) (by decide) hp
  have hlt : n%54<54 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 54, ((2:Nat)^r.val%81=16 ↔ r.val=4) := by decide
  rw [hred]
  exact hfinite ⟨n%54,hlt⟩

theorem pow257_ne56 (n : Nat) : (2:Nat)^n % 257 ≠ 56 := by
  have hp : (2:Nat)^16%257=1 := by decide
  have hred := pow_mod_reduce 257 16 n (by decide) (by decide) hp
  have hlt : n%16<16 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 16, (2:Nat)^r.val%257≠56 := by decide
  rw [hred]
  exact hfinite ⟨n%16,hlt⟩

theorem pow171_ne25 (n : Nat) : (2:Nat)^n % 171 ≠ 25 := by
  have hp : (2:Nat)^18%171=1 := by decide
  have hred := pow_mod_reduce 171 18 n (by decide) (by decide) hp
  have hlt : n%18<18 := Nat.mod_lt _ (by decide)
  have hfinite : ∀ r : Fin 18, (2:Nat)^r.val%171≠25 := by decide
  rw [hred]
  exact hfinite ⟨n%18,hlt⟩

private theorem high_k_gap_shift (n : Nat) :
    1 < 54*(n+9)-65 ∧ 54*(n+9)-65 < (2:Nat)^(n+9) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : (2:Nat)^(n+1+9) = 2*2^(n+9) := by
        rw [show n+1+9=(n+9)+1 by omega, Nat.pow_succ]
        omega
      have hbig : 54 ≤ (2:Nat)^(n+9) := by
        have hx : (2:Nat)^9 ≤ (2:Nat)^(n+9) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [hpow]
      omega

theorem high_k_gap_bound (a : Nat) (ha : 9 ≤ a) :
    1 < 54*a-65 ∧ 54*a-65 < (2:Nat)^a := by
  have heq : a-9+9=a := by omega
  simpa only [heq] using high_k_gap_shift (a-9)

theorem no_a6_in_sector (j : Nat) (hj : j%18=0) (hj54 : j%54≠0) :
    (2:Nat)^(j+4)%81 ≠ 16 := by
  intro h
  have hr := (pow81_eq16 (j+4)).mp h
  omega

#print axioms pow135_eq124
#print axioms pow243_eq43
#print axioms pow17_ne12
#print axioms pow33_ne19
#print axioms pow5_ne0
#print axioms pow81_eq16
#print axioms pow257_ne56
#print axioms pow171_ne25
#print axioms high_k_gap_bound
#print axioms no_a6_in_sector

end Agent17SheepH3
