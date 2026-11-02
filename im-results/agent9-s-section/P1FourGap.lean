import Std
set_option maxRecDepth 2048
namespace BB6.Agent9P1

private theorem two_pow_ge_add_one (h:Nat) : h+1 ≤ 2^h := by
  induction h with
  | zero => decide
  | succ h ih =>
      rw [Nat.pow_succ]
      omega

def X (h k:Nat) : Nat := 2^(512*h+k)
def t (h k:Nat) : Nat := 7*X h k-4*(h+1)

theorem X_growth (h k:Nat) (hk:5≤k) : 32*(h+1) ≤ X h k := by
  have he : h+5 ≤ 512*h+k := by omega
  have hp := Nat.pow_le_pow_right (by decide : (1:Nat)≤2) he
  have hl := two_pow_ge_add_one h
  have hi : 2^(h+5)=32*2^h := by
    rw [Nat.pow_add]
    simp [Nat.mul_comm]
  dsimp [X]
  rw [hi] at hp
  omega

theorem t_shift (h k:Nat) (hk:5≤k) :
  t h k+4*(h+1)=7*X h k := by
  have hg:=X_growth h k hk
  dsimp [t]
  omega

theorem t_growth (h k:Nat) (hk:5≤k) :
  220*(h+1) ≤ t h k := by
  have hg:=X_growth h k hk
  have hs:=t_shift h k hk
  omega

theorem power_low (h k:Nat) :
  14*2^(512*h+k+6)=128*7*X h k := by
  unfold X
  rw [show 512*h+k+6= (512*h+k)+6 by omega, Nat.pow_add]
  simp [Nat.mul_comm]
  omega

theorem power_high (h k:Nat) :
  14*2^(512*h+k+7)=256*7*X h k := by
  unfold X
  rw [show 512*h+k+7= (512*h+k)+7 by omega, Nat.pow_add]
  simp [Nat.mul_comm]
  omega

private theorem no_14_power_between (e v:Nat)
    (hl:14*2^e<v) (hu:v<14*2^(e+1)) :
    ∀ j:Nat, v ≠14*2^j := by
  intro j heq
  have hlow : 2^e < 2^j := by omega
  have hupper : 2^j < 2^(e+1) := by omega
  have hjlo : e<j :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hlow
  have hjhi : j<e+1 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hupper
  omega

/-- Uniform power gap for affine leaves 132≤A≤254 and B≤768
  on t=7*2^(512h+k)-4(h+1), k≥5. -/
theorem leaf_gap (h k A B:Nat) (hk:5≤k)
    (hAl:132≤A) (hAu:A≤254) (hB:B≤768) :
    ∀ j:Nat, A*t h k+B ≠14*2^j := by
  have ht := t_growth h k hk
  have hs := t_shift h k hk
  have hal : 132*t h k ≤ A*t h k := Nat.mul_le_mul_right (t h k) hAl
  have hau : A*t h k ≤254*t h k := Nat.mul_le_mul_right (t h k) hAu
  have hl : 128*7*X h k < A*t h k+B := by omega
  have hu : A*t h k+B < 256*7*X h k := by omega
  apply no_14_power_between (512*h+k+6)
  · rw [power_low]; exact hl
  · simpa only [show 512*h+k+6+1=512*h+k+7 by omega, power_high] using hu

#print axioms leaf_gap

/-- The smaller affine parameter used by finite G-inverse certificates. -/
def s (h k : Nat) : Nat := 7*2^(512*h+k-2)-(h+1)

theorem s_shift (h k:Nat) (hk:7≤k) :
    s h k+(h+1)=7*2^(512*h+k-2) := by
  have he : 512*h+k-2 = 512*h+(k-2) := by omega
  have hb := X_growth h (k-2) (by omega)
  unfold X at hb
  rw [←he] at hb
  dsimp [s]
  omega

theorem four_s_eq_t (h k:Nat) (hk:7≤k) :
    4*s h k=t h k := by
  have hs := s_shift h k hk
  have ht := t_shift h k (by omega)
  have hpow : X h k = 4*2^(512*h+k-2) := by
    unfold X
    have he : 512*h+k = (512*h+k-2)+2 := by omega
    rw [he, Nat.pow_add]
    simp [Nat.mul_comm]
  rw [hpow] at ht
  omega

/-- Common all-residue affine gateway identity. -/
theorem root_affine (h k C:Nat) (hk:7≤k)
    (hC:C+2*k=994) :
    1024*s h k+C = 14*2^(512*h+k+7)-2*(512*h+k+7)-16 := by
  have ht := t_shift h k (by omega)
  have hs := four_s_eq_t h k hk
  have hp := power_high h k
  omega

#print axioms root_affine

end BB6.Agent9P1
