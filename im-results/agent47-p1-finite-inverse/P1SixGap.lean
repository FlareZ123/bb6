import Std
namespace BB6.Agent47P1

def sixX (h : Nat) : Nat := 2^(16*h)
def sixU (h : Nat) : Nat := 28*sixX h-(h+2)

private theorem two_pow_ge_add_one (h : Nat) : h+1 ≤ 2^h := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [Nat.pow_succ]
    omega

theorem sixX_growth (h:Nat) : h+1 ≤ sixX h := by
  have hl := two_pow_ge_add_one h
  have he : h≤16*h := by omega
  have hp : (2:Nat)^h ≤ (2:Nat)^(16*h) :=
    Nat.pow_le_pow_right (by decide) he
  unfold sixX
  omega

theorem sixU_shift (h:Nat) : sixU h+(h+2)=28*sixX h := by
  unfold sixU
  have hbound := sixX_growth h
  omega

theorem sixU_lower (h:Nat) : 3 ≤ sixU h := by
  have hbound := sixX_growth h
  have hs := sixU_shift h
  omega

private theorem sixpower_lower (h:Nat) :
    14*2^(16*h+5)=448*sixX h := by
  unfold sixX
  rw [Nat.pow_add]
  simp only [show (2:Nat)^5=32 by decide]
  omega

private theorem sixpower_upper (h:Nat) :
    14*2^(16*h+6)=896*sixX h := by
  unfold sixX
  rw [Nat.pow_add]
  simp only [show (2:Nat)^6=64 by decide]
  omega

private theorem no_14_power_between (e v:Nat)
    (hl:14*2^e<v) (hu:v<14*2^(e+1)) :
    ∀ j:Nat, v ≠ 14*2^j := by
  intro j heq
  have hlow : 2^e < 2^j := by omega
  have hupper : 2^j < 2^(e+1) := by omega
  have hjlo : e<j :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hlow
  have hjhi : j<e+1 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hupper
  omega

private theorem six_gap_generic (h A C:Nat)
    (hl:448*sixX h<A*sixU h+C)
    (hu:A*sixU h+C<896*sixX h) :
    ∀j:Nat, A*sixU h+C ≠14*2^j := by
  apply no_14_power_between (16*h+5)
  · simpa only [sixpower_lower] using hl
  · simpa only [show 16*h+5+1=16*h+6 by omega,
          sixpower_upper] using hu

theorem six_gap0 (h:Nat) :
    ∀j:Nat,30*sixU h+40 ≠14*2^j := by
  apply six_gap_generic h 30 40
  · have hx := sixX_growth h
    have hs := sixU_shift h
    omega
  · have hx := sixX_growth h
    have hs := sixU_shift h
    omega

theorem six_gap1 (h:Nat) :
    ∀j:Nat,20*sixU h+28 ≠14*2^j := by
  apply six_gap_generic h 20 28
  · have hx := sixX_growth h
    have hs := sixU_shift h
    omega
  · have hx := sixX_growth h
    have hs := sixU_shift h
    omega

theorem six_gap2 (h:Nat) :
    ∀j:Nat,18*sixU h+24 ≠14*2^j := by
  apply six_gap_generic h 18 24
  · have hx := sixX_growth h
    have hs := sixU_shift h
    omega
  · have hx := sixX_growth h
    have hs := sixU_shift h
    omega

theorem six_root_identity (h:Nat) :
    32*sixU h+36 = 14*2^(16*h+6)-2*(16*h+6)-16 := by
  have hs := sixU_shift h
  have hpow : 14*2^(16*h+6)=896*sixX h := sixpower_upper h
  omega

#print axioms six_gap0
#print axioms six_gap1
#print axioms six_gap2
#print axioms six_root_identity
end BB6.Agent47P1
