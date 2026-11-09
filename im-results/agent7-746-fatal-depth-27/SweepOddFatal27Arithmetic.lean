import Std
set_option maxHeartbeats 0

namespace CascadeFatalDepth27

private theorem pow2_period18 (n : Nat) : 2^(n+18)%27=2^n%27 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow2_mod18 (n : Nat) : 2^n%27=2^(n%18)%27 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n<18
    · rw [Nat.mod_eq_of_lt hn]
    · have ht : n=(n-18)+18 := by omega
      have hm : n%18=(n-18)%18 := by omega
      calc
        2^n%27=2^((n-18)+18)%27 := congrArg (fun e : Nat => 2^e%27) ht
        _=2^(n-18)%27 := pow2_period18 (n-18)
        _=2^((n-18)%18)%27 := ih (n-18) (by omega)
        _=2^(n%18)%27 := by rw [hm]

private theorem mod_gate_reduced (k m : Nat) :
    ((16*2^k+2*k+5)%27 = (2^(m+1)*(4*k+10))%27) ↔
    ((16*2^(k%18)+2*(k%27)+5)%27 =
         (2^((m+1)%18)*(4*(k%27)+10))%27) := by
  have hp : (2^k)%27=(2^(k%18))%27 := pow2_mod18 k
  have hl : (16*2^k+2*k+5)%27 = (16*2^(k%18)+2*(k%27)+5)%27 := by omega
  have hq : (2^(m+1))%27 = (2^((m+1)%18))%27 := pow2_mod18 (m+1)
  have hr : (4*k+10)%27 = (4*(k%27)+10)%27 := by omega
  have hright : (2^(m+1)*(4*k+10))%27 =
      (2^((m+1)%18)*(4*(k%27)+10))%27 := by
    have hxy : ((2^(m+1)%27)*((4*k+10)%27))%27 =
      ((2^((m+1)%18)%27)*((4*(k%27)+10)%27))%27 := by rw [hq, hr]
    simpa only [Nat.mul_mod, Nat.mod_mod] using hxy
  rw [hl,hright]

/-- Unique arithmetic depth class modulo 18 for the high odd-entry fatal gate. -/
def depth27 (r : Nat) : Nat :=
  match r%54 with
  | 3 => 5  | 4 => 17 | 9 => 3  | 10 => 13 | 15 => 1 | 16 => 9
  | 21 => 17 | 22 => 5 | 27 => 15 | 28 => 1 | 33 => 13 | 34 => 15
  | 39 => 11 | 40 => 11 | 45 => 9 | 46 => 7 | 51 => 7 | 52 => 3
  | _ => 0

private theorem finite_gate_unique (r s : Nat)
    (hr : r<54) (hs : s<18)
    (hsector : r%6=3 ∨ r%6=4)
    (hgate : (16*2^(r%18)+2*(r%27)+5)%27 =
          (2^((s+1)%18)*(4*(r%27)+10))%27) :
    s=depth27 r := by
  have table : ∀ (x : Fin 54) (y : Fin 18),
    (x.val%6=3 ∨ x.val%6=4) →
    (16*2^(x.val%18)+2*(x.val%27)+5)%27 =
      (2^((y.val+1)%18)*(4*(x.val%27)+10))%27 →
    y.val=depth27 x.val := by decide
  exact table ⟨r, hr⟩ ⟨s, hs⟩ hsector hgate

/-- For high odd-entry fatal histories, k mod54 uniquely fixes m mod18. -/
theorem fatal_depth_mod27 (k m : Nat)
    (hsector : k%6=3 ∨ k%6=4)
    (hgate : (16*2^k+2*k+5)%27=(2^(m+1)*(4*k+10))%27) :
    m%18=depth27 (k%54) := by
  let r := k%54
  let s := m%18
  have hr : r<54 := Nat.mod_lt k (by decide)
  have hs : s<18 := Nat.mod_lt m (by decide)
  have hk18 : k%18=r%18 := by dsimp [r]; omega
  have hk27 : k%27=r%27 := by dsimp [r]; omega
  have hm18 : (m+1)%18=(s+1)%18 := by dsimp [s]; omega
  have hred := (mod_gate_reduced k m).mp hgate
  have hgate' : (16*2^(r%18)+2*(r%27)+5)%27 =
      (2^((s+1)%18)*(4*(r%27)+10))%27 := by
    rw [←hk18, ←hk27, ←hm18]
    exact hred
  have hsector' : r%6=3 ∨ r%6=4 := by
    have hk6 : k%6=r%6 := by dsimp [r]; omega
    simpa only [←hk6] using hsector
  exact finite_gate_unique r s hr hs hsector' hgate'

#print axioms fatal_depth_mod27
end CascadeFatalDepth27
