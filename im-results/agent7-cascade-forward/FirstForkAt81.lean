import FirstForkOddT2
import FirstForkModulo54

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

theorem near_top_exact_two_at81 (n u A q:Nat) (hn:4≤n)
    (hA:3≤A) (hclose:u+A=4*2^n)
    (hsize:8*A≤5*2^n)
    (hdiv9:(2*u+5)%9=0) (hnot81:(2*u+5)%81≠0) :
    ResetParent q u ↔ q=oddPre n u ∨ q=evenPre n A := by
  have ho := odd_parent_near_top n u A hn hclose hsize hdiv9
  have he := even_parent_near_top n u A hn hA hclose hsize
  have hpow2 : 2^n=2*2^(n-1) := by
    have hh:2^n=2^((n-1)+1):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_succ] at hh
    omega
  have hbandE : 6*2^(n-1)-1≤u ∧ u≤8*2^(n-1)-3 := by omega
  have heveneq : 2*u=8*2^(n-1)+evenPre n A+(n-1) := by
    have hh:=two_n_le_pow n hn
    dsimp [evenPre]
    omega
  have hbiglo:3*2^n≤u := by omega
  have hbighi:u≤4*2^n := by omega
  let d0 := (2*u+5)/9
  have hd0:9*d0=2*u+5 := by
    have hm:=Nat.mod_add_div (2*u+5) 9
    dsimp [d0]
    omega
  have hpow4:2^n=4*2^(n-2) := by
    have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hlarge : 4 ≤ 2^(n-2) := by
    have hp := pow_at_least_16 n hn
    omega
  have odd_band : 6*2^(n-2)+1≤2*d0 ∧ 2*d0≤8*2^(n-2)-1 := by
    constructor <;> omega
  have hlinear : n+3 ≤ 4*2^(n-2) := by
    have hp := n_plus_three_le_pow n hn
    omega
  have odd_eq:2*(2*d0)=8*2^(n-2)+oddPre n u+(n-2)+5 := by
    dsimp [oddPre,d0]
    omega
  constructor
  · intro hp
    rcases hp with ⟨k,hband,heq⟩|⟨k,t,d,hd,hband,hout,heq⟩
    · have hk : k=n-1 := even_band_scale_unique u k (n-1) hband hbandE
      right
      rw [hk] at heq
      omega
    · by_cases ht:t=0
      · subst t
        have hprod : 2*u+5=3*d := by simpa using hout
        exact False.elim (odd_tzero_in_dyadic_gap n u hn hbiglo hbighi
          ⟨k,d,by simpa using hband,hprod⟩)
      · have ht1 : t=1 := by
          by_cases hte:t=1
          · exact hte
          by_cases ht2:t=2
          · subst t
            have hpow2:2^2=4 := by decide
            have hpow3:3^(2+1)=27 := by decide
            have hbad:2*u+5=27*d := by simpa [hpow3] using hout
            have hband2:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1 := by
              simpa [hpow2] using hband
            exact False.elim ((near_top_no_odd_ttwo n u A hn hclose hsize)
              ⟨k,d,hband2,hbad⟩)
          · have ht3:3≤t := by omega
            have hex:t+1=4+(t-3):=by omega
            have hpow:3^(t+1)%81=0:=by
              rw [hex,Nat.pow_add]
              simp
            have hzero:(2*u+5)%81=0:=by
              rw [hout,Nat.mul_mod,hpow]
              simp
            exact False.elim (hnot81 hzero)
        subst t
        have hdd:d=d0 := by
          have hp:3^(1+1)=9 := by decide
          rw [hp] at hout
          omega
        have hk : k=n-2 := odd_band_scale_unique (2*d0) k (n-2)
          (by simpa [hdd] using hband) odd_band
        left
        rw [hdd,hk] at heq
        omega
  · rintro (rfl|rfl)
    · exact ho
    · exact he

#print axioms near_top_exact_two_at81
end CascadeFirstFork
