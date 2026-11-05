import FirstForkOddValuationSix
set_option maxHeartbeats 0

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

/-- When the output valuation is exactly seven (divisible by 3^7 but
    not by 3^8), the complete source reset inverse has four explicit arms.
    This is an exact synthetic-parent theorem, not blank reachability. -/
theorem near_top_exact_four (n u A q:Nat) (hn:10≤n)
    (hA:3≤A) (hclose:u+A=4*2^n)
    (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%2187=0) (hnot:(2*u+5)%6561≠0) :
    ResetParent q u ↔
      q=oddPre6 n u ∨ q=oddPre3 n u ∨ q=oddPre n u ∨
      q=evenPre n A := by
  have hsize:8*A≤5*2^n:=by omega
  have hdiv81:(2*u+5)%81=0:=by omega
  have hdiv9:(2*u+5)%9=0:=by omega
  have ho6:=near_top_has_tsix n u A hn hclose htight hdiv
  have ho3:=near_top_has_tthree n u A (by omega) hclose htight hdiv81
  have ho1:=odd_parent_near_top n u A (by omega) hclose hsize hdiv9
  have he:=even_parent_near_top n u A (by omega) hA hclose hsize
  have hp2 : 2^n=2*2^(n-1) := by
    have hh:2^n=2^((n-1)+1):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_succ] at hh
    omega
  have hbandE : 6*2^(n-1)-1≤u ∧ u≤8*2^(n-1)-3 := by omega
  have heveneq : 2*u=8*2^(n-1)+evenPre n A+(n-1) := by
    have hh:=two_n_le_pow n (by omega)
    dsimp [evenPre]
    omega
  let d1:Nat:=(2*u+5)/9
  let d3:Nat:=(2*u+5)/81
  let d6:Nat:=(2*u+5)/2187
  have hd1:9*d1=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 9
    dsimp [d1]
    omega
  have hd3:81*d3=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 81
    dsimp [d3]
    omega
  have hd6:2187*d6=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 2187
    dsimp [d6]
    omega
  have hp4:2^n=4*2^(n-2) := by
    have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hp8:2^n=8*2^(n-3) := by
    have hh:2^n=2^((n-3)+3):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hp32:2^n=32*2^(n-5) := by
    have hh:2^n=2^((n-5)+5):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hlinear : n+3≤4*2^(n-2) := by
    have hh:=n_plus_three_le_pow n (by omega)
    omega
  have hlarge : 1024≤2^n := by
    have hh:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hn
    exact hh
  have hb1 : 6*2^(n-2)+1≤2*d1 ∧ 2*d1≤8*2^(n-2)-1 := by
    constructor <;> omega
  have hb3 : 6*2^(n-3)+1≤8*d3 ∧ 8*d3≤8*2^(n-3)-1 := by
    constructor <;> omega
  have hb6 : 6*2^(n-5)+1≤64*d6 ∧ 64*d6≤8*2^(n-5)-1 := by
    constructor <;> omega
  have eq1 : 2*(2*d1)=8*2^(n-2)+oddPre n u+(n-2)+5 := by
    dsimp [oddPre,d1]
    omega
  have hfour:4*n≤2^n:=by
    have h:∀ k:Nat,4*(k+10)≤2^(k+10):=by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
        omega
    have he:n=(n-10)+10:=by omega
    rw [he]
    exact h (n-10)
  have eq3 : 2*(8*d3)=8*2^(n-3)+oddPre3 n u+(n-3)+5 := by
    dsimp [oddPre3,d3]
    omega
  have hlin6:=sixth_linear n hn
  have eq6 : 2*(64*d6)=8*2^(n-5)+oddPre6 n u+(n-5)+5 := by
    dsimp [oddPre6,d6]
    omega
  constructor
  · intro hq
    rcases hq with ⟨k,hband,heq⟩ | ⟨k,t,d,hd,hband,hout,heq⟩
    · have hk:k=n-1:=even_band_scale_unique u k (n-1) hband hbandE
      right;right;right
      rw [hk] at heq
      omega
    · have ht:=near_top_odd_only_one_three_six n u A k t d hn
        hclose htight hnot hband hout
      rcases ht with ht|ht|ht
      · subst t
        have hdd:d=d1:=by
          have hh:3^(1+1)=9:=by decide
          rw [hh] at hout
          omega
        have hk:k=n-2:=odd_band_scale_unique (2*d1) k (n-2)
          (by simpa [hdd] using hband) hb1
        right;right;left
        rw [hdd,hk] at heq
        omega
      · subst t
        have hdd:d=d3:=by
          have hh:3^(3+1)=81:=by decide
          rw [hh] at hout
          omega
        have hk:k=n-3:=odd_band_scale_unique (8*d3) k (n-3)
          (by simpa [hdd] using hband) hb3
        right;left
        rw [hdd,hk] at heq
        omega
      · subst t
        have hdd:d=d6:=by
          have hh:3^(6+1)=2187:=by decide
          rw [hh] at hout
          omega
        have hk:k=n-5:=odd_band_scale_unique (64*d6) k (n-5)
          (by simpa [hdd] using hband) hb6
        left
        rw [hdd,hk] at heq
        omega
  · rintro (rfl|rfl|rfl|rfl)
    · exact ho6
    · exact ho3
    · exact ho1
    · exact he

#print axioms near_top_exact_four
end CascadeFirstFork
