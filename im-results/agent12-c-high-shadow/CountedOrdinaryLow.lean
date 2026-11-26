import CountedOrdinary

set_option maxHeartbeats 0

namespace BB6.Agent12CountedOrdinaryLow

open BB6.Agent12Clock
open BB6.Agent12CountedOrdinary
open BB6.Agent47ThinCounted

/-- The ordinary counted edge also works at the true source minimum y=5.
    The original y>=8 bound was only used to ensure C=y+(a mod 2)>=4
    for the chain and exit certificates. -/
theorem ordinary_edge5 (a k x y r : Nat) (hr : 1≤r) (ha : 2≤a) (hk : 1≤k)
    (hy : 5≤y) (hb : if r=1 then 2*k≤a else a<2*k)
    (hM : x+2*y=a+2*k+3*r+1)
    (hA : 2^r*(a+2+a%2)=2*x+2*y+2*(a%2)) :
    ∃ t w, Path t w (a,k,0) (x,y,0) ∧
      (t:Int)=2*(k:Int)+r+(a%2:Nat)*(3-3*(r:Int)) ∧
      6*(w:Int)=cost6 a (a+2*k:Nat) x r (a%2:Nat) := by
  let o := a%2
  have ho : o≤1 := by dsimp [o]; omega
  have hoi : (o:Int)=0 ∨ (o:Int)=1 := by omega
  by_cases h1 : r=1
  · subst r
    simp at hb hA
    have hx : x=a-2*k := by omega
    have hy' : y=2*k+2 := by omega
    subst x; subst y
    have hp := direct_counted a k ha hk hb
    refine ⟨_,_,hp,by simp,?_⟩
    have hX : ((a-2*k:Nat):Int)=2*(a:Int)-(a+2*k:Nat) := by omega
    rw [hX]
    change _ = cost6 (a:Int) (a+2*k:Nat) (2*(a:Int)-(a+2*k:Nat)) 1 o
    rw [direct_polynomial _ _ _ hoi]
    push_cast
    grind
  · simp [h1] at hb
    let n := r-2
    have hrn : r=n+2 := by dsimp [n]; omega
    let B := a+2+o
    let K := 2^n*B-(3+o)
    let C := y+o
    have hB : 3+o≤B := by dsimp [B]; omega
    have hpos : 1≤2^n := Nat.pow_pos (by decide)
    have hge := Nat.mul_le_mul_right B hpos
    simp only [Nat.one_mul] at hge
    have hK : K+3+o=2^n*B := by dsimp [K]; omega
    have hpow : 2^r=4*2^n := by rw [hrn,Nat.pow_add]; simp; ac_rfl
    change 2^r*B=2*x+2*y+2*o at hA
    rw [hpow, Nat.mul_assoc,←hK] at hA
    have hKC : C+2*K=2*k-a+3+2*(a-1)+3*n := by dsimp [C]; omega
    have hstop : C≤2*K+6+2*o := by dsimp [C]; omega
    have hC : 4≤C := by dsimp [C]; omega
    have hpar : (a-1)%2+o=1 := by dsimp [o]; omega
    have hkpar : K%2+o=1 := by
      by_cases hn : n=0
      · rw [hn,Nat.pow_zero,Nat.one_mul] at hK; dsimp [B] at hK; omega
      · obtain ⟨j,hj⟩ : ∃ j,n=j+1 := ⟨n-1,by omega⟩
        rw [hj,Nat.pow_succ,Nat.mul_comm (2^j) 2,Nat.mul_assoc] at hK; omega
    obtain ⟨v,hv,hvw⟩ := high_entry a k ha hb
    obtain ⟨t,w,hp,ht,hw⟩ := chain_counted n (a-1) (2*k-a+3) o K C ho hpar
      (by rw [hK]; congr 1; dsimp [B]; omega) hKC (by omega)
    have hpath := hv.append hp
    have ho' : o=0 ∨ o=1 := by omega
    rcases ho' with he|he
    · obtain ⟨z,hz,hzw⟩ := odd_exit K C (by omega) (by omega) (by omega)
      have hx : 2*K+6-C=x := by dsimp [C] at *; omega
      have hy' : C=y := by dsimp [C]; omega
      rw [hx] at hz
      have hz' : Path C z (0,K,C) (x,y,0) := by simpa only [hy'] using hz
      refine ⟨_,_,hpath.append hz',?_,?_⟩
      · change _ = 2*(k:Int)+r+(o:Int)*(3-3*(r:Int))
        rw [he] at ht ⊢
        simp at ht
        push_cast [Int.natCast_sub (show 1≤a by omega)]
        omega
      · change 6*((v+w+z:Nat):Int)=cost6 a (a+2*k:Nat) x r o
        have hT : 2*(2*((K:Int)+3+o))=(a+2*k:Nat)+3*(r:Int)+1+x+2*(o:Int) := by omega
        rw [bounce_polynomial _ _ _ _ _ _ hT hoi]
        have hCC : (a:Int)+2*k+3*r+1-x+2*o=2*(C:Int) := by dsimp [C]; omega
        push_cast
        rw [show (a:Int)+2*k+3*r+1-x+2*o=2*(C:Int) by exact hCC]
        rw [he] at hw ⊢
        push_cast [Int.natCast_sub (show 1≤a by omega)] at hw
        push_cast at hzw
        have hri : (r:Int)=(n:Int)+2 := by omega
        rw [hri]
        grind
    · obtain ⟨z,hz,hzw⟩ := even_exit K C (by omega) (by omega) (by omega)
      have hx : 2*K+8-C=x := by dsimp [C] at *; omega
      have hy' : C-1=y := by dsimp [C]; omega
      rw [hx,hy'] at hz
      refine ⟨_,_,hpath.append hz,?_,?_⟩
      · change _ = 2*(k:Int)+r+(o:Int)*(3-3*(r:Int))
        rw [he] at ht ⊢
        simp at ht
        push_cast [Int.natCast_sub (show 1≤a by omega), Int.natCast_sub (show 3≤C by omega)]
        omega
      · change 6*((v+w+z:Nat):Int)=cost6 a (a+2*k:Nat) x r o
        have hT : 2*(2*((K:Int)+3+o))=(a+2*k:Nat)+3*(r:Int)+1+x+2*(o:Int) := by omega
        rw [bounce_polynomial _ _ _ _ _ _ hT hoi]
        have hCC : (a:Int)+2*k+3*r+1-x+2*o=2*(C:Int) := by dsimp [C]; omega
        push_cast
        rw [show (a:Int)+2*k+3*r+1-x+2*o=2*(C:Int) by exact hCC]
        rw [he] at hw ⊢
        push_cast [Int.natCast_sub (show 1≤a by omega)] at hw
        push_cast at hzw
        have hri : (r:Int)=(n:Int)+2 := by omega
        rw [hri]
        grind

end BB6.Agent12CountedOrdinaryLow
