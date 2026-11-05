import FourthGeneralTwo
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeAgent10TripleFork
open CascadeResetInverse CascadeUniformFatal CascadeAgent10Four CascadeAgent10FourthBranch CascadeAgent10Mod81

private theorem n_growth (n:Nat) (hn:11≤n) :
  1984*n+3300 ≤ 13*2^n := by
  have h : ∀ k:Nat,1984*(k+11)+3300 ≤ 13*2^(k+11) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+11=k+11+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-11)+11:=by omega
  rw [he]
  exact h (n-11)

private theorem pos_growth (n:Nat) (hn:11≤n) :
  257*n+500 ≤ 5*2^n := by
  have h : ∀ k:Nat,257*(k+11)+500 ≤ 5*2^(k+11) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+11=k+11+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-11)+11:=by omega
  rw [he]
  exact h (n-11)

/-- Two of eighteen mod162 fatal index classes have divisibility by 81 in
    the fourth ancestor odd-gate numerator, enabling a second odd valuation. -/
theorem fourth_div81 (n:Nat) (hn:64≤n)
    (hres:n%162=64 ∨ n%162=107) :
    (2*fourthPred n+5)%81=0 := by
  have hg := fifth_growth n (by omega)
  have heq : 2*fourthPred n+5+62*n+93=8*2^n := by
    dsimp [fourthPred]
    omega
  have hp := pow_mod_fiftyfour n
  rcases hres with h|h
  · have hm:n%54=10:=by omega
    have hn81:n%81=64:=by omega
    have hp81:2^n%81=2^10%81:=by rw [hp,hm]
    omega
  · have hm:n%54=53:=by omega
    have hn81:n%81=26:=by omega
    have hp81:2^n%81=2^53%81:=by rw [hp,hm]
    omega

def d3 (n:Nat) : Nat := (2*fourthPred n+5)/81
def oddPre3 (n:Nat) : Nat := 16*d3 n -8*2^(n-3)-(n-3)-5

theorem div81_factor (n:Nat) (hn:64≤n)
    (hres:n%162=64 ∨ n%162=107) :
    81*d3 n=2*fourthPred n+5 ∧ (d3 n)%2=1 := by
  have hm := fourth_div81 n hn hres
  have hd := Nat.mod_add_div (2*fourthPred n+5) 81
  have he : 81*d3 n=2*fourthPred n+5 := by
    dsimp [d3]
    omega
  constructor
  · exact he
  · omega

private theorem third_band_arith (n P R D : Nat)
    (hgrowth:1984*n+3300 ≤ 13*P)
    (hfactor:81*D+62*n+93=8*P)
    (hpow:P=8*R) :
    6*R+1 ≤ 8*D ∧ 8*D ≤ 8*R-1 := by
  omega

theorem third_band (n:Nat) (hn:64≤n)
    (hres:n%162=64 ∨ n%162=107) :
    6*2^(n-3)+1 ≤ 8*d3 n ∧ 8*d3 n≤8*2^(n-3)-1 := by
  have hg := n_growth n (by omega)
  have hf := div81_factor n hn hres
  have hu : fourthPred n+31*n+49=4*2^n := by
    dsimp [fourthPred]
    omega
  have hp : 2^n=8*2^(n-3) := by
    have he : 2^n=2^((n-3)+3):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at he
    omega
  have hfactor : 81*d3 n+62*n+93=8*2^n := by omega
  exact third_band_arith n (2^n) (2^(n-3)) (d3 n) hg hfactor hp

theorem n_small (n:Nat) (hn:10≤n) : n+10≤2^(n-3) := by
  have h : ∀ k:Nat, k+20≤2^(k+7) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+7=k+7+1 by omega,Nat.pow_succ]
      omega
  have he:n-3=(n-10)+7:=by omega
  rw [he]
  have hh:=h (n-10)
  omega

theorem pre3_identity (n R D:Nat) (hn:3≤n)
    (hsmall:n+10≤R) (hl:6*R+1≤8*D) :
    16*D=8*R+(16*D-8*R-(n-3)-5)+(n-3)+5 := by
  omega

/-- Source-complete exact odd inverse at valuation t=3, universally
    for both remaining mod162 index sectors. -/
theorem fourth_third_odd_parent (n:Nat) (hn:64≤n)
    (hres:n%162=64 ∨ n%162=107) :
    ResetParent (oddPre3 n) (fourthPred n) := by
  have hfac := div81_factor n hn hres
  have hb := third_band n hn hres
  have hsmall:=n_small n (by omega)
  have heq : 2*(8*d3 n)=8*2^(n-3)+oddPre3 n+(n-3)+5 := by
    have hh:=pre3_identity n (2^(n-3)) (d3 n) (by omega) hsmall hb.1
    dsimp [oddPre3]
    simpa only [show 2*(8*d3 n)=16*d3 n by omega] using hh
  have hout : 2*fourthPred n+5=3^(3+1)*d3 n := by
    have hthree:3^(3+1)=81:=by decide
    rw [hthree]
    exact hfac.1.symm
  exact Or.inr ⟨n-3,3,d3 n,hfac.2,by simpa using hb,hout,by simpa using heq⟩

private theorem third_lt_arith (n P R D:Nat) (hp:P=8*R)
    (hup:8*D≤8*R-1) (hR:1≤R) :
    16*D-8*R-(n-3)-5 < P := by
  omega

private theorem first_gt_arith (n P R D:Nat)
    (hg:257*n+500≤5*P)
    (heq:9*D+62*n+93=8*P)
    (hp:P=4*R) (hn:10≤n) :
    P < 4*D-8*R-(n-2)-5 := by
  omega

private theorem first_lt_arith (n P R D:Nat)
    (hp:P=4*R) (hu:2*D≤8*R-1) (hR:1≤R) :
    4*D-8*R-(n-2)-5 < 2*P := by
  omega

/-- Both exceptional classes have a genuine third inverse option at t=3;
    the completeness of the inverse grammar does not imply root reachability. -/
theorem fourth_has_three_parents (n:Nat) (hn:64≤n)
    (hres:n%162=64 ∨ n%162=107) :
    ∃ x y z, x≠y ∧ x≠z ∧ y≠z ∧
      ResetParent x (fourthPred n) ∧
      ResetParent y (fourthPred n) ∧
      ResetParent z (fourthPred n) := by
  have h18:n%18=10 ∨ n%18=17:=by omega
  have he := fourth_even_parent n (by omega)
  have ho := fourth_odd_parent n (by omega) h18
  have ht := fourth_third_odd_parent n hn hres
  have hb := third_band n hn hres
  have hb1 := odd_band n (by omega) h18
  have hg:=pos_growth n (by omega)
  have hf:=odd_factor n (by omega) h18
  have hf3:=div81_factor n hn hres
  have hp : 2^n=8*2^(n-3) := by
    have hh:2^n=2^((n-3)+3):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hthird_lt : oddPre3 n < 2^n := by
    have hpre:=third_lt_arith n (2^n) (2^(n-3)) (d3 n) hp hb.2 (Nat.one_le_pow _ _ (by decide))
    exact hpre
  have hfirst_gt : 2^n < oddPre n := by
    have hp4:2^n=4*2^(n-2):=by
      have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
      rw [Nat.pow_add] at hh
      omega
    have hf1 : 9*d n+62*n+93=8*2^n := by
      have hu:fourthPred n+31*n+49=4*2^n:=by
        dsimp [fourthPred]
        omega
      omega
    have hpre:=first_gt_arith n (2^n) (2^(n-2)) (d n) hg hf1 hp4 (by omega)
    exact hpre
  have hfirst_lt : oddPre n < 2*2^n := by
    have hp4:2^n=4*2^(n-2):=by
      have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
      rw [Nat.pow_add] at hh
      omega
    exact first_lt_arith n (2^n) (2^(n-2)) (d n) hp4 hb1.2
      (Nat.one_le_pow _ _ (by decide))
  have heven_gt : 3*2^n ≤ evenPre n := by
    have hlg:=fifth_growth n (by omega)
    dsimp [evenPre]
    omega
  refine ⟨oddPre3 n,oddPre n,evenPre n,?_,?_,?_,ht,ho,he⟩
  · omega
  · omega
  · omega

#print axioms fourth_div81
#print axioms fourth_third_odd_parent
#print axioms fourth_has_three_parents
end CascadeAgent10TripleFork
