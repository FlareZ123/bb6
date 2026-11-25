import ThinGatewayCounted
import OrdinaryClock
import Lean
set_option maxHeartbeats 2000000
namespace BB6.Agent12CountedOrdinary
open BB6CLine BB6.Agent47ThinCounted

def D (h k : Nat) : Nat := 2*h*h+(4*k+7)*h

theorem sweep_counted (h A k C : Nat) (hC : 3≤C) :
    Path h (D h k) (A+h,k,C+h) (A,k+h,C) := by
  induction h generalizing k with
  | zero => simp [D]; exact Path.nil _
  | succ h ih =>
    have he : C+(h+1)=(C+h-3)+4 := by omega
    have ha : A+(h+1)=(A+h)+1 := by omega
    have hs : nextC (A+(h+1),k,C+(h+1))=some (A+h,k+1,C+h) := by
      rw [he,ha]; simp only [nextC,Option.some.injEq,Prod.mk.injEq,true_and]; omega
    have hw : weight (A+(h+1),k,C+(h+1))=4*k+9 := by rw [he,ha]; rfl
    have hh := Path.cons hs (ih (k+1))
    rw [hw,show k+1+h=k+(h+1) by omega] at hh
    have hc : 4*k+9+D h (k+1)=D (h+1) k := by simp [D,Nat.add_mul,Nat.mul_add]; omega
    rwa [hc] at hh

theorem finish3 (a k : Nat) : Path 2 14 (a,k,3) (a,k+3,0) := by
  have h1 : nextC (a,k,3)=some (a,k+2,1) := rfl
  have h2 : nextC (a,k+2,1)=some (a,k+3,0) := by simp [nextC]
  exact Path.cons h1 (Path.cons h2 (Path.nil _))

-- Odd/even continuation costs, in the same shifted variable as ClosedBounce.
def cycleCost (k : Nat) : Nat := if k%2=0 then 8*k*k+51*k+59 else 8*k*k+43*k+52

theorem odd_cycle (k c : Nat) (hk : k%2=1) (hc : 2*k+6<c) :
    Path (2*k+4) (cycleCost k) (0,k,c) (0,2*k+3,c-(2*k+3)) := by
  have he : c=c-4+4 := by omega
  have hn : nextC (0,k,c)=some (2*k+3,0,c) := by
    conv => lhs; rw [he]
    simp only [nextC,show ¬k%2=0 by omega,ite_false,Option.some.injEq,Prod.mk.injEq]
    exact ⟨by omega,trivial,he.symm⟩
  have hw : weight (0,k,c)=5*k+13 := by rw [he]; simp only [weight,show ¬k%2=0 by omega,ite_false]; omega
  have hp := sweep_counted (2*k+3) 0 0 (c-(2*k+3)) (by omega)
  simp only [Nat.zero_add] at hp
  rw [show c-(2*k+3)+(2*k+3)=c by omega] at hp
  have hh := Path.cons hn hp
  rw [hw] at hh
  have hcost : 5*k+13+D (2*k+3) 0=cycleCost k := by
    simp [cycleCost,show ¬k%2=0 by omega,D]; grind
  rwa [hcost,show 2*k+3+1=2*k+4 by omega] at hh

theorem even_cycle (k c : Nat) (hk : k%2=0) (hc : 2*k+8<c) :
    Path (2*k+3) (cycleCost k) (0,k,c) (0,2*k+4,c-(2*k+5)) := by
  have he : c=c-4+4 := by omega
  have hn : nextC (0,k,c)=some (2*k+2,2,c-3) := by
    rw [he]; simp only [nextC,hk,ite_true,Option.some.injEq,Prod.mk.injEq,true_and]; omega
  have hw : weight (0,k,c)=5*k+21 := by rw [he]; simp only [weight,hk,ite_true]; omega
  have hp := sweep_counted (2*k+2) 0 2 (c-(2*k+5)) (by omega)
  simp only [Nat.zero_add] at hp
  rw [show c-(2*k+5)+(2*k+2)=c-3 by omega,show 2+(2*k+2)=2*k+4 by omega] at hp
  have hh := Path.cons hn hp
  rw [hw] at hh
  have hcost : 5*k+21+D (2*k+2) 2=cycleCost k := by
    simp [cycleCost,hk,D]; grind
  rwa [hcost,show 2*k+2+1=2*k+3 by omega] at hh

theorem odd_exit (k c : Nat) (hk : k%2=1) (hc : 4≤c) (he : c≤2*k+6) :
    ∃ w, Path c w (0,k,c) (2*k+6-c,c,0) ∧
      (w:Int)=2*(c:Int)^2-5*c+5*(k+3:Nat)+9 := by
  have h4 : c=c-4+4 := by omega
  have hn : nextC (0,k,c)=some (2*k+3,0,c) := by
    conv => lhs; rw [h4]
    simp only [nextC,show ¬k%2=0 by omega,ite_false,Option.some.injEq,Prod.mk.injEq]
    exact ⟨by omega,trivial,h4.symm⟩
  have hw : weight (0,k,c)=5*k+13 := by rw [h4]; simp only [weight,show ¬k%2=0 by omega,ite_false]; omega
  have hp := sweep_counted (c-3) (2*k+6-c) 0 3 (by decide)
  rw [show 2*k+6-c+(c-3)=2*k+3 by omega,show 3+(c-3)=c by omega,Nat.zero_add] at hp
  have hh := (Path.cons hn hp).append (finish3 (2*k+6-c) (c-3))
  rw [hw,show c-3+1+2=c by omega] at hh
  refine ⟨_,hh,?_⟩
  simp only [D,Int.natCast_add,Int.natCast_mul,Int.natCast_sub (show 3≤c by omega)]
  grind

theorem even_exit (k c : Nat) (hk : k%2=0) (hc : 6≤c) (he : c≤2*k+8) :
    ∃ w, Path (c-3) w (0,k,c) (2*k+8-c,c-1,0) ∧
      (w:Int)=2*(c:Int)^2-9*c+5*(k+4:Nat)-3 := by
  have h4 : c=c-4+4 := by omega
  have hn : nextC (0,k,c)=some (2*k+2,2,c-3) := by
    rw [h4]; simp only [nextC,hk,ite_true,Option.some.injEq,Prod.mk.injEq,true_and]; omega
  have hw : weight (0,k,c)=5*k+21 := by rw [h4]; simp only [weight,hk,ite_true]; omega
  have hp := sweep_counted (c-6) (2*k+8-c) 2 3 (by decide)
  rw [show 2*k+8-c+(c-6)=2*k+2 by omega,show 3+(c-6)=c-3 by omega] at hp
  have hh := (Path.cons hn hp).append (finish3 (2*k+8-c) (2+(c-6)))
  rw [hw,show c-6+1+2=c-3 by omega,show 2+(c-6)+3=c-1 by omega] at hh
  refine ⟨_,hh,?_⟩
  simp only [D,Int.natCast_add,Int.natCast_mul,Int.natCast_sub (show 6≤c by omega)]
  grind

-- Both parity cases share a single polynomial after shifting by b=3+o.
theorem cycle_counted (k c o : Nat) (ho : o≤1) (hk : k%2+o=1)
    (hc : 2*k+6+2*o<c) :
    ∃ n w, Path n w (0,k,c) (0,2*k+3+o,c-(2*k+3+2*o)) ∧
      n+o=2*k+4 ∧
      (w:Int)=8*((k:Int)+3+o)^2-(5+8*(o:Int))*((k:Int)+3+o)-(5+12*(o:Int)) := by
  have h : o=0 ∨ o=1 := by omega
  rcases h with rfl|rfl
  · have hpath := odd_cycle k c (by omega) (by omega)
    refine ⟨_,_,by simpa using hpath,by omega,?_⟩
    simp [cycleCost,show ¬k%2=0 by omega]
    grind
  · have hpath := even_cycle k c (by omega) (by omega)
    refine ⟨_,_,by simpa [Nat.add_assoc] using hpath,by omega,?_⟩
    simp [cycleCost,show k%2=0 by omega]
    grind

/-- A closed count of an entire bounce chain. The final high counter C≥4
    ensures every preceding continuation was legal, without checking them. -/
theorem chain_counted (n k c o K C : Nat) (ho : o≤1) (hk : k%2+o=1)
    (hK : K+3+o=2^n*(k+3+o)) (hC : C+2*K=c+2*k+3*n) (hmin : 4≤C) :
    ∃ t w, Path t w (0,k,c) (0,K,C) ∧
      t+2*k+(2+3*o)*n=2*K ∧
      3*(w:Int)=8*(((K:Int)+3+o)^2-((k:Int)+3+o)^2) -
        3*(5+8*(o:Int))*((K:Int)-k)-3*(5+12*(o:Int))*n := by
  induction n generalizing K C with
  | zero =>
    simp at hK hC
    have h1 : K=k := by omega
    subst K
    have h2 : C=c := by omega
    subst C
    exact ⟨0,0,Path.nil _,by simp,by simp⟩
  | succ n ih =>
    let L := 2^n*(k+3+o)-(3+o)
    have hpos : 1≤2^n := Nat.pow_pos (by decide)
    have hge := Nat.mul_le_mul_right (k+3+o) hpos
    have hL : L+3+o=2^n*(k+3+o) := by dsimp [L]; simp at hge; omega
    have hKL : K=2*L+3+o := by rw [Nat.pow_succ,Nat.mul_comm (2^n) 2,Nat.mul_assoc,←hL] at hK; omega
    have hpar : L%2+o=1 := by
      cases n with
      | zero => simp at hL; omega
      | succ n =>
        rw [Nat.pow_succ,Nat.mul_comm (2^n) 2,Nat.mul_assoc] at hL
        omega
    let E := C+2*L+3+2*o
    have hEL : E+2*L=c+2*k+3*n := by dsimp [E]; omega
    obtain ⟨t,w,hp,ht,hw⟩ := ih L E hL hEL (by dsimp [E]; omega)
    obtain ⟨u,v,hq,hu,hv⟩ := cycle_counted L E o ho hpar (by dsimp [E]; omega)
    have hsub : E-(2*L+3+2*o)=C := by dsimp [E]; omega
    rw [←hKL,hsub] at hq
    refine ⟨t+u,w+v,hp.append hq,?_,?_⟩
    · simp [Nat.mul_succ] at *; omega
    · have hI : (K:Int)=2*(L:Int)+3+o := by exact_mod_cast hKL
      push_cast
      grind


theorem direct_counted (a k : Nat) (ha : 2≤a) (hk : 1≤k) (h : 2*k≤a) :
    Path (2*k+1) (8*k*k+8*k+4) (a,k,0) (a-2*k,2*k+2,0) := by
  obtain ⟨A,rfl⟩ : ∃ A,a=A+2 := ⟨a-2,by omega⟩
  have hn : nextC (A+2,k,0)=some (A,1,2*k+1) := rfl
  have hw : weight (A+2,k,0)=2*k+4 := rfl
  have hp := sweep_counted (2*k-2) (A+2-2*k) 1 3 (by decide)
  rw [show A+2-2*k+(2*k-2)=A by omega,show 3+(2*k-2)=2*k+1 by omega] at hp
  have hh := (Path.cons hn hp).append (finish3 (A+2-2*k) (1+(2*k-2)))
  rw [hw,show 2*k-2+1+2=2*k+1 by omega,show 1+(2*k-2)+3=2*k+2 by omega] at hh
  have hc : 2*k+4+D (2*k-2) 1+14=8*k*k+8*k+4 := by
    obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
    rw [show 2*(j+1)-2=2*j by omega]
    simp [D]; grind
  rwa [hc] at hh

theorem high_entry (a k : Nat) (ha : 2≤a) (h : a<2*k) :
    ∃ w, Path (a-1) w (a,k,0) (0,a-1,2*k-a+3) ∧
      (w:Int)=2*(a:Int)^2+3*a+2*k-10 := by
  obtain ⟨A,rfl⟩ : ∃ A,a=A+2 := ⟨a-2,by omega⟩
  have hn : nextC (A+2,k,0)=some (A,1,2*k+1) := rfl
  have hw : weight (A+2,k,0)=2*k+4 := rfl
  have hp := sweep_counted A 0 1 (2*k-(A+2)+3) (by omega)
  simp only [Nat.zero_add] at hp
  rw [show 2*k-(A+2)+3+A=2*k+1 by omega,show 1+A=A+2-1 by omega] at hp
  have hh := Path.cons hn hp
  rw [hw,show A+1=A+2-1 by omega] at hh
  refine ⟨_,hh,?_⟩
  simp [D]; grind

-- This is the weighted analogue of WordBlock.EdgeLaw: the same endpoint
-- data and inequalities prove the literal weighted CLine path.
open BB6.Agent12Clock

theorem ordinary_edge (a k x y r : Nat) (hr : 1≤r) (ha : 2≤a) (hk : 1≤k)
    (hy : 8≤y) (hb : if r=1 then 2*k≤a else a<2*k)
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
    have hC : 8≤C := by dsimp [C]; omega
    have hpar : (a-1)%2+o=1 := by dsimp [o]; omega
    have hkpar : K%2+o=1 := by
      by_cases hn : n=0
      · rw [hn,Nat.pow_zero,Nat.one_mul] at hK; dsimp [B] at hK; omega
      · obtain ⟨j,hj⟩ : ∃ j,n=j+1 := ⟨n-1,by omega⟩
        rw [hj,Nat.pow_succ,Nat.mul_comm (2^j) 2,Nat.mul_assoc] at hK; omega
    obtain ⟨v,hv,hvw⟩ := high_entry a k ha hb
    obtain ⟨t,w,hp,ht,hw⟩ := chain_counted n (a-1) (2*k-a+3) o K C ho hpar (by rw [hK]; congr 1; dsimp [B]; omega) hKC (by omega)
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

end BB6.Agent12CountedOrdinary
