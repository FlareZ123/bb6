import Raw14042Counter
namespace Raw14042CGeneral
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042Counter (CTail T B cword ccarry counterCfg counterIter scanTwo scanTrip prep backAll two_shift)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] boundary run
abbrev R := Reach M42
-- Common counter lemmas factored from Raw14086C; they use only base.
def crank : CTail → Nat
  | .c31 => 0 | .c32 => 1 | .c315 => 2 | .c325 => 3 | .c3242 => 4 | .c35221 => 5

abbrev cn := Raw14042Counter.next
abbrev ct := Raw14042Counter.turn

theorem crank_lt (s : CTail) : crank s < 6 := by cases s <;> decide
theorem cbalance (s : CTail) : 6*ccarry s + crank (cn s) = crank s+1 := by cases s <;> decide
theorem ct_balance (k : Nat) (s : CTail) :
    6*(ct k s).1 + crank (ct k s).2 = k+crank s := by
  induction k generalizing s with
  | zero => simp [ct,Raw14042Counter.turn]
  | succ k ih =>
    have h := ih (cn s)
    have h' := cbalance s
    change 6*(ccarry s + (ct k (cn s)).1) + crank (ct k (cn s)).2 = k+1+crank s
    omega

-- Depletion of the marker costs two suffix rotations, and leaves an even bank.
theorem depleteC (m n : Nat) (s : CTail) :
    Reach base (counterCfg m n [S 2] s)
      (boundary 1 false [] (U 2 (m+4) ++ T (n+ccarry s+ccarry (cn s)) ++ cword (cn (cn s)))) := by
  let X : List Sym := [S 7,S 2]
  let Y := T (n+ccarry s) ++ cword (cn s)
  have h0 := scanTwo m X (T n ++ cword s)
  have h1 := scanTrip n (U 6 m ++ X) (cword s)
  have h2 := prep s (B n ++ U 6 m ++ X)
  have h3 := backAll n m X s
  have h4 := Raw14042CounterLocal.finishZero (U 2 m ++ Y)
  simp only [List.append_assoc] at h0 h1 h2 h3
  have h := Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3
  rw [two_shift] at h
  have h5 : Reach base (counterCfg m n [S 2] s)
      (boundary 4 true [S 2,S 6] (S 3::(U 2 (m+1) ++ Y))) := by
    simpa only [counterCfg,X,Y,U,List.replicate_succ,List.cons_append,List.append_assoc] using
      Reach.trans h (⟨_,h4⟩ : Reach base _ _)
  have h6 := scanTwo (m+1) [S 6] Y
  have h7 := scanTrip (n+ccarry s) (U 6 (m+1) ++ [S 6]) (cword (cn s))
  have h8 := prep (cn s) (B (n+ccarry s) ++ U 6 (m+1) ++ [S 6])
  have h9 := backAll (n+ccarry s) (m+1) [S 6] (cn s)
  have h10 := sweepL base 1 (S 6) (S 2) 3 1 []
      (U 2 (m+1) ++ S 2::S 2::(T (n+ccarry s+ccarry (cn s)) ++ cword (cn (cn s)))) (by rfl)
  simp only [Y,List.append_assoc] at h5 h6 h7 h8 h9 h10
  have h11 := Reach.trans (Reach.trans (Reach.trans (Reach.trans h5 h6) h7) h8) h9
  simpa only [ite_false,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
    List.append_assoc,rep_cons,show m+4=(m+1)+3 by omega] using Reach.trans h11 (⟨_,h10⟩ : Reach base _ _)

def cCfg (p n : Nat) (s : CTail) : Prim :=
  boundary 0 true (U 3 p ++ [S 2]) (S 2::(T n ++ cword s))

theorem twoPumpAll (p j b : Nat) (Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ [S 2]) (U 2 (2*j+b+1) ++ Y))
      (boundary 0 true (U 3 (p+4*j) ++ [S 2]) (U 2 (b+1) ++ Y)) := by
  induction j generalizing p with
  | zero => simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] using Reach.refl base _
  | succ j ih =>
    have h0 := Raw14042CounterLocal.twoPump p (U 2 (2*j+b) ++ Y)
    have h0' : Reach base
        (boundary 0 true (U 3 p ++ [S 2]) (U 2 (2*(j+1)+b+1) ++ Y))
        (boundary 0 true (U 3 (p+4) ++ [S 2]) (U 2 (2*j+b+1) ++ Y)) := by
      simpa only [Raw140VariantTransfer.Mbase,
        show 2*(j+1)+b+1=(2*j+b)+1+1+1 by omega,
        U,List.replicate_succ,List.cons_append,List.append_assoc] using
        (show Reach base _ _ from ⟨_,h0⟩)
    simpa only [show p+4+4*j=p+4*(j+1) by omega] using Reach.trans h0' (ih (p+4))

theorem evenReturn (k m : Nat) (s : CTail) (he : (k+m)%2=0) :
    ∃ t : CTail, crank t=(k+crank s+2)%6 ∧
      R (counterCfg m 0 (U 3 k ++ [S 2]) s) (cCfg (2*(k+m)+6) ((k+crank s+2)/6) t) := by
  let n := (ct k s).1
  let u := (ct k s).2
  let t := cn (cn u)
  let z := n+ccarry u+ccarry (cn u)
  let p := k+m
  let Y := T z ++ cword t
  have hb := ct_balance k s
  have hb1 := cbalance u
  have hb2 := cbalance (cn u)
  have hlt := crank_lt t
  have hbal : 6*z+crank t=k+crank s+2 := by dsimp [z,n,t,u] at *; omega
  have hn : z=(k+crank s+2)/6 := by omega
  have hr : crank t=(k+crank s+2)%6 := by omega
  have h0 := counterIter k m 0 [S 2] s
  have h0' : Reach base (counterCfg m 0 (U 3 k ++ [S 2]) s) (counterCfg p n [S 2] u) := by
    simpa only [p,n,u,Nat.add_comm m k,Nat.zero_add] using h0
  have h1 := depleteC p n u
  have h01 : Reach base (counterCfg m 0 (U 3 k ++ [S 2]) s)
      (boundary 1 false [] (U 2 (p+4) ++ Y)) := by
    simpa only [p,n,u,Y,z,t,Nat.add_comm m k,Nat.zero_add,List.append_assoc] using Reach.trans h0' h1
  have h2 := Raw14042CounterLocal.initTwos (U 2 (p+2) ++ Y)
  have h2' : Reach base (boundary 1 false [] (U 2 (p+4) ++ Y))
      (boundary 0 true (U 3 2 ++ [S 2]) (U 2 (p+3) ++ Y)) := by
    simpa only [Raw140VariantTransfer.Mbase,show p+4=(p+2)+1+1 by omega,show p+3=(p+2)+1 by omega,
      U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using (show Reach base _ _ from ⟨_,h2⟩)
  let j := (p+2)/2
  have hj : 2*j=p+2 := by dsimp [j,p]; omega
  have hm : 2+4*j=2*p+6 := by omega
  have h3 := twoPumpAll 2 j 0 Y
  have h3' : Reach base (boundary 0 true (U 3 2 ++ [S 2]) (U 2 (p+3) ++ Y)) (cCfg (2*p+6) z t) := by
    simpa only [cCfg,Y,hj,hm,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using h3
  exact ⟨t,hr,by simpa only [p,hn] using Reach.ext (M := M42) (fill_extends _ _) (Reach.trans (Reach.trans h01 h2') h3')⟩
#print axioms evenReturn
end Raw14042CGeneral
