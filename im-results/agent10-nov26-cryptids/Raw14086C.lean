import Raw14086D
import Raw14042Counter
namespace Raw14086
open BB6BlockFAR Raw140Orbit Raw140Extra Raw14086Local Raw140Double Raw14086Arithmetic
open Raw14042Counter (CTail T B cword ccarry counterCfg counterIter scanTwo scanTrip prep backAll two_shift)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] boundary run

def crank : CTail → Nat
  | .c31 => 0 | .c32 => 1 | .c315 => 2 | .c325 => 3 | .c3242 => 4 | .c35221 => 5

abbrev cn := Raw14042Counter.next
abbrev ct := Raw14042Counter.turn

theorem crank_lt (s : CTail) : crank s < 6 := by cases s <;> decide
theorem crank_next (s : CTail) : crank (cn s) = next (crank s) := by cases s <;> decide
theorem ccarry_rank (s : CTail) : ccarry s = carry (crank s) := by cases s <;> decide
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

theorem cPumpAll (p n : Nat) (Y : List Sym) (hp : 24 ≤ p) :
    R (boundary 0 true (U 3 p ++ [S 2]) (S 2::(T n ++ Y)))
      (boundary 0 true (U 3 (p+5*n) ++ [S 2]) (S 2::Y)) := by
  induction n generalizing p with
  | zero => exact Reach.refl M86 _
  | succ n ih =>
    have h0 : R (boundary 0 true (U 3 p ++ [S 2]) (S 2::(T (n+1) ++ Y)))
        (boundary 0 true (U 3 (p+5) ++ [S 2]) (S 2::(T n ++ Y))) := by
      simpa only [T,List.cons_append,show p-24+24=p by omega,show p-24+29=p+5 by omega] using
        rr (cPump (p-24) (T n ++ Y))
    simpa only [show p+5+5*n=p+5*(n+1) by omega] using Reach.trans h0 (ih (p+5) (by omega))

theorem terminalC (p : Nat) (s : CTail) (hp : 24 ≤ p) :
    R (cCfg p 0 s) (cfg (termC p (crank s))) := by
  cases s
  · have h0 : R (cCfg p 0 .c31) (D (p-2)) := by
      simpa only [cCfg,T,cword,D,List.nil_append,show p-24+24=p by omega,show p-24+22=p-2 by omega,
        U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc] using rr (cSeed (p-24))
    exact Reach.trans h0 (dReturn_sound (p-2) (by omega))
  · simpa only [cCfg,T,cword,crank,termC,cfg,A0,List.nil_append,
      show p-24+24=p by omega,show p-24+29=p+5 by omega] using rr (c32 (p-24))
  · simpa only [cCfg,T,cword,crank,termC,cfg,B0,List.nil_append,
      show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (c315 (p-24))
  · simpa only [cCfg,T,cword,crank,termC,cfg,A2,List.nil_append,
      show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (c325 (p-24))
  · simpa only [cCfg,T,cword,crank,termC,cfg,A2,List.nil_append,
      show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (c3242 (p-24))
  · simpa only [cCfg,T,cword,crank,termC,cfg,A0,List.nil_append,
      show p-24+24=p by omega,show p-24+31=p+7 by omega] using rr (c35221 (p-24))

theorem drainC (p n : Nat) (s : CTail) (hp : 24 ≤ p) :
    R (cCfg p n s) (cfg (termC (p+5*n) (crank s))) :=
  Reach.trans (cPumpAll p n _ hp) (terminalC _ s (by omega))

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

-- Input bank of two symbols has one surplus two when p is odd.
theorem cFront (p : Nat) (hp : 24 ≤ p) :
    Plus (A0 p) (boundary 1 false [] (U 2 (p+4) ++
      T (((ct (p-7) .c31).1)+ccarry (ct (p-7) .c31).2+ccarry (cn (ct (p-7) .c31).2)) ++
      cword (cn (cn (ct (p-7) .c31).2)))) := by
  let X := U 3 (p-7) ++ [S 2]
  have h0 := positive (seedCounter X) (by omega)
  have h0' : Plus (A0 p) (counterCfg 7 0 X .c31) := by
    have hp7 : U 3 p ++ [S 2] = U 3 7 ++ X := by
      dsimp only [X]
      rw [merge,show 7+(p-7)=p by omega]
    simpa only [A0,counterCfg,T,cword,X,hp7,U,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.append_assoc,List.nil_append] using h0
  have h1 := lift (counterIter (p-7) 7 0 [S 2] .c31)
  have h2 := lift (depleteC p (ct (p-7) .c31).1 (ct (p-7) .c31).2)
  simp only [show 7+(p-7)=p by omega,Nat.zero_add] at h1
  exact Plus.transR (Plus.transR h0' h1) h2

theorem cOdd (p n : Nat) (s : CTail) (hp : 24 ≤ p) (hn : 2 ≤ n) :
    R (boundary 0 true (U 3 p ++ [S 2]) (S 2::S 2::(T n ++ cword s)))
      (cCfg (p+11) (n+ccarry s-2) (cn s)) := by
  let X := U 6 (p+2) ++ [S 4]
  let z := n-1
  have hz : n=z+1 := by dsimp [z]; omega
  have h0 : R (boundary 0 true (U 3 p ++ [S 2]) (S 2::S 2::(T n ++ cword s)))
      (boundary 4 true (S 2::X) (S 3::S 2::S 2::(T z ++ cword s))) := by
    rw [hz]
    simpa only [X,T,List.cons_append,show p-24+24=p by omega,show p-24+26=p+2 by omega] using
      rr (cOddStart (p-24) (T z ++ cword s))
  have h1 := lift (scanTwo 2 X (T z ++ cword s))
  have h2 := lift (scanTrip z (U 6 2 ++ X) (cword s))
  have h3 := lift (prep s (B z ++ U 6 2 ++ X))
  have h4 := lift (backAll z 2 X s)
  let w := n+ccarry s-2
  have hw : z+ccarry s=w+1 := by dsimp [z,w]; omega
  rw [hw] at h4
  have h5 := rr (cOddFinish (p-24) (T w ++ cword (cn s)))
  have h6 := lift (⟨_,Raw14042CounterLocal.twoPump (p+7) (T w ++ cword (cn s))⟩ :
      Reach base _ _)
  simp only [X,U,T,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1 h2 h3 h4
  have h := Reach.trans (Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3) h4
  have h5' : R (boundary 1 false X (U 2 4 ++ T (w+1) ++ cword (cn s)))
      (boundary 0 true (U 3 (p+7) ++ [S 2]) (U 2 3 ++ T w ++ cword (cn s))) := by
    simpa only [X,T,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,
      show p-24+26=p+2 by omega,show p-24+31=p+7 by omega] using h5
  have h' := Reach.trans h h5'
  simpa only [cCfg,w,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,
    show p+7+4=p+11 by omega] using Reach.trans h' h6

theorem a0Return (p : Nat) (hp : 24 ≤ p) : Plus (A0 p) (cfg (ret .a0 p)) := by
  let s := (ct (p-7) .c31).2
  let n := (ct (p-7) .c31).1 + ccarry s + ccarry (cn s)
  let t := cn (cn s)
  have hb := ct_balance (p-7) .c31
  have hb0 : 6*(ct (p-7) .c31).1 + crank s = p-7 := by simpa only [s,crank,Nat.add_zero] using hb
  have hb1 := cbalance s
  have hb2 := cbalance (cn s)
  have ht := crank_lt t
  have hbal : 6*n+crank t=p-5 := by dsimp [n,t]; omega
  have hn : n=(p-5)/6 := by omega
  have hs : crank t=(p-5)%6 := by omega
  have hn3 : 3 ≤ n := by omega
  let Y := T n ++ cword t
  have h0 : Plus (A0 p) (boundary 1 false [] (U 2 (p+4) ++ Y)) := by
    simpa only [Y,n,t,s,List.append_assoc] using cFront p hp
  have h1 := rb (Raw14042CounterLocal.initTwos (U 2 (p+2) ++ Y))
  have h1' : R (boundary 1 false [] (U 2 (p+4) ++ Y))
      (boundary 0 true (U 3 2 ++ [S 2]) (U 2 (p+3) ++ Y)) := by
    simpa only [Raw140VariantTransfer.Mbase,show p+4=(p+2)+1+1 by omega,show p+3=(p+2)+1 by omega,
      U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using h1
  by_cases he : p%2=0
  · let j := (p+2)/2
    have h2 := lift (twoPumpAll 2 j 0 Y)
    have h2' : R (boundary 0 true (U 3 2 ++ [S 2]) (U 2 (p+3) ++ Y))
        (cCfg (2*p+6) n t) := by
      simpa only [cCfg,Y,j,show 2*((p+2)/2)+0+1=p+3 by omega,
        show 2+4*((p+2)/2)=2*p+6 by omega,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using h2
    have h3 := drainC (2*p+6) n t (by omega)
    simpa only [ret,he,ite_true,hn,hs] using Plus.transR (Plus.transR (Plus.transR h0 h1') h2') h3
  · let j := (p+1)/2
    have h2 := lift (twoPumpAll 2 j 1 Y)
    have h2' : R (boundary 0 true (U 3 2 ++ [S 2]) (U 2 (p+3) ++ Y))
        (boundary 0 true (U 3 (2*p+4) ++ [S 2]) (S 2::S 2::Y)) := by
      simpa only [j,show 2*((p+1)/2)+1+1=p+3 by omega,show 2+4*((p+1)/2)=2*p+4 by omega,
        U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using h2
    have h3 := cOdd (2*p+4) n t (by omega) (by omega)
    have h4 := drainC (2*p+15) (n+ccarry t-2) (cn t) (by omega)
    have h := Plus.transR (Plus.transR (Plus.transR h0 h1') h2') (by simpa only [Y,show 2*p+4+11=2*p+15 by omega] using Reach.trans h3 h4)
    simpa only [ret,he,ite_false,crank_next,ccarry_rank,hn,hs] using h

#print axioms depleteC
#print axioms a0Return
end Raw14086
