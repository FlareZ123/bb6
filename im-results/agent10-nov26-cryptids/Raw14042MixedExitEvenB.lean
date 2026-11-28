import Raw14042MixedExitOdd
import Raw14042BEvenLocal
import Raw14042Word
namespace Raw14042MixedExitEvenB
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042Counter (CTail T cword ccarry next)
open Raw14042Word Raw14042BEvenLocal Raw14042CGeneral
open Raw14042DExitTail (A absorb)
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
abbrev RR := Reach base
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : RR c d := ⟨k,h⟩

theorem bEvenFront (k : Nat) (Y : List Sym) :
    RR (boundary 1 true [S 5] (S 2::S 2::(U 1 (2*k+3) ++ S 2::S 3::(U 2 (2*k+1) ++ Y))))
      (A (4*k+7) (S 0::S 2::S 3::(U 2 (2*k+1) ++ Y))) := by
  let Z := S 2::S 3::(U 2 (2*k+1) ++ Y)
  have h0 := rr (Raw14042MixedExitLocal.bInit (U 1 (2*k+2) ++ Z))
  have h1 := absorb (k+1) 3 Z
  have h0' : RR (boundary 1 true [S 5] (S 2::S 2::(U 1 (2*k+3) ++ Z))) (A 3 (S 0::(U 1 (2*(k+1)) ++ Z))) := by
    simpa only [A,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,show 2*(k+1)=2*k+2 by omega] using h0
  simpa only [Z,show 3+4*(k+1)=4*k+7 by omega] using Reach.trans h0' h1

-- Framed conversion of 023 to the arbitrary-word counter, with one rotation.
theorem bEvenCounter (p : Nat) (W : List Bool) (s : CTail) :
    RR (A (p+2) (S 0::S 2::S 3::(w23 W ++ cword s)))
      (Cfg (U 3 p ++ [S 2]) (true::true::W ++ trip23 (ccarry s)) (next s)) := by
  have h0 := rr (bEvenStart (p+2) (w23 W ++ cword s))
  have h1 := Raw14042Word.bounce W (S 2::(U 3 (p+2) ++ [S 2])) s
  have h2 := rr (bEvenMark (U 3 p ++ [S 2]) (w23 W ++ T (ccarry s) ++ cword (next s)))
  have h01 := Reach.trans h0 h1
  have h2' : RR (boundary 1 false (S 2::(U 3 (p+2) ++ [S 2])) (S 2::S 2::(w23 W ++ T (ccarry s) ++ cword (next s))))
      (Cfg (U 3 p ++ [S 2]) (true::true::W ++ trip23 (ccarry s)) (next s)) := by
    simpa only [Cfg,U,List.replicate_succ,List.cons_append,w23,w23_append,word_trip23,ite_true,List.append_assoc,show p+2=p+1+1 by omega] using h2
  exact Reach.trans h01 h2'

-- After the main counter is exhausted, the suffix rank is exactly five.
theorem bEvenDeplete (k n : Nat) (s : CTail) (hb : 6*n+crank s=2*k+3) :
    RR (A (4*k+7) (S 0::S 2::S 3::(U 2 (2*k+1) ++ T n ++ cword s)))
      (boundary 1 false [] (U 2 (4*k+9) ++ S 3::S 3::(U 2 (2*k+1) ++ T (k+1) ++ cword .c35221))) := by
  let W := List.replicate (2*k+1) false ++ trip23 n
  let V := true::true::W ++ trip23 (ccarry s)
  let j := 4*k+5
  let u := (Raw14042Counter.turn j (next s)).2
  let v := (Raw14042Counter.turn 2 u).2
  have h0 := bEvenCounter j W s
  have h1 := Raw14042Word.iter j [S 2] V (next s)
  have h2 := Raw14042Word.deplete (List.replicate j false ++ V ++ trip23 (Raw14042Counter.turn j (next s)).1) u
  have hb0 : 6*ccarry s+crank (next s)=crank s+1 := cbalance s
  have hb1 : 6*(Raw14042Counter.turn j (next s)).1+crank u=j+crank (next s) := ct_balance j (next s)
  have hb2 : 6*(Raw14042Counter.turn 2 u).1+crank v=2+crank u := ct_balance 2 u
  have hlt := crank_lt v
  let N := n+ccarry s+(Raw14042Counter.turn j (next s)).1+(Raw14042Counter.turn 2 u).1
  have hbal : 6*N+crank v=2*k+6+j := by
    dsimp only [N]
    omega
  have hj : 2*k+6+j=6*k+11 := by dsimp [j]; omega
  rw [hj] at hbal
  have hN : N=k+1 := by omega
  have hr : crank v=5 := by omega
  have ht : v=.c35221 := by cases hv : v <;> simp_all [crank]
  have h01 := Reach.trans h0 h1
  have h := Reach.trans h01 h2
  have hw : List.replicate j false ++ V ++ trip23 (Raw14042Counter.turn j (next s)).1 ++ trip23 (Raw14042Counter.turn 2 u).1 =
      List.replicate j false ++ true::true::(List.replicate (2*k+1) false ++ trip23 (k+1)) := by
    simpa only [V,W,List.cons_append,List.append_assoc,← trip23_add,N,hN]
  have he : w23 (List.replicate j false ++ V ++ trip23 (Raw14042Counter.turn j (next s)).1) ++ T (Raw14042Counter.turn 2 u).1 =
      U 2 j ++ S 3::S 3::(U 2 (2*k+1) ++ T (k+1)) := by
    have h' := congrArg w23 hw
    simpa only [w23_append,w23_two,word_trip23,w23,ite_true,List.cons_append,List.append_assoc] using h'
  have h' : RR (A (j+2) (S 0::S 2::S 3::(w23 W ++ cword s)))
      (boundary 1 false [] (S 2::S 2::S 2::S 2::(U 2 j ++ S 3::S 3::(U 2 (2*k+1) ++ T (k+1) ++ cword .c35221)))) := by
    have hlist : S 2::S 2::S 2::S 2::(w23 (List.replicate j false ++ V ++ trip23 (Raw14042Counter.turn j (next s)).1) ++ T (Raw14042Counter.turn 2 u).1 ++ cword v) =
        S 2::S 2::S 2::S 2::(U 2 j ++ S 3::S 3::(U 2 (2*k+1) ++ T (k+1) ++ cword .c35221)) := by
      calc
        _ = S 2::S 2::S 2::S 2::((U 2 j ++ S 3::S 3::(U 2 (2*k+1) ++ T (k+1))) ++ cword v) := congrArg (fun L : List Sym => S 2::S 2::S 2::S 2::(L ++ cword v)) he
        _ = _ := by rw [ht]; simp only [List.cons_append,List.append_assoc]
    rw [← hlist]
    exact h
  have hw0 : w23 W = U 2 (2*k+1) ++ T n := by
    simp only [W,w23_append,w23_two,word_trip23]
  rw [hw0] at h'
  simpa only [j,show 4*k+5+2=4*k+7 by omega,U,List.replicate_succ,List.cons_append,List.append_assoc,
    show 4*k+9=4*k+5+1+1+1+1 by omega] using h'

-- An arbitrary word bounce from A with two leading twos, followed by
-- conversion of the homogeneous six bank back to BL.
theorem bounceA (p : Nat) (W : List Bool) (s : CTail) :
    RR (A p (S 2::S 2::S 3::(w23 W ++ cword s)))
      (boundary 1 false [S 4] (U 2 (p+4) ++ w23 W ++ T (ccarry s) ++ cword (next s))) := by
  let Y := w23 W ++ T (ccarry s) ++ cword (next s)
  have h0 := rr (bBounceSeed p (w23 W ++ cword s))
  have h1 := Raw14042Word.bounce W (U 6 (p+2) ++ [S 4]) s
  have h2 := sweepL base 1 (S 6) (S 2) 3 (p+2) [S 4] (S 2::S 2::Y) (by rfl)
  have h2' : RR (boundary 1 false (U 6 (p+2) ++ [S 4]) (S 2::S 2::Y))
      (boundary 1 false [S 4] (U 2 (p+4) ++ Y)) := by
    have e : U 2 (p+4) ++ Y = U 2 (p+2) ++ S 2::S 2::Y := by
      rw [show p+4=(p+2)+2 by omega,Raw14042DExitTail.ua]
      simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc]
    rw [e]
    exact rr h2
  simpa only [Y,List.append_assoc] using Reach.trans (Reach.trans h0 h1) h2'

theorem bEvenFinish (k : Nat) :
    RR (boundary 1 false [] (U 2 (4*k+9) ++ S 3::S 3::(U 2 (2*k+1) ++ T (k+1) ++ cword .c35221)))
      (cCfg (12*k+30) k .c32) := by
  let Y := S 3::S 3::(U 2 (2*k+1) ++ T (k+1) ++ cword .c35221)
  have h0 := rr (Raw14042CounterLocal.initTwos (U 2 (4*k+7) ++ Y))
  have h1 := twoPumpAll 2 (2*k+3) 1 Y
  have h01 : RR (boundary 1 false [] (U 2 (4*k+9) ++ Y)) (A (8*k+14) (S 2::S 2::Y)) := by
    have h0' : RR (boundary 1 false [] (U 2 (4*k+9) ++ Y)) (A 2 (U 2 (4*k+8) ++ Y)) := by
      simpa only [A,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,show 4*k+9=4*k+7+1+1 by omega,show 4*k+8=4*k+7+1 by omega] using h0
    rw [show 2*(2*k+3)+1+1=4*k+8 by omega] at h1
    simpa only [A,show 2+4*(2*k+3)=8*k+14 by omega,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append] using Reach.trans h0' h1
  let W := true::(List.replicate (2*k+1) false ++ trip23 (k+1))
  have h2 := bounceA (8*k+14) W .c35221
  have h2' : RR (A (8*k+14) (S 2::S 2::Y)) (boundary 1 false [S 4] (U 2 (8*k+18) ++ S 3::(U 2 (2*k+1) ++ T (k+2) ++ cword .c31))) := by
    simpa only [Y,W,w23,w23_append,w23_two,word_trip23,ite_true,ccarry,next,List.cons_append,List.append_assoc,← Raw14042Counter.Tadd] using h2
  have h3 := rr (bBounceExit (8*k+18) (U 2 (2*k+1) ++ T (k+2) ++ cword .c31))
  have h4 := twoPumpAll (8*k+19) k 1 (T (k+2) ++ cword .c31)
  have h34 : RR (boundary 1 false [S 4] (U 2 (8*k+18) ++ S 3::(U 2 (2*k+1) ++ T (k+2) ++ cword .c31))) (A (12*k+19) (S 2::S 2::(T (k+2) ++ cword .c31))) := by
    have h3' : RR (boundary 1 false [S 4] (U 2 (8*k+18) ++ S 3::(U 2 (2*k+1) ++ T (k+2) ++ cword .c31))) (A (8*k+19) (U 2 (2*k+2) ++ T (k+2) ++ cword .c31)) := by
      simpa only [A,U,List.replicate_succ,List.cons_append,List.append_assoc] using h3
    rw [show 2*k+1+1=2*k+2 by omega] at h4
    simp only [List.append_assoc] at h3'
    simpa only [A,show 8*k+19+4*k=12*k+19 by omega,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,List.append_assoc] using Reach.trans h3' h4
  let V := false::false::trip23 (k+1)
  have h5 := bounceA (12*k+19) V .c31
  have h5' : RR (A (12*k+19) (S 2::S 2::(T (k+2) ++ cword .c31))) (boundary 1 false [S 4] (U 2 (12*k+25) ++ S 3::S 2::S 2::(T k ++ cword .c32))) := by
    have e : U 2 (12*k+25)=U 2 (12*k+23) ++ [S 2,S 2] := by
      rw [show 12*k+25=12*k+23+2 by omega,Raw14042DExitTail.ua]
      rfl
    simpa only [V,w23,w23_append,word_trip23,Bool.false_eq_true,ite_false,ccarry,next,T,List.cons_append,List.append_assoc,List.nil_append,e,List.singleton_append] using h5
  have h6 := rr (bBounceExit (12*k+25) (S 2::S 2::(T k ++ cword .c32)))
  have h7 := twoPumpAll (12*k+26) 1 0 (T k ++ cword .c32)
  have h67 : RR (boundary 1 false [S 4] (U 2 (12*k+25) ++ S 3::S 2::S 2::(T k ++ cword .c32))) (cCfg (12*k+30) k .c32) := by
    simpa only [cCfg,A,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,show 12*k+26+4*1=12*k+30 by omega] using Reach.trans h6 h7
  exact Reach.trans (Reach.trans (Reach.trans (Reach.trans h01 h2') h34) h5') h67

theorem bEvenExit (k n : Nat) (s : CTail) (hb : 6*n+crank s=2*k+3) :
    RR (boundary 1 true [S 5] (S 2::S 2::(U 1 (2*k+3) ++ S 2::S 3::(U 2 (2*k+1) ++ T n ++ cword s)))) (cCfg (12*k+30) k .c32) := by
  have h := bEvenFront k (T n ++ cword s)
  have h0 : RR (boundary 1 true [S 5] (S 2::S 2::(U 1 (2*k+3) ++ S 2::S 3::(U 2 (2*k+1) ++ T n ++ cword s)))) (A (4*k+7) (S 0::S 2::S 3::(U 2 (2*k+1) ++ T n ++ cword s))) := by
    simpa only [List.append_assoc] using h
  exact Reach.trans h0 (Reach.trans (bEvenDeplete k n s hb) (bEvenFinish k))
#print axioms bEvenExit
end Raw14042MixedExitEvenB
