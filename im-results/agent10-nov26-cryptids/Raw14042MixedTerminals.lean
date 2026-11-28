import Raw14042AMixedEven
import Raw14042MixedExitEvenB
import Raw14042MixedExitEvenC
import Raw14042ExtraTail

namespace Raw14042MixedTerminals
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042ArithmeticInvariant
open Raw14042Counter (CTail T cword turn)
open Raw14042CGeneral (crank crank_lt ct_balance cCfg)
open Raw14042BGeneral (ATail arank arank_lt aCfg)
open Raw14042MixedFront Raw14042MixedExitOdd
open Raw14042MixedExitEvenB Raw14042MixedExitEvenC
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary

abbrev R := Reach M42
abbrev A (p : Nat) (w : List Sym) := boundary 0 true (U 3 p ++ [S 2]) w
abbrev Braw (p : Nat) (w : List Sym) := boundary 1 true (U 5 p) w
private theorem rr {k : Nat} {c d : Prim} (h : run M42 k c = some d) : R c d := ⟨k,h⟩

/-- The B62542 terminal for p = 2 mod 4 realizes the arithmetic C branch. -/
theorem b0r5_mod2 (p : Nat) (hp : 24 ≤ p) (he : p%2=0) (hm : p%4=2) :
    ∃ s : CTail, crank s=(p/2+1)%6 ∧
      R (Braw p [S 6,S 2,S 5,S 4,S 2]) (cCfg (2*p+4) ((p/2+1)/6) s) := by
  let j := (p-4)/2
  let k := (j-1)/2
  let n := (turn j .c325).1
  let s := (turn j .c325).2
  have hj : p=2*j+4 := by dsimp [j]; omega
  have hjodd : j%2=1 := by dsimp [j]; omega
  have hk : j=2*k+1 := by dsimp [k]; omega
  have h0 := rr (Raw14042LowLocal.b0_62542 (2*j+1))
  have h1 := Raw14042MixedFront.bDeplete j
  have h01 : R (Braw p [S 6,S 2,S 5,S 4,S 2])
      (boundary 1 true [S 5]
        (S 2::S 2::(U 1 (j+3) ++ S 2::S 3::(U 2 (j+1) ++ T n ++ cword s)))) := by
    have h0' : R (Braw p [S 6,S 2,S 5,S 4,S 2])
        (boundary 4 true (S 1::S 3::U 5 (2*j+1)) [S 1,S 1,S 2,S 3,S 3,S 1,S 5]) := by
      simpa only [Braw,hj,U,List.replicate_succ,List.cons_append] using h0
    simpa only [n,s] using Reach.trans h0' h1
  have h2 := Raw14042MixedExitOdd.bExit k (T n ++ cword s)
  have h2' : R
      (boundary 1 true [S 5]
        (S 2::S 2::(U 1 (j+3) ++ S 2::S 3::(U 2 (j+1) ++ T n ++ cword s))))
      (cCfg (8*k+16) n s) := by
    simpa only [cCfg,A,hk,List.append_assoc,show (2*k+1)+3=2*k+4 by omega,
      show (2*k+1)+1=2*k+2 by omega] using h2
  have hb := Raw14042CGeneral.ct_balance j (.c325)
  have hlt := crank_lt s
  have hbal : 6*n+crank s=p/2+1 := by
    dsimp only [n,s]
    simp only [Raw14042CGeneral.crank] at hb
    omega
  have hn : n=(p/2+1)/6 := by omega
  have hs : crank s=(p/2+1)%6 := by omega
  refine ⟨s,hs,?_⟩
  have h := Reach.trans h01 h2'
  simpa only [hn,hj,hk,show 2*(2*k+1)+4=4*k+6 by omega,
    show 2*(4*k+6)+4=8*k+16 by omega] using h

/-- The B62542 terminal for p = 0 mod 4 realizes the arithmetic exceptional C branch. -/
theorem b0r5_mod0 (p : Nat) (hp : 24 ≤ p) (he : p%2=0) (hm : p%4=0) :
    R (Braw p [S 6,S 2,S 5,S 4,S 2])
      (cCfg (3*p+18) (p/4-1) .c32) := by
  let j := (p-4)/2
  let k := j/2
  let n := (turn j .c325).1
  let s := (turn j .c325).2
  have hj : p=2*j+4 := by dsimp [j]; omega
  have hje : j%2=0 := by dsimp [j]; omega
  have hk : j=2*k := by dsimp [k]; omega
  have h0 := rr (Raw14042LowLocal.b0_62542 (2*j+1))
  have h1 := Raw14042MixedFront.bDeplete j
  have h01 : R (Braw p [S 6,S 2,S 5,S 4,S 2])
      (boundary 1 true [S 5]
        (S 2::S 2::(U 1 (j+3) ++ S 2::S 3::(U 2 (j+1) ++ T n ++ cword s)))) := by
    have h0' : R (Braw p [S 6,S 2,S 5,S 4,S 2])
        (boundary 4 true (S 1::S 3::U 5 (2*j+1)) [S 1,S 1,S 2,S 3,S 3,S 1,S 5]) := by
      simpa only [Braw,hj,U,List.replicate_succ,List.cons_append] using h0
    simpa only [n,s] using Reach.trans h0' h1
  have hb := Raw14042CGeneral.ct_balance j (.c325)
  have hbal : 6*n+crank s=2*k+3 := by
    dsimp only [n,s]
    simp only [Raw14042CGeneral.crank] at hb
    omega
  have h2 := Raw14042MixedExitEvenB.bEvenExit k n s hbal
  have h := Reach.trans h01 h2
  have hp4 : p/4=k+1 := by omega
  simpa only [hj,hk,hp4,show 3*(4*k+4)+18=12*k+30 by omega] using h

/-- The C35221 terminal for p = 0 mod 4 realizes the ordinary arithmetic A branch. -/
theorem c0r5_mod0 (p : Nat) (hp : 24 ≤ p) (he : p%2=0) (hm : p%4=0) :
    ∃ s : ATail, arank s=(p/2)%6 ∧
      R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
        (aCfg (2*p+10) ((p/2)/6) s) := by
  let j := (p-4)/2
  let k := j/2
  let n := (Raw14042DMixed.turn j .t1121).1
  let s := (Raw14042DMixed.turn j .t1121).2
  have hj : p=2*j+4 := by dsimp [j]; omega
  have hje : j%2=0 := by dsimp [j]; omega
  have hk : j=2*k := by dsimp [k]; omega
  have h0 := rr (Raw14042LowLocal.c0_35221 p)
  have h1 := Raw14042MixedFront.cDeplete j
  have h01 : R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
      (boundary 3 false [S 4]
        (U 4 (j+4) ++ S 0::S 5::(U 1 (j+2) ++ S 5::
          (Raw14042AWord.TA n ++ Raw14042DMixed.aw s)))) := by
    have h0' : R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
        (boundary 3 false (U 6 (p+1) ++ [S 4]) [S 4,S 2,S 1,S 5,S 5,S 4,S 2]) := by
      simpa only [A] using h0
    simpa only [n,s,hj,show 2*j+5=2*j+4+1 by omega] using Reach.trans h0' h1
  have h2 := Raw14042MixedExitOdd.cExit k (Raw14042AWord.TA n ++ Raw14042DMixed.aw s)
  have h2' : R
      (boundary 3 false [S 4]
        (U 4 (j+4) ++ S 0::S 5::(U 1 (j+2) ++ S 5::
          (Raw14042AWord.TA n ++ Raw14042DMixed.aw s))))
      (aCfg (8*k+18) n s) := by
    simpa only [aCfg,Raw14042MixedExitEvenC.ta_eq,hk,List.append_assoc,
      show 2*k+4=2*k+4 by omega,show 2*k+2=2*k+2 by omega] using h2
  have hb := Raw14042MixedExitEvenC.turn_balance j (.t1121)
  have hlt := arank_lt s
  have hbal : 6*n+arank s=p/2 := by
    dsimp only [n,s]
    simp only [Raw14042BGeneral.arank] at hb
    omega
  have hn : n=(p/2)/6 := by omega
  have hs : arank s=(p/2)%6 := by omega
  refine ⟨s,hs,?_⟩
  have h := Reach.trans h01 h2'
  simpa only [hn,hj,hk,show 2*(4*k+4)+10=8*k+18 by omega] using h

/-- The C35221 terminal for p = 2 mod 4 realizes the exceptional arithmetic A branch. -/
theorem c0r5_mod2 (p : Nat) (hp : 24 ≤ p) (he : p%2=0) (hm : p%4=2) :
    R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
      (aCfg (3*p+38) (p/4-2) .t542) := by
  let j := (p-4)/2
  let k := (j-1)/2
  let n := (Raw14042DMixed.turn j .t1121).1
  let s := (Raw14042DMixed.turn j .t1121).2
  have hj : p=2*j+4 := by dsimp [j]; omega
  have hjo : j%2=1 := by dsimp [j]; omega
  have hk : j=2*k+1 := by dsimp [k]; omega
  have hkpos : 1 ≤ k := by omega
  have h0 := rr (Raw14042LowLocal.c0_35221 p)
  have h1 := Raw14042MixedFront.cDeplete j
  have h01 : R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
      (boundary 3 false [S 4]
        (U 4 (j+4) ++ S 0::S 5::(U 1 (j+2) ++ S 5::
          (Raw14042AWord.TA n ++ Raw14042DMixed.aw s)))) := by
    have h0' : R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
        (boundary 3 false (U 6 (p+1) ++ [S 4]) [S 4,S 2,S 1,S 5,S 5,S 4,S 2]) := by
      simpa only [A] using h0
    simpa only [n,s,hj,show 2*j+5=2*j+4+1 by omega] using Reach.trans h0' h1
  have hb := Raw14042MixedExitEvenC.turn_balance j (.t1121)
  have hbal : 6*n+arank s=2*k+3 := by
    dsimp only [n,s]
    simp only [Raw14042BGeneral.arank] at hb
    omega
  have h2 := Raw14042MixedExitEvenC.cEvenExit k n s hbal
  have h12 : R (A p [S 2,S 3,S 5,S 2,S 2,S 1])
      (A (12*k+44) (Raw14042Bank.T (k+1) ++ [S 1,S 1])) :=
    Reach.trans h01 h2
  have h3 := Raw14042ExtraTail.return11 (k-1) (12*k+43)
  have h3' : R (A (12*k+44) (Raw14042Bank.T (k+1) ++ [S 1,S 1]))
      (aCfg (12*k+56) (k-1) .t542) := by
    simpa only [A,aCfg,Raw14042BGeneral.aCfg,Raw14042BGeneral.TA,
      Raw14042BGeneral.aword,Raw140ERSuffix.tailWord,
      show k-1+2=k+1 by omega,show 12*k+43+1=12*k+44 by omega,
      show 12*k+43+13=12*k+56 by omega] using h3
  have hp4 : p/4=k+1 := by omega
  have hn : p/4-2=k-1 := by omega
  simpa only [hj,hk,hp4,hn,show 3*(4*k+6)+38=12*k+56 by omega] using Reach.trans h12 h3'

#print axioms b0r5_mod2
#print axioms b0r5_mod0
#print axioms c0r5_mod0
#print axioms c0r5_mod2
end Raw14042MixedTerminals
