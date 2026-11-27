import Raw14042CGeneral
import Raw14042LowLocal
namespace Raw14042CTerminals
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042CGeneral Raw14042LowLocal
open Raw14042Counter (CTail T cword counterCfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] run boundary
abbrev A (p : Nat) (w : List Sym) := boundary 0 true (U 3 p ++ [S 2]) w
abbrev Braw (p : Nat) (w : List Sym) := boundary 1 true (U 5 p) w
abbrev RR (k m : Nat) (s : CTail) (c : Prim) :=
  ∃ t : CTail, crank t=(k+crank s+2)%6 ∧ R c (cCfg (2*(k+m)+6) ((k+crank s+2)/6) t)
theorem viaC (k m : Nat) (s : CTail) (c : Prim) (he : (k+m)%2=0)
    (h : R c (counterCfg m 0 (U 3 k ++ [S 2]) s)) : RR k m s c := by
  obtain ⟨t,hr,hh⟩ := evenReturn k m s he
  exact ⟨t,hr,Reach.trans h hh⟩
private theorem rr {k : Nat} {c d : Prim} (h : run M42 k c = some d) : R c d := ⟨k,h⟩
theorem viaA0 (p : Nat) (c : Prim) (hp : 7≤p) (he : p%2=0) (h : R c (A p [])) : RR (p-7) 7 .c31 c := by
  apply viaC _ _ _ _ (by omega)
  let X := U 3 (p-7) ++ [S 2]
  have h0 := rr (Raw14042CounterLocal.seedCounter X)
  have hp7 : U 3 p ++ [S 2] = U 3 7 ++ X := by
    dsimp only [X]
    rw [merge,show 7+(p-7)=p by omega]
  have h1 : R (A p []) (counterCfg 7 0 X .c31) := by
    simpa only [A,counterCfg,T,cword,X,hp7,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using h0
  exact Reach.trans h h1

theorem a0r0 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p-2) 0 .c315 (A p [S 5,S 4,S 2]) := by
  apply viaC _ _ _ _ (by omega)
  simpa only [A,counterCfg,T,cword,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,show p-2+2=p by omega] using rr (a0_542 (p-2))
theorem a1r0 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+12-7) 7 .c31 (A p [S 1,S 1,S 5,S 5,S 4,S 2]) := by
  apply viaA0 (p+12) _ (by omega) (by omega)
  simpa only [A,show p-1+1=p by omega,show p-1+13=p+12 by omega] using rr (Raw14042CounterLocal.low542 (p-1))
theorem a1r1 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+12-7) 7 .c31 (A p [S 1,S 1,S 5,S 1,S 5,S 2]) := by
  apply viaA0 (p+12) _ (by omega) (by omega)
  simpa only [A,show p-1+1=p by omega,show p-1+13=p+12 by omega] using rr (a1_152 (p-1))
theorem a1r3 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+4) 10 .c31 (A p [S 1,S 1,S 5,S 5,S 2,S 1,S 5]) := by
  apply viaC _ _ _ _ (by omega)
  simpa only [A,counterCfg,T,cword,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,show p-1+1=p by omega,show p-1+5=p+4 by omega] using rr (a1_5215 (p-1))
theorem a1r4 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+16-7) 7 .c31 (A p [S 1,S 1,S 5,S 1,S 1,S 5,S 5]) := by
  apply viaA0 (p+16) _ (by omega) (by omega)
  simpa only [A,show p-1+1=p by omega,show p-1+17=p+16 by omega] using rr (a1_1155 (p-1))
theorem b0r3 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+8-7) 7 .c31 (Braw p [S 6,S 4,S 2,S 1]) := by
  apply viaA0 (p+8) _ (by omega) (by omega)
  exact rr (b0_6421 p)
theorem b0r4 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+6-7) 7 .c31 (Braw p [S 6,S 4,S 0,S 5]) := by
  apply viaA0 (p+6) _ (by omega) (by omega)
  exact rr (b0_6405 p)
theorem b1r1 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+10-7) 7 .c31 (Braw p [S 6,S 4,S 4,S 6,S 4]) := by
  apply viaA0 (p+10) _ (by omega) (by omega)
  exact rr (b1_64 p)
theorem c1r0 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+12-7) 7 .c31 (A p [S 2,S 3,S 2,S 2,S 3,S 1]) := by
  apply viaA0 (p+12) _ (by omega) (by omega)
  exact rr (c1_31 p)
theorem c1r4 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+14-7) 7 .c31 (A p [S 2,S 3,S 2,S 2,S 3,S 2,S 4,S 2]) := by
  apply viaA0 (p+14) _ (by omega) (by omega)
  exact rr (c1_3242 p)

theorem a1r5 (p : Nat) (hp : 24≤p) : R (A p [S 1,S 1,S 5,S 1,S 1,S 5,S 1,S 1]) (A (p+12) [S 5,S 4,S 2]) := by
  simpa only [A,show p-1+1=p by omega,show p-1+13=p+12 by omega] using rr (a1_11511 (p-1))
theorem b1r5 (p : Nat) : R (Braw p [S 6,S 4,S 4,S 6,S 2,S 5,S 4,S 2]) (Braw (p+12) [S 6,S 2]) := rr (b1_62542 p)
theorem c1r5 (p : Nat) : R (A p [S 2,S 3,S 2,S 2,S 3,S 5,S 2,S 2,S 1]) (A (p+12) [S 2,S 3,S 1]) := rr (c1_35221 p)
#print axioms a0r0
#print axioms a1r0
#print axioms a1r1
#print axioms a1r3
#print axioms a1r4
#print axioms b0r3
#print axioms b0r4
#print axioms b1r1
#print axioms c1r0
#print axioms c1r4
#print axioms a1r5
#print axioms b1r5
#print axioms c1r5
end Raw14042CTerminals
