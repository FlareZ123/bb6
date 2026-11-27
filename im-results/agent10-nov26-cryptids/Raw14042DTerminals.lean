import Raw14042LowLocal
import Raw14042DGeneral
import Raw14042Growth
import Raw14042Bank
namespace Raw14042DTerminals
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042DGeneral Raw14042LowLocal
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] run boundary
abbrev R := Reach M42
abbrev A (p : Nat) (w : List Sym) := boundary 0 true (U 3 p ++ [S 2]) w
abbrev Braw (p : Nat) (w : List Sym) := boundary 1 true (U 5 p) w
abbrev RR (k h : Nat) (s : Tail) (c : Prim) :=
  ∃ t : Tail, rank t=(k+rank s)%6 ∧ R c (B (2*(k+h)+2) ((k+rank s)/6) t)
theorem viaD (k h : Nat) (s : Tail) (c : Prim) (ho : (k+h)%2=1) (he : R c (D k h s)) : RR k h s c := by
  obtain ⟨t,hr,hh⟩ := oddReturn_rank k h s ho
  exact ⟨t,hr,Reach.trans he hh⟩
private theorem rr {k : Nat} {c d : Prim} (h : run M42 k c = some d) : R c d := ⟨k,h⟩
private theorem a2ToD (p : Nat) (hp : 4≤p) : R (A p [S 2]) (D (p-4) 8 .s62) := by
  simpa only [A,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,show p-4+4=p by omega] using rr (seedA2 (p-4))

theorem a0r1 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+3) 8 .s62 (A p [S 1,S 5,S 2]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [A,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,show p-1+1=p by omega,show p-1+4=p+3 by omega] using rr (a0_152 (p-1))
theorem a0r2 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+1) 8 .s62 (A p [S 1,S 1,S 2,S 1]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [A,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,show p-1+1=p by omega,show p-1+2=p+1 by omega] using rr (a0_1121 (p-1))
theorem a0r5 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+5) 8 .s62 (A p [S 1,S 1,S 5,S 1,S 1]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [A,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,show p-1+1=p by omega,show p-1+6=p+5 by omega] using rr (a0_11511 (p-1))
theorem b1r0 (p : Nat) (he : p%2=0) : RR (p+5) 8 .s62 (Braw p [S 6,S 4,S 4,S 6,S 2]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [Braw,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using rr (b1_62 p)
theorem b1r4 (p : Nat) (he : p%2=0) : RR (p+7) 8 .s62 (Braw p [S 6,S 4,S 4,S 6,S 4,S 0,S 5]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [Braw,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using rr (b1_6405 p)
theorem c0r0 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p-4) 11 .s62 (A p [S 2,S 3,S 1]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [A,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,show p-4+4=p by omega] using rr (c0_31 (p-4))
theorem c0r1 (p : Nat) (he : p%2=0) : RR (p+1) 8 .s62 (A p [S 2,S 3,S 2]) := by
  apply viaD _ _ _ _ (by omega)
  have h0 := rr (c0_32 p)
  have h1 := a2ToD (p+5) (by omega)
  simpa only [show p+5-4=p+1 by omega] using Reach.trans h0 h1
theorem c0r2 (p : Nat) (he : p%2=0) : RR (p+2) 1 .s6221 (A p [S 2,S 3,S 1,S 5]) := by
  apply viaD _ _ _ _ (by omega)
  simpa only [A,D,tailWord,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using rr (c0_315 p)
theorem c1r2 (p : Nat) (he : p%2=0) : RR (p+9) 8 .s62 (A p [S 2,S 3,S 2,S 2,S 3,S 1,S 5]) := by
  apply viaD _ _ _ _ (by omega)
  have h0 := rr (lowC315 p)
  have h1 := a2ToD (p+13) (by omega)
  simpa only [show p+13-4=p+9 by omega] using Reach.trans h0 h1
theorem c1r3 (p : Nat) (he : p%2=0) : RR (p+9) 8 .s62 (A p [S 2,S 3,S 2,S 2,S 3,S 2,S 5]) := by
  apply viaD _ _ _ _ (by omega)
  have h0 := rr (c1_325 p)
  have h1 := a2ToD (p+13) (by omega)
  simpa only [show p+13-4=p+9 by omega] using Reach.trans h0 h1
#print axioms a0r1
#print axioms a0r2
#print axioms a0r5
#print axioms b1r0
#print axioms b1r4
#print axioms c0r0
#print axioms c0r1
#print axioms c0r2
#print axioms c1r2
#print axioms c1r3
end Raw14042DTerminals
