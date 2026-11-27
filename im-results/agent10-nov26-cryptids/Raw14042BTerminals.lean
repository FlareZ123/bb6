import Raw14042BGeneral
import Raw14042LowLocal
namespace Raw14042BTerminals
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer Raw14042BGeneral Raw14042LowLocal
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] run boundary
abbrev A (p : Nat) (w : List Sym) := boundary 0 true (U 3 p ++ [S 2]) w
abbrev Braw (p : Nat) (w : List Sym) := boundary 1 true (U 5 p) w
abbrev RR (k u v : Nat) (s : ATail) (c : Prim) :=
  ∃ t : ATail, arank t=(k+arank s+1)%6 ∧ R c (aCfg (2*(k+v+1)+6) (u+(k+arank s+1)/6-1) t)
private theorem rr {k : Nat} {c d : Prim} (h : run M42 k c = some d) : R c d := ⟨k,h⟩
theorem viaB (k u v : Nat) (s : ATail) (c : Prim) (ho : (k+v+1)%2=1) (hu : 1≤u+(k+arank s)/6)
    (h : R c (bSeedCfg k u v s)) : RR k u v s c := by
  obtain ⟨t,hr,hh⟩ := oddReturn k u v s ho hu
  exact ⟨t,hr,Reach.trans h hh⟩
theorem viaB0 (p : Nat) (c : Prim) (hp : 24≤p) (ho : p%2=1) (h : R c (Braw p [])) : RR (p-4) 0 3 .t152 c := by
  apply viaB _ _ _ _ _ (by omega) (by simp only [arank]; omega)
  have h0 : R (Braw p []) (bSeedCfg (p-4) 0 3 .t152) := by
    simpa only [Braw,bSeedCfg,AB,Raw14042Bank.B,Raw140VariantTransfer.bank,aword,Raw140ERSuffix.tailWord,
      U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,show p-4+4=p by omega] using rr (seedBblank (p-4))
  exact Reach.trans h h0

theorem a0r4 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+11-4) 0 3 .t152 (A p [S 1,S 1,S 5,S 5]) := by
  apply viaB0 (p+11) _ (by omega) (by omega)
  simpa only [A,Braw,show p-1+1=p by omega,show p-1+12=p+11 by omega] using rr (a0_1155 (p-1))
theorem a1r2 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+13-4) 0 3 .t152 (A p [S 1,S 1,S 5,S 1,S 1,S 2,S 1]) := by
  apply viaB0 (p+13) _ (by omega) (by omega)
  simpa only [A,Braw,show p-1+1=p by omega,show p-1+14=p+13 by omega] using rr (a1_1121 (p-1))
theorem b0r0 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p-4) 0 6 .t152 (Braw p [S 6,S 2]) := by
  apply viaB _ _ _ _ _ (by omega) (by simp only [arank]; omega)
  simpa only [Braw,bSeedCfg,AB,Raw14042Bank.B,Raw140VariantTransfer.bank,aword,Raw140ERSuffix.tailWord,
    U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,show p-4+4=p by omega] using rr (b0_62 (p-4))
theorem b0r1 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+5-4) 0 3 .t152 (Braw p [S 6,S 4]) := by
  apply viaB0 (p+5) _ (by omega) (by omega)
  exact rr (lowB64 p)
theorem b0r2 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p-2) 1 0 .t152 (Braw p [S 6,S 2,S 2,S 1]) := by
  apply viaB _ _ _ _ _ (by omega) (by omega)
  simpa only [Braw,bSeedCfg,AB,Raw14042Bank.B,Raw140VariantTransfer.bank,aword,Raw140ERSuffix.tailWord,
    U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_nil,List.append_assoc,show p-2+2=p by omega] using rr (b0_6221 (p-2))
theorem b1r2 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+13-4) 0 3 .t152 (Braw p [S 6,S 4,S 4,S 6,S 2,S 2,S 1]) := by
  apply viaB0 (p+13) _ (by omega) (by omega)
  exact rr (b1_6221 p)
theorem b1r3 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+13-4) 0 3 .t152 (Braw p [S 6,S 4,S 4,S 6,S 4,S 2,S 1]) := by
  apply viaB0 (p+13) _ (by omega) (by omega)
  exact rr (b1_6421 p)
theorem c0r3 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+11-4) 0 3 .t152 (A p [S 2,S 3,S 2,S 5]) := by
  apply viaB0 (p+11) _ (by omega) (by omega)
  exact rr (c0_325 p)
theorem c0r4 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+9-4) 0 3 .t152 (A p [S 2,S 3,S 2,S 4,S 2]) := by
  apply viaB0 (p+9) _ (by omega) (by omega)
  exact rr (c0_3242 p)
theorem c1r1 (p : Nat) (hp : 24≤p) (he : p%2=0) : RR (p+13-4) 0 3 .t152 (A p [S 2,S 3,S 2,S 2,S 3,S 2]) := by
  apply viaB0 (p+13) _ (by omega) (by omega)
  exact rr (c1_32 p)
#print axioms a0r4
#print axioms a1r2
#print axioms b0r0
#print axioms b0r1
#print axioms b0r2
#print axioms b1r2
#print axioms b1r3
#print axioms c0r3
#print axioms c0r4
#print axioms c1r1
end Raw14042BTerminals
