import Raw14042SourceReach

namespace Raw14042TerminalReach
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042ArithmeticInvariant Raw14042SourceReach
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
attribute [local simp] Raw14042Right.T Raw140Double.tailWord
  Raw140ERSuffix.tailWord Raw140VariantTransfer.trip
  Raw14042BGeneral.aCfg Raw14042BGeneral.TA Raw14042BGeneral.aword
  Raw14042Bank.T Raw14042CGeneral.cCfg Raw14042Counter.T Raw14042Counter.cword
  Raw14042BTerminals.A Raw14042BTerminals.Braw
  Raw14042CTerminals.A Raw14042CTerminals.Braw
  Raw14042DTerminals.A Raw14042DTerminals.Braw
  Raw14042MixedTerminals.A Raw14042MixedTerminals.Braw

abbrev R := Reach M42

theorem terminal_reach_a (p n s : Nat) (hp : 24≤p) (he : p%2=0)
    (hn : n<2) (hs : s<6) :
    R (encode ⟨.a,p,n,s⟩) (encode (terminal .a p n s)) := by
  have hN : n=0 ∨ n=1 := by omega
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hN with rfl|rfl
  · rcases hS with rfl|rfl|rfl|rfl|rfl|rfl
    · have G := ccRR (p-2) 0 .c315 _ (by omega) (Raw14042CTerminals.a0r0 p hp he)
      simpa [encode,aTail,cTail,Raw14042CGeneral.crank,terminal] using G
    · have G := dRR (p+3) 8 _ (by omega) (Raw14042DTerminals.a0r1 p hp he)
      simpa [encode,aTail,bTail,terminal] using G
    · have G := dRR (p+1) 8 _ (by omega) (Raw14042DTerminals.a0r2 p hp he)
      simpa [encode,aTail,bTail,terminal] using G
    · by_cases hm : p%4=2
      · obtain ⟨t,ht,hR⟩ := Raw14042AMixedTerminal.a5215_mod2 p hp hm
        have hq : (p-8)/2+5=p/2+1 := by omega
        have G : R (Raw14042AMixedTerminal.A p [S 5,S 2,S 1,S 5])
            (encode ⟨.b,2*p+6,(p/2+1)/6,(p/2+1)%6⟩) := by
          apply bOut (Nat.mod_lt _ (by decide))
          refine ⟨t,?_,hR⟩
          simpa only [hq] using ht
        simpa [encode,aTail,Raw14042AMixedTerminal.A,Raw14042BGeneral.aCfg,
          Raw14042BGeneral.TA,Raw14042BGeneral.aword,Raw14042Bank.T,
          Raw140VariantTransfer.trip,Raw140ERSuffix.tailWord,terminal,hm] using G
      · have hm0 : p%4=0 := by omega
        obtain ⟨t,ht,hR⟩ := Raw14042AMixedEven.a5215_mod0 p hp hm0
        have G : R (Raw14042AMixedTerminal.A p [S 5,S 2,S 1,S 5])
            (encode ⟨.b,3*p+20,p/4-1,1⟩) := by
          apply bOut (by decide)
          exact ⟨t,ht,hR⟩
        simpa [encode,aTail,Raw14042AMixedTerminal.A,Raw14042BGeneral.aCfg,
          Raw14042BGeneral.TA,Raw14042BGeneral.aword,Raw14042Bank.T,
          Raw140VariantTransfer.trip,Raw140ERSuffix.tailWord,terminal,hm] using G
    · have G := bsRR (p+11-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.a0r4 p hp he)
      simpa [encode,aTail,Raw14042ArithmeticInvariant.b0,
        Raw14042BGeneral.arank,terminal] using G
    · have G := dRR (p+5) 8 _ (by omega) (Raw14042DTerminals.a0r5 p hp he)
      simpa [encode,aTail,bTail,terminal] using G
  · rcases hS with rfl|rfl|rfl|rfl|rfl|rfl
    · have G := ccRR (p+12-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.a1r0 p hp he)
      simpa [encode,aTail,cTail,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · have G := ccRR (p+12-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.a1r1 p hp he)
      simpa [encode,aTail,cTail,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · have G := bsRR (p+13-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.a1r2 p hp he)
      simpa [encode,aTail,Raw14042ArithmeticInvariant.b0,
        Raw14042BGeneral.arank,terminal] using G
    · have G := ccRR (p+4) 10 .c31 _ (by omega)
        (Raw14042CTerminals.a1r3 p hp he)
      simpa [encode,aTail,cTail,Raw14042CGeneral.crank,terminal] using G
    · have G := ccRR (p+16-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.a1r4 p hp he)
      simpa [encode,aTail,cTail,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · have H := Raw14042CTerminals.a1r5 p hp
      simpa [encode,aTail,Raw14042BGeneral.aCfg,Raw14042BGeneral.TA,
        Raw14042BGeneral.aword,Raw14042Bank.T,Raw140VariantTransfer.trip,
        Raw140ERSuffix.tailWord,terminal] using H

theorem terminal_reach_b (p n s : Nat) (hp : 24≤p) (he : p%2=0)
    (hn : n<2) (hs : s<6) :
    R (encode ⟨.b,p,n,s⟩) (encode (terminal .b p n s)) := by
  have hN : n=0 ∨ n=1 := by omega
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hN with rfl|rfl
  · rcases hS with rfl|rfl|rfl|rfl|rfl|rfl
    · have G := bsRR (p-4) 0 6 .t152 _ (by omega)
        (Raw14042BTerminals.b0r0 p hp he)
      simpa [encode,bTail,Raw14042BGeneral.arank,terminal] using G
    · have G := bsRR (p+5-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.b0r1 p hp he)
      simpa [encode,bTail,Raw14042ArithmeticInvariant.b0,
        Raw14042BGeneral.arank,terminal] using G
    · have G := bsRR (p-2) 1 0 .t152 _ (by omega)
        (Raw14042BTerminals.b0r2 p hp he)
      simpa [encode,bTail,Raw14042BGeneral.arank,terminal] using G
    · have G := ccRR (p+8-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.b0r3 p hp he)
      simpa [encode,bTail,cTail,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · have G := ccRR (p+6-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.b0r4 p hp he)
      simpa [encode,bTail,cTail,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · by_cases hm : p%4=0
      · have H := Raw14042MixedTerminals.b0r5_mod0 p hp he hm
        simpa [encode,bTail,cTail,Raw14042CGeneral.cCfg,terminal,hm] using H
      · have hm2 : p%4=2 := by omega
        obtain ⟨t,ht,hR⟩ := Raw14042MixedTerminals.b0r5_mod2 p hp he hm2
        have G : R (Raw14042MixedTerminals.Braw p [S 6,S 2,S 5,S 4,S 2])
            (encode ⟨.c,2*p+4,(p/2+1)/6,(p/2+1)%6⟩) := by
          apply cOut (Nat.mod_lt _ (by decide))
          exact ⟨t,ht,hR⟩
        simpa [encode,bTail,Raw14042MixedTerminals.Braw,terminal,hm] using G
  · rcases hS with rfl|rfl|rfl|rfl|rfl|rfl
    · have G := dRR (p+5) 8 _ (by omega) (Raw14042DTerminals.b1r0 p he)
      simpa [encode,bTail,Raw14042Right.T,Raw140Double.tailWord,terminal] using G
    · have G := ccRR (p+10-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.b1r1 p hp he)
      simpa [encode,bTail,cTail,Raw14042Right.T,Raw140Double.tailWord,
        Raw14042ArithmeticInvariant.a0,Raw14042CGeneral.crank,terminal] using G
    · have G := bsRR (p+13-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.b1r2 p hp he)
      simpa [encode,bTail,Raw14042Right.T,Raw140Double.tailWord,
        Raw14042ArithmeticInvariant.b0,Raw14042BGeneral.arank,terminal] using G
    · have G := bsRR (p+13-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.b1r3 p hp he)
      simpa [encode,bTail,Raw14042Right.T,Raw140Double.tailWord,
        Raw14042ArithmeticInvariant.b0,Raw14042BGeneral.arank,terminal] using G
    · have G := dRR (p+7) 8 _ (by omega) (Raw14042DTerminals.b1r4 p he)
      simpa [encode,bTail,Raw14042Right.T,Raw140Double.tailWord,terminal] using G
    · have H := Raw14042CTerminals.b1r5 p
      simpa [encode,bTail,Raw14042Right.T,Raw140Double.tailWord,terminal] using H

theorem terminal_reach_c (p n s : Nat) (hp : 24≤p) (he : p%2=0)
    (hn : n<2) (hs : s<6) :
    R (encode ⟨.c,p,n,s⟩) (encode (terminal .c p n s)) := by
  have hN : n=0 ∨ n=1 := by omega
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hN with rfl|rfl
  · rcases hS with rfl|rfl|rfl|rfl|rfl|rfl
    · have G := dRR (p-4) 11 _ (by omega) (Raw14042DTerminals.c0r0 p hp he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,terminal] using G
    · have G := dRR (p+1) 8 _ (by omega) (Raw14042DTerminals.c0r1 p he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,terminal] using G
    · have G := dRROdd (p+2) 1 .s6221 _ (by omega)
        (Raw14042DTerminals.c0r2 p he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,Raw140Double.rank,terminal] using G
    · have G := bsRR (p+11-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.c0r3 p hp he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,Raw14042ArithmeticInvariant.b0,
        Raw14042BGeneral.arank,terminal] using G
    · have G := bsRR (p+9-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.c0r4 p hp he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,Raw14042ArithmeticInvariant.b0,
        Raw14042BGeneral.arank,terminal] using G
    · by_cases hm : p%4=0
      · obtain ⟨t,ht,hR⟩ := Raw14042MixedTerminals.c0r5_mod0 p hp he hm
        have G : R (Raw14042MixedTerminals.A p [S 2,S 3,S 5,S 2,S 2,S 1])
            (encode ⟨.a,2*p+10,(p/2)/6,(p/2)%6⟩) := by
          apply aOut (Nat.mod_lt _ (by decide))
          exact ⟨t,ht,hR⟩
        simpa [encode,cTail,Raw14042MixedTerminals.A,
          Raw14042CGeneral.cCfg,Raw14042Counter.T,Raw14042Counter.cword,
          terminal,hm] using G
      · have hm2 : p%4=2 := by omega
        have H := Raw14042MixedTerminals.c0r5_mod2 p hp he hm2
        simpa [encode,aTail,cTail,Raw14042MixedTerminals.A,
          Raw14042CGeneral.cCfg,Raw14042Counter.T,Raw14042Counter.cword,
          terminal,hm] using H
  · rcases hS with rfl|rfl|rfl|rfl|rfl|rfl
    · have G := ccRR (p+12-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.c1r0 p hp he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · have G := bsRR (p+13-4) 0 3 .t152 _ (by omega)
        (Raw14042BTerminals.c1r1 p hp he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,Raw14042ArithmeticInvariant.b0,
        Raw14042BGeneral.arank,terminal] using G
    · have G := dRR (p+9) 8 _ (by omega) (Raw14042DTerminals.c1r2 p he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,terminal] using G
    · have G := dRR (p+9) 8 _ (by omega) (Raw14042DTerminals.c1r3 p he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,terminal] using G
    · have G := ccRR (p+14-7) 7 .c31 _ (by omega)
        (Raw14042CTerminals.c1r4 p hp he)
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,Raw14042ArithmeticInvariant.a0,
        Raw14042CGeneral.crank,terminal] using G
    · have H := Raw14042CTerminals.c1r5 p
      simpa [encode,cTail,Raw14042CGeneral.cCfg,Raw14042Counter.T,
        Raw14042Counter.cword,terminal] using H

theorem terminal_reach (x : Section) (hx : good x) (hn : x.n<2) :
    R (encode x) (encode (terminal x.kind x.p x.n x.s)) := by
  rcases x with ⟨kind,p,n,s⟩
  rcases hx with ⟨hp,he,hs⟩
  cases kind with
  | a => exact terminal_reach_a p n s hp he hn hs
  | b => exact terminal_reach_b p n s hp he hn hs
  | c => exact terminal_reach_c p n s hp he hn hs

theorem step_reach (x : Section) (hx : good x) :
    R (encode x) (encode (step x)) := by
  unfold step
  by_cases hn : 2≤x.n
  · simp only [hn,if_pos]
    exact drain_reach x hx hn
  · simp only [hn,if_neg]
    exact terminal_reach x hx (by omega)

#print axioms terminal_reach
#print axioms step_reach
end Raw14042TerminalReach
