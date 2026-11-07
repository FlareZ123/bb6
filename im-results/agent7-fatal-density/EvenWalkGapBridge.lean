import EvenWalkNoOvershoot
import EvenChainGap
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace GapNumber
private theorem pow_scale (n:Nat)(hn:25≤n):2^(n-4)=512*2^(n-13):=by
  have he:n-4=(n-13)+9:=by omega
  rw [he,Nat.pow_add]
  simp [Nat.mul_comm]

theorem uniform_initial_B_bands (n j B : Nat) (hn:25≤n)
  (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
  (hweak:2*(2^j*(2*n+3))+2*n+10≤2^(n-4)) :
   3≤B ∧ B≤2*2^(n-4)+1 ∧
   3≤2*B+(n-4) ∧ 2*B+(n-4)≤2*2^(n-4)+1 := by
  let p:=2^(n-4)
  let M:=2^j*(2*n+3)
  have hg := Growth.exp_quad n hn
  have hscale := pow_scale n hn
  have hbig:512*n<p:=by dsimp[p];rw [hscale];omega
  have hmod:81*B+3=16*p+128*M+169*n:=hmodel
  have hweak':2*M+2*n+10≤p:=hweak
  have hB0 : 3≤B ∧ B≤2*p+1:=by grind
  have hB1 : 3≤2*B+(n-4) ∧ 2*B+(n-4)≤2*p+1:=by grind
  exact ⟨hB0.1,hB0.2,hB1.1,hB1.2⟩

#print axioms uniform_initial_B_bands
end GapNumber

namespace GapNumber
open CascadeEvenChainGap
private theorem walk_one_balance (p k u C:Nat)
  (hpk: p=2^k)
  (hu:C+u=8*p) (hnear:2*C+k≤8*p) :
    evenWalk k u 1+(2*C+k)=8*p := by
  have hp:0<p:=by rw[hpk];exact Nat.pow_pos (by decide)
  simp only [evenWalk]
  rw [←hpk]
  omega

private theorem arithmetic_band (p u C:Nat) (hb:C+u=8*p)
  (hlo:3≤C) (hhi:C≤2*p+1) :
    6*p-1≤u ∧ u≤8*p-3 := by
  omega

private theorem arithmetic_gap (p u C:Nat) (hb:C+u=8*p)
  (hlo:2*p+1<C) (hhi:C<4*p+3) :
    4*p-3<u ∧ u<6*p-1 := by
  omega

/-- A fully quantified all-index inverse-walk certificate with genuine
    dyadic image-band hypotheses at all intermediate steps. -/
theorem uniform_two_four_walk (n j B q:Nat) (hn:25≤n)
 (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
 (hweak:2*(2^j*(2*n+3))+2*n+10≤2^(n-4))
 (hq:B+q=8*2^(n-4)) :
 ∃r:Nat, (r=2 ∨ r=3 ∨ r=4) ∧
   (∀i<r,6*2^(n-4)-1≤evenWalk (n-4) q i ∧
      evenWalk (n-4) q i≤8*2^(n-4)-3) ∧
   4*2^(n-4)-3<evenWalk (n-4) q r ∧
   evenWalk (n-4) q r<6*2^(n-4)-1 := by
 let p:=2^(n-4)
 let k:=n-4
 let B1:=2*B+k
 let B2:=4*B+3*k
 let B3:=8*B+7*k
 let B4:=16*B+15*k
 have hp:0<p:=by dsimp[p];exact Nat.pow_pos (by decide)
 have hpk:p=2^k:=rfl
 have hqc:B+q=8*p:=hq
 have hbb:=uniform_initial_B_bands n j B hn hmodel hweak
 have hB0 : 3≤B ∧ B≤2*p+1 := ⟨hbb.1,hbb.2.1⟩
 have hB1 : 3≤B1 ∧ B1≤2*p+1 := ⟨hbb.2.2.1,hbb.2.2.2⟩
 have heq1:evenWalk k q 1+B1=8*p := by
   simpa only [B1] using walk_one_balance p k q B hpk hqc (by
     have h:=hB1.2
     omega)
 have hband0: 6*p-1≤evenWalk k q 0 ∧ evenWalk k q 0≤8*p-3:=by
   simpa only [evenWalk] using arithmetic_band p q B hqc hB0.1 hB0.2
 have hband1: 6*p-1≤evenWalk k q 1 ∧ evenWalk k q 1≤8*p-3:=
   arithmetic_band p (evenWalk k q 1) B1 (by simpa [Nat.add_comm] using heq1) hB1.1 hB1.2
 have heq2 (hsmall:B2≤8*p):evenWalk k q 2+B2=8*p:=by
   have h : evenWalk k (evenWalk k q 1) 1+(2*B1+k)=8*p :=
     walk_one_balance p k (evenWalk k q 1) B1 hpk (by simpa [Nat.add_comm] using heq1) (by
       dsimp[B2,B1] at hsmall ⊢;omega)
   have he:evenWalk k q 2=evenWalk k (evenWalk k q 1) 1:=rfl
   rw[he]
   have hb:2*B1+k=B2:=by dsimp[B1,B2];omega
   rw [hb] at h
   exact h
 have heq3 (hsmall:B2≤2*p+1) (hsmaller:B3≤8*p):
      evenWalk k q 3+B3=8*p:=by
   have hb2:3≤B2:=by dsimp[B2];omega
   have heq2':=heq2 (by omega)
   have h : evenWalk k (evenWalk k q 2) 1+(2*B2+k)=8*p :=
     walk_one_balance p k (evenWalk k q 2) B2 hpk (by simpa [Nat.add_comm] using heq2') (by
       dsimp[B2,B3] at hsmaller ⊢;omega)
   have he:evenWalk k q 3=evenWalk k (evenWalk k q 2) 1:=rfl
   rw[he]
   have hb:2*B2+k=B3:=by dsimp[B2,B3];omega
   rw [hb] at h
   exact h
 have hklimit : k≤p:=by
   have hg:=Growth.exp_quad n hn
   have hs:=pow_scale n hn
   have hsmall: n<2^(n-13):=by omega
   dsimp [p,k]
   rw [hs]
   omega
 have heq4 (hsmall:B2≤2*p+1) (hsmaller:B3≤2*p+1):
      evenWalk k q 4+B4=8*p:=by
   have hh:=heq3 hsmall (by omega)
   have hB:2*B3+k≤8*p:=by
     dsimp[B3,B4] at *
     omega
   have h : evenWalk k (evenWalk k q 3) 1+(2*B3+k)=8*p :=
     walk_one_balance p k (evenWalk k q 3) B3 hpk (by simpa [Nat.add_comm] using hh) hB
   have he:evenWalk k q 4=evenWalk k (evenWalk k q 3) 1:=rfl
   rw[he]
   have hb:2*B3+k=B4:=by dsimp[B3,B4];omega
   rw [hb] at h
   exact h
 have hgap:=uniform_two_four_gap n j B hn hmodel hweak
 change (2*p+1 < B2 ∧ B2 < 4*p+3) ∨
   (B2≤2*p+1 ∧ 2*p+1<B3 ∧ B3<4*p+3) ∨
   (B3≤2*p+1 ∧ 2*p+1<B4 ∧ B4<4*p+3) at hgap
 rcases hgap with h2 | h3 | h4
 · let r:=2
   have heq:=heq2 (by omega)
   have hend := arithmetic_gap p (evenWalk k q 2) B2 (by simpa [Nat.add_comm] using heq) h2.1 h2.2
   refine ⟨r,Or.inl rfl,?_,hend.1,hend.2⟩
   intro i hi
   have hieq:i=0 ∨ i=1:=by dsimp[r] at hi;omega
   rcases hieq with hh|hh <;> subst i
   · exact hband0
   · exact hband1
 · let r:=3
   have hsmall:B2≤2*p+1:=h3.1
   have heq:=heq3 hsmall (by omega)
   have hend := arithmetic_gap p (evenWalk k q 3) B3 (by simpa [Nat.add_comm] using heq) h3.2.1 h3.2.2
   refine ⟨r,Or.inr (Or.inl rfl),?_,hend.1,hend.2⟩
   intro i hi
   have hieq:i=0 ∨ i=1 ∨ i=2:=by dsimp[r] at hi;omega
   rcases hieq with hh|hh|hh <;> subst i
   · exact hband0
   · exact hband1
   · apply arithmetic_band p (evenWalk k q 2) B2
     · simpa [Nat.add_comm] using (heq2 (by omega))
     · dsimp[B2,k];omega
     · omega
 · let r:=4
   have hsmall:B2≤2*p+1:=by
     have hh:=h4.1
     dsimp[B2,B3] at *
     omega
   have hsmaller:B3≤2*p+1:=h4.1
   have heq:=heq4 hsmall hsmaller
   have hend := arithmetic_gap p (evenWalk k q 4) B4 (by simpa [Nat.add_comm] using heq) h4.2.1 h4.2.2
   refine ⟨r,Or.inr (Or.inr rfl),?_,hend.1,hend.2⟩
   intro i hi
   have hieq:i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by dsimp[r] at hi;omega
   rcases hieq with hh|hh|hh|hh <;> subst i
   · exact hband0
   · exact hband1
   · apply arithmetic_band p (evenWalk k q 2) B2
     · simpa [Nat.add_comm] using (heq2 (by omega))
     · dsimp[B2,k];omega
     · omega
   · apply arithmetic_band p (evenWalk k q 3) B3
     · simpa [Nat.add_comm] using (heq3 hsmall (by omega))
     · dsimp[B3,k];omega
     · exact hsmaller

/-- Rooted exclusion from actual (2,0) source reset semantics under the
    exact arithmetic model and the proved all-time SafeResidue condition. -/
theorem uniform_two_four_root_exclusion (n j B q : Nat) (hn:25≤n)
 (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
 (hweak:2*(2^j*(2*n+3))+2*n+10≤2^(n-4))
 (hq:B+q=8*2^(n-4))
 (hs:CascadeEvenChainGap.SafeResidue (n-4) q) :
 ¬CascadeSweep.ReachC (2,0) (q,0) := by
  obtain ⟨r,_,hb,hl,hh⟩:=uniform_two_four_walk n j B q hn hmodel hweak hq
  exact CascadeEvenChainGap.walk_exits_gap_unreachable (n-4) q r
    (by omega) hs hb hl hh

#print axioms uniform_two_four_walk
#print axioms uniform_two_four_root_exclusion
end GapNumber
