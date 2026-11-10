import ForkCensus
import ForkOriginal
import FatalOddFeeder46
import FeederSixFamily
set_option maxHeartbeats 0

namespace BB746ForkCensus

open CascadeResetInverse CascadeFirstFork CascadeManyShield CascadeSweep

/-- Combine three source-certified infinite inverse-cone obstructions.
A genuine fatal odd predecessor is unreachable in 154 of 162 admissible
classes modulo 1458. The other eight classes are exceptional below. -/
theorem fatal_odd_feeder_154_of_162 (n : Nat)
    (hn : 76≤n)
    (hs : n%18=4 ∨ n%18=5)
    (hex : ¬ exceptional (n%1458)) :
    ResetParent (oddPre n (fatal n)) (fatal n) ∧
    ¬ReachC (2,0) (oddPre n (fatal n),0) := by
  have hparent : ResetParent (oddPre n (fatal n)) (fatal n) :=
    fatal_has_odd_parent n (by omega) hs
  have hx : 9*oddPre n (fatal n)+17*n+39=56*2^(n-2) := by
    let p := 2^(n-2)
    let u := fatal n
    let d := (2*u+5)/9
    have hpow : 2^n=4*p := by
      have he : n=(n-2)+2 := by omega
      rw [he,Nat.pow_add]
      dsimp [p]
      omega
    have hclose : u+n+4=4*2^n := by
      simpa only [u] using (fatal_close n (by omega))
    have hnum : 2*u+5+2*n+3=32*p := by omega
    have hdiv : (2*u+5)%9=0 := fatal_divnine n (by omega) hs
    have hd : 9*d=2*u+5 := by dsimp [d]; omega
    have hpbound : 12*n+40<p := by
      have hb := CascadeFastReturn.feeder_growth (n-2) (by omega)
      have he : (n-2)+2=n := by omega
      rw [he] at hb
      exact hb
    have hodd : oddPre n u +8*p+n+3=4*d := by
      dsimp [oddPre,p,d]
      omega
    change 9*oddPre n u+17*n+39=56*p
    omega
  have hfour (hr : n%486=76 ∨ n%486=238 ∨ n%486=275 ∨ n%486=437) :
      ¬ReachC (2,0) (oddPre n (fatal n),0) :=
    CascadeFeederSix.fatal_feeder_four_residues n
      (oddPre n (fatal n)) hn hr hx
  have hnew (r : Nat)
      (hr : r=40 ∨ r=401 ∨ r=1012 ∨ r=1373)
      (he : n%1458=r) :
      ResetParent (oddPre n (fatal n)) (fatal n) ∧
      ¬ReachC (2,0) (oddPre n (fatal n),0) := by
    have hnrep : n=r+1458*(n/1458) := by
      have hm := Nat.mod_add_div n 1458
      omega
    have h := BB746Fork.fatal_odd_feeder_four_classes r (n/1458) hr
    simpa only [←hnrep] using h
  rcases universal_154 n hs hex with hgood | h76 | h238 | h275 | h437 |
    h40 | h401 | h1012 | h1373
  · exact CascadeFastReturn.fatal_odd_feeder_46_residue_exclusion n (by omega) hgood
  · exact ⟨hparent,hfour (Or.inl h76)⟩
  · exact ⟨hparent,hfour (Or.inr (Or.inl h238))⟩
  · exact ⟨hparent,hfour (Or.inr (Or.inr (Or.inl h275)))⟩
  · exact ⟨hparent,hfour (Or.inr (Or.inr (Or.inr h437)))⟩
  · exact hnew 40 (Or.inl rfl) h40
  · exact hnew 401 (Or.inr (Or.inl rfl)) h401
  · exact hnew 1012 (Or.inr (Or.inr (Or.inl rfl))) h1012
  · exact hnew 1373 (Or.inr (Or.inr (Or.inr rfl))) h1373

#print axioms fatal_odd_feeder_154_of_162
end BB746ForkCensus
