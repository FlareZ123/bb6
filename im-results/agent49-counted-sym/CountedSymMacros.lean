module
public import CountedSymPure
public import SourceAffineBlocks

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine BB6.Agent11.SourceCost

namespace BB6.Agent49.CountedSym.CountedAtoms
set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
variable {target_tm : Machine (Fin 2) (Fin 6)} {flag : Bool}
variable (rules : CountedAtoms target_tm flag)
include rules

/-! Original-source macro proofs adapted from the F412 counted draft.
Both variants use the same source endpoints and the already checked
fourteen affine block identities. A case split on the cost variant is
needed only for choosing the coefficient formula and its polynomial sum. -/

theorem ruleA0_exact (k d : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 32 28)*k+(fcost flag 314 284))
      (evalSym target_tm (stateA0 (k+1) (d+6) R_tail))
      (evalSym target_tm (stateA 0 k d R_tail)) := by
  have h := rules.costIter_exact 46 (stateA0 (k+1) (d+6) R_tail)
  have hcost : costIter flag 46 (stateA0 (k+1) (d+6) R_tail) = (fcost flag 32 28)*k+(fcost flag 314 284) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.a0_false k d R_tail
    · exact BB6.Agent26.SourceAffine.a0_true k d R_tail
  rw [hcost] at h
  exact h

theorem ruleA_step_exact (m k d : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 454 408))
      (evalSym target_tm (stateA m (k+1) (d+6) R_tail))
      (evalSym target_tm (stateA (m+1) k d R_tail)) := by
  have h := rules.costIter_exact 66 (stateA m (k+1) (d+6) R_tail)
  have hcost : costIter flag 66 (stateA m (k+1) (d+6) R_tail) = (fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 454 408) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.a_false m k d R_tail
    · exact BB6.Agent26.SourceAffine.a_true m k d R_tail
  rw [hcost, ruleA_step_eq] at h
  exact h

theorem ruleA_iter_exact (n m k d : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (n*((fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 86 76)*n+(fcost flag 368 332)))
      (evalSym target_tm (stateA m (k+n) (d+6*n) R_tail))
      (evalSym target_tm (stateA (m+n) k d R_tail)) := by
  induction n generalizing m k d with
  | zero => simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero]; rfl
  | succ n ih =>
    have h1 : k+(n+1) = (k+n)+1 := by omega
    have h2 : d+6*(n+1) = (d+6*n)+6 := by omega
    have h3 : m+(n+1) = (m+1)+n := by omega
    have hc : ((fcost flag 140 124)*m+(fcost flag 32 28)*(k+n)+(fcost flag 454 408))+n*((fcost flag 140 124)*(m+1)+(fcost flag 32 28)*k+(fcost flag 86 76)*n+(fcost flag 368 332)) =
        (n+1)*((fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 86 76)*(n+1)+(fcost flag 368 332)) := by
      cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] <;> ring
    rw [←hc,h1,h2,h3]
    exact ReachesIn.trans (rules.ruleA_step_exact m (k+n) (d+6*n) R_tail) (ih (m+1) k d)

theorem ruleC_step_exact (p k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 76 68)*p+(fcost flag 64 56)*k+(fcost flag 486 434))
      (evalSym target_tm (stateC (p+3) (k+1) d2 R_tail))
      (evalSym target_tm (stateC (p+2) (k+3) (d2+2) R_tail)) := by
  have h := rules.costIter_exact 46 (stateC (p+3) (k+1) d2 R_tail)
  have hcost : costIter flag 46 (stateC (p+3) (k+1) d2 R_tail) = (fcost flag 76 68)*p+(fcost flag 64 56)*k+(fcost flag 486 434) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.c_false p k d2 R_tail
    · exact BB6.Agent26.SourceAffine.c_true p k d2 R_tail
  rw [hcost,ruleC_step_eq] at h
  exact h

theorem ruleC_iter_exact (n p k d2 : ℕ) (R_tail : List SymTok) (hk : 1 ≤ k) :
    ReachesIn target_tm (n*((fcost flag 76 68)*p+(fcost flag 64 56)*k+(fcost flag 102 90)*n+(fcost flag 320 288)))
      (evalSym target_tm (stateC (p+n+2) k d2 R_tail))
      (evalSym target_tm (stateC (p+2) (k+2*n) (d2+2*n) R_tail)) := by
  induction n generalizing p k d2 with
  | zero => simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero]; rfl
  | succ n ih =>
    obtain ⟨k0,rfl⟩ : ∃ k0, k = k0+1 := ⟨k-1,by omega⟩
    have h1 : p+(n+1)+2 = (p+n)+3 := by omega
    have h2 : k0+1+2*(n+1) = (k0+3)+2*n := by omega
    have h3 : d2+2*(n+1) = (d2+2)+2*n := by omega
    have hc : ((fcost flag 76 68)*(p+n)+(fcost flag 64 56)*k0+(fcost flag 486 434))+n*((fcost flag 76 68)*p+(fcost flag 64 56)*(k0+3)+(fcost flag 102 90)*n+(fcost flag 320 288)) =
        (n+1)*((fcost flag 76 68)*p+(fcost flag 64 56)*(k0+1)+(fcost flag 102 90)*(n+1)+(fcost flag 320 288)) := by
      cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] <;> ring
    rw [←hc,h1,h2,h3]
    exact ReachesIn.trans (rules.ruleC_step_exact (p+n) k0 d2 R_tail)
      (ih p (k0+3) (d2+2) (by omega))

theorem ruleB_step_AA_exact (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 1048 942))
      (evalSym target_tm (stateB sep3A sep3A (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3A sep3A (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := rules.costIter_exact 126 (stateB sep3A sep3A (p+1) (m+2) (k+1) d2 R_tail)
  have hcost : costIter flag 126 (stateB sep3A sep3A (p+1) (m+2) (k+1) d2 R_tail) = (fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 1048 942) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.bAA_false p m k d2 R_tail
    · exact BB6.Agent26.SourceAffine.bAA_true p m k d2 R_tail
  rw [hcost] at h
  have hrfl : iterStep stepPure 126 (stateB sep3A sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 126 (stateB sep3A sep3A (p + 1) (m + 2) (k +
      1) d2 R_tail)) =
      (evalSym target_tm) (stateB sep3A sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

theorem ruleB_step_AB_exact (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 978 880))
      (evalSym target_tm (stateB sep3A sep3B (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3A sep3B (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := rules.costIter_exact 118 (stateB sep3A sep3B (p+1) (m+2) (k+1) d2 R_tail)
  have hcost : costIter flag 118 (stateB sep3A sep3B (p+1) (m+2) (k+1) d2 R_tail) = (fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 978 880) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.bAB_false p m k d2 R_tail
    · exact BB6.Agent26.SourceAffine.bAB_true p m k d2 R_tail
  rw [hcost] at h
  have hrfl : iterStep stepPure 118 (stateB sep3A sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 118 (stateB sep3A sep3B (p + 1) (m + 2) (k +
      1) d2 R_tail)) =
      (evalSym target_tm) (stateB sep3A sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

theorem ruleB_step_BA_exact (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 896 806))
      (evalSym target_tm (stateB sep3B sep3A (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3B sep3A (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := rules.costIter_exact 106 (stateB sep3B sep3A (p+1) (m+2) (k+1) d2 R_tail)
  have hcost : costIter flag 106 (stateB sep3B sep3A (p+1) (m+2) (k+1) d2 R_tail) = (fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 896 806) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.bBA_false p m k d2 R_tail
    · exact BB6.Agent26.SourceAffine.bBA_true p m k d2 R_tail
  rw [hcost] at h
  have hrfl : iterStep stepPure 106 (stateB sep3B sep3A (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item (.run 1), .item (.run 2), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 106 (stateB sep3B sep3A (p + 1) (m + 2) (k +
      1) d2 R_tail)) =
      (evalSym target_tm) (stateB sep3B sep3A (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3A, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

theorem ruleB_step_BB_exact (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 826 744))
      (evalSym target_tm (stateB sep3B sep3B (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3B sep3B (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := rules.costIter_exact 98 (stateB sep3B sep3B (p+1) (m+2) (k+1) d2 R_tail)
  have hcost : costIter flag 98 (stateB sep3B sep3B (p+1) (m+2) (k+1) d2 R_tail) = (fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 826 744) := by
    cases flag
    · exact BB6.Agent26.SourceAffine.bBB_false p m k d2 R_tail
    · exact BB6.Agent26.SourceAffine.bBB_true p m k d2 R_tail
  rw [hcost] at h
  have hrfl : iterStep stepPure 98 (stateB sep3B sep3B (p + 1) (m + 2) (k + 1) d2 R_tail) =
    (.CB,
      [.item (.run 0), .item (.run 0), .item (.run 1), .rep2 (p + 3), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .rep12 m,
       .item (.run 1), .item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 1), .item (.run 0), .item (.run 1),
       .item (.run 0), .item .zero, .item (.run 1), .repB1 k, .item (.run 0)],
      .item .zero :: .item (.run (d2 + 4)) :: R_tail) := rfl
  have heq : (evalSym target_tm) (iterStep stepPure 98 (stateB sep3B sep3B (p + 1) (m + 2) (k + 1)
      d2 R_tail)) =
      (evalSym target_tm) (stateB sep3B sep3B (p + 3) (m + 1) k (d2 + 4) R_tail) := by
    rw [hrfl]
    simp only [stateB, sep3B, evalSym, encSymL, List.cons_append, List.nil_append,
        repBlock12_snoc]
  exact heq ▸ h

def bOffset (flag : Bool) (s_sep m_sep : List SymTok) : Nat :=
  if s_sep = sep3A then (if m_sep = sep3A then (fcost flag 506 458) else (fcost flag 436 396))
  else (if m_sep = sep3A then (fcost flag 354 322) else (fcost flag 284 260))

theorem ruleB_step_exact (s_sep m_sep : List SymTok)
    (hs : s_sep = sep3A ∨ s_sep = sep3B) (hm : m_sep = sep3A ∨ m_sep = sep3B)
    (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm ((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(bOffset flag s_sep m_sep+(fcost flag 542 484)))
      (evalSym target_tm (stateB s_sep m_sep (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB s_sep m_sep (p+3) (m+1) k (d2+4) R_tail)) := by
  rcases hs with rfl | rfl <;> rcases hm with rfl | rfl
  · cases flag <;> exact rules.ruleB_step_AA_exact p m k d2 R_tail
  · cases flag <;> exact rules.ruleB_step_AB_exact p m k d2 R_tail
  · cases flag <;> exact rules.ruleB_step_BA_exact p m k d2 R_tail
  · cases flag <;> exact rules.ruleB_step_BB_exact p m k d2 R_tail

theorem ruleB_iter_exact (s_sep m_sep : List SymTok)
    (hs : s_sep = sep3A ∨ s_sep = sep3B) (hm : m_sep = sep3A ∨ m_sep = sep3B)
    (n p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (n*((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 238 212)*n+bOffset flag s_sep m_sep+(fcost flag 304 272)))
      (evalSym target_tm (stateB s_sep m_sep (p+1) (m+n+1) (k+n) d2 R_tail))
      (evalSym target_tm (stateB s_sep m_sep (p+1+2*n) (m+1) k (d2+4*n) R_tail)) := by
  induction n generalizing p m k d2 with
  | zero => simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero]; rfl
  | succ n ih =>
    have h1 : m+(n+1)+1 = (m+n)+2 := by omega
    have h2 : k+(n+1) = (k+n)+1 := by omega
    have h3 : p+1+2*(n+1) = (p+2)+1+2*n := by omega
    have h4 : d2+4*(n+1) = (d2+4)+4*n := by omega
    have hc : ((fcost flag 152 136)*p+(fcost flag 140 124)*(m+n)+(fcost flag 32 28)*(k+n)+(bOffset flag s_sep m_sep+(fcost flag 542 484)))+
        n*((fcost flag 152 136)*(p+2)+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 238 212)*n+bOffset flag s_sep m_sep+(fcost flag 304 272)) =
        (n+1)*((fcost flag 152 136)*p+(fcost flag 140 124)*m+(fcost flag 32 28)*k+(fcost flag 238 212)*(n+1)+bOffset flag s_sep m_sep+(fcost flag 304 272)) := by
      cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] <;> ring
    rw [←hc,h1,h2,h3,h4]
    exact ReachesIn.trans (rules.ruleB_step_exact s_sep m_sep hs hm p (m+n) (k+n) d2 R_tail)
      (ih (p+2) m k (d2+4))











#print axioms ruleA_iter_exact
#print axioms ruleB_iter_exact
#print axioms ruleC_iter_exact
end BB6.Agent49.CountedSym.CountedAtoms
end
