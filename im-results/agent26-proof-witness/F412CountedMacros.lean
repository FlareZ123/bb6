module
import all F412CountedPure
import SourceAffineBlocks
import SourceCostModel
import all BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA
import all BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine BB6.Agent11.SourceCost
open BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

namespace Agent26F412
set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/-! Source-anchored macro counts. Endpoint identities reuse the original
HaltShared ruleA_step_eq and ruleC_step_eq, and the original ruleB_step
endpoint proof snippets (with exact count replaced for existential reach).
The arithmetic formulae are those derived by Agent11, proved directly
in closed form to avoid unfolding the symbolic iteration. -/

theorem ruleA0_exact (k d : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (28*k+284)
      (evalSym target_tm (stateA0 (k+1) (d+6) R_tail))
      (evalSym target_tm (stateA 0 k d R_tail)) := by
  have h := costIter_exact 46 (stateA0 (k+1) (d+6) R_tail)
  rw [BB6.Agent26.SourceAffine.a0_false] at h
  exact h

theorem ruleA_step_exact (m k d : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (124*m+28*k+408)
      (evalSym target_tm (stateA m (k+1) (d+6) R_tail))
      (evalSym target_tm (stateA (m+1) k d R_tail)) := by
  have h := costIter_exact 66 (stateA m (k+1) (d+6) R_tail)
  rw [BB6.Agent26.SourceAffine.a_false, ruleA_step_eq] at h
  exact h

theorem ruleA_iter_exact (n m k d : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (n*(124*m+28*k+76*n+332))
      (evalSym target_tm (stateA m (k+n) (d+6*n) R_tail))
      (evalSym target_tm (stateA (m+n) k d R_tail)) := by
  induction n generalizing m k d with
  | zero => simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero]; rfl
  | succ n ih =>
    have h1 : k+(n+1) = (k+n)+1 := by omega
    have h2 : d+6*(n+1) = (d+6*n)+6 := by omega
    have h3 : m+(n+1) = (m+1)+n := by omega
    have hc : (124*m+28*(k+n)+408)+n*(124*(m+1)+28*k+76*n+332) =
        (n+1)*(124*m+28*k+76*(n+1)+332) := by ring
    rw [←hc,h1,h2,h3]
    exact reachesIn_trans (ruleA_step_exact m (k+n) (d+6*n) R_tail) (ih (m+1) k d)

theorem ruleC_step_exact (p k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (68*p+56*k+434)
      (evalSym target_tm (stateC (p+3) (k+1) d2 R_tail))
      (evalSym target_tm (stateC (p+2) (k+3) (d2+2) R_tail)) := by
  have h := costIter_exact 46 (stateC (p+3) (k+1) d2 R_tail)
  rw [BB6.Agent26.SourceAffine.c_false,ruleC_step_eq] at h
  exact h

theorem ruleC_iter_exact (n p k d2 : ℕ) (R_tail : List SymTok) (hk : 1 ≤ k) :
    ReachesIn target_tm (n*(68*p+56*k+90*n+288))
      (evalSym target_tm (stateC (p+n+2) k d2 R_tail))
      (evalSym target_tm (stateC (p+2) (k+2*n) (d2+2*n) R_tail)) := by
  induction n generalizing p k d2 with
  | zero => simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero]; rfl
  | succ n ih =>
    obtain ⟨k0,rfl⟩ : ∃ k0, k = k0+1 := ⟨k-1,by omega⟩
    have h1 : p+(n+1)+2 = (p+n)+3 := by omega
    have h2 : k0+1+2*(n+1) = (k0+3)+2*n := by omega
    have h3 : d2+2*(n+1) = (d2+2)+2*n := by omega
    have hc : (68*(p+n)+56*k0+434)+n*(68*p+56*(k0+3)+90*n+288) =
        (n+1)*(68*p+56*(k0+1)+90*(n+1)+288) := by ring
    rw [←hc,h1,h2,h3]
    exact reachesIn_trans (ruleC_step_exact (p+n) k0 d2 R_tail)
      (ih p (k0+3) (d2+2) (by omega))

theorem ruleB_step_AA_exact (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (136*p+124*m+28*k+942)
      (evalSym target_tm (stateB sep3A sep3A (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3A sep3A (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := costIter_exact 126 (stateB sep3A sep3A (p+1) (m+2) (k+1) d2 R_tail)
  rw [BB6.Agent26.SourceAffine.bAA_false] at h
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
    ReachesIn target_tm (136*p+124*m+28*k+880)
      (evalSym target_tm (stateB sep3A sep3B (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3A sep3B (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := costIter_exact 118 (stateB sep3A sep3B (p+1) (m+2) (k+1) d2 R_tail)
  rw [BB6.Agent26.SourceAffine.bAB_false] at h
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
    ReachesIn target_tm (136*p+124*m+28*k+806)
      (evalSym target_tm (stateB sep3B sep3A (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3B sep3A (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := costIter_exact 106 (stateB sep3B sep3A (p+1) (m+2) (k+1) d2 R_tail)
  rw [BB6.Agent26.SourceAffine.bBA_false] at h
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
    ReachesIn target_tm (136*p+124*m+28*k+744)
      (evalSym target_tm (stateB sep3B sep3B (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB sep3B sep3B (p+3) (m+1) k (d2+4) R_tail)) := by
  have h := costIter_exact 98 (stateB sep3B sep3B (p+1) (m+2) (k+1) d2 R_tail)
  rw [BB6.Agent26.SourceAffine.bBB_false] at h
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

def bOffset (s_sep m_sep : List SymTok) : Nat :=
  if s_sep = sep3A then (if m_sep = sep3A then 458 else 396)
  else (if m_sep = sep3A then 322 else 260)

theorem ruleB_step_exact (s_sep m_sep : List SymTok)
    (hs : s_sep = sep3A ∨ s_sep = sep3B) (hm : m_sep = sep3A ∨ m_sep = sep3B)
    (p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (136*p+124*m+28*k+(bOffset s_sep m_sep+484))
      (evalSym target_tm (stateB s_sep m_sep (p+1) (m+2) (k+1) d2 R_tail))
      (evalSym target_tm (stateB s_sep m_sep (p+3) (m+1) k (d2+4) R_tail)) := by
  rcases hs with rfl | rfl <;> rcases hm with rfl | rfl
  · exact ruleB_step_AA_exact p m k d2 R_tail
  · exact ruleB_step_AB_exact p m k d2 R_tail
  · exact ruleB_step_BA_exact p m k d2 R_tail
  · exact ruleB_step_BB_exact p m k d2 R_tail

theorem ruleB_iter_exact (s_sep m_sep : List SymTok)
    (hs : s_sep = sep3A ∨ s_sep = sep3B) (hm : m_sep = sep3A ∨ m_sep = sep3B)
    (n p m k d2 : ℕ) (R_tail : List SymTok) :
    ReachesIn target_tm (n*(136*p+124*m+28*k+212*n+bOffset s_sep m_sep+272))
      (evalSym target_tm (stateB s_sep m_sep (p+1) (m+n+1) (k+n) d2 R_tail))
      (evalSym target_tm (stateB s_sep m_sep (p+1+2*n) (m+1) k (d2+4*n) R_tail)) := by
  induction n generalizing p m k d2 with
  | zero => simp only [Nat.zero_mul,Nat.add_zero,Nat.mul_zero]; rfl
  | succ n ih =>
    have h1 : m+(n+1)+1 = (m+n)+2 := by omega
    have h2 : k+(n+1) = (k+n)+1 := by omega
    have h3 : p+1+2*(n+1) = (p+2)+1+2*n := by omega
    have h4 : d2+4*(n+1) = (d2+4)+4*n := by omega
    have hc : (136*p+124*(m+n)+28*(k+n)+(bOffset s_sep m_sep+484))+
        n*(136*(p+2)+124*m+28*k+212*n+bOffset s_sep m_sep+272) =
        (n+1)*(136*p+124*m+28*k+212*(n+1)+bOffset s_sep m_sep+272) := by ring
    rw [←hc,h1,h2,h3,h4]
    exact reachesIn_trans (ruleB_step_exact s_sep m_sep hs hm p (m+n) (k+n) d2 R_tail)
      (ih (p+2) m k (d2+4))

#print axioms ruleA0_exact
#print axioms ruleA_step_exact
#print axioms ruleA_iter_exact
#print axioms ruleC_step_exact
#print axioms ruleC_iter_exact
#print axioms ruleB_step_AA_exact
#print axioms ruleB_step_AB_exact
#print axioms ruleB_step_BA_exact
#print axioms ruleB_step_BB_exact
#print axioms ruleB_step_exact
#print axioms ruleB_iter_exact
end Agent26F412
