import BB429Branch29All
import Branch29Extra1024
import Branch29Extra2048
import Lean.Elab.Tactic.Omega

/-!
# Exact necessary 31/2048 residue roster for #429 branch29 blank-root feeder

Combines the previously accepted globally rooted 38/1024 theorem with
eight new complete 1024-class exclusions and 29 further 2048-class
exclusions. The final roster is a *necessary* condition for ever reaching
(32q+29,64q+55) in the authentic blank-root accelerator.

The arithmetic partition checks only the 38 existing possibilities,
at both lifts modulo 2048, rather than enumerating 2048 cases.
-/

namespace BB429Branch29Roster31
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def surviving2048 : List Nat :=
  [2,111,127,239,338,399,495,570,575,655,714,850,879,895,954,1023,
   1087,1106,1210,1226,1282,1343,1410,1482,1666,1791,1850,1855,
   1935,1994,2047]

theorem roster_count : surviving2048.length = 31 := by decide

private def partitionRow (r : Nat) : Prop :=
  (r ∈ BB429Branch29Extra1024.cutResidues ∨
   r ∈ BB429Branch29Extra2048.extra2048 ∨ r ∈ surviving2048) ∧
  (r ∈ BB429Branch29Extra1024.cutResidues ∨
   r+1024 ∈ BB429Branch29Extra2048.extra2048 ∨ r+1024 ∈ surviving2048)

private instance (r : Nat) : Decidable (partitionRow r) := by
  unfold partitionRow
  infer_instance

private theorem partition38 :
    BB429Branch29Reflect1024.surviving1024.all
      (fun r => decide (partitionRow r)) = true := by
  decide +kernel

theorem residue_partition (q : Nat)
    (h38 : q%1024 ∈ BB429Branch29Reflect1024.surviving1024)
    (h8 : q%1024 ∉ BB429Branch29Extra1024.cutResidues)
    (h29 : q%2048 ∉ BB429Branch29Extra2048.extra2048) :
    q%2048 ∈ surviving2048 := by
  have hp : partitionRow (q%1024) :=
    of_decide_eq_true ((List.all_eq_true.mp partition38) (q%1024) h38)
  rcases hp with ⟨hp0,hp1⟩
  have hsplit : q%2048=q%1024 ∨ q%2048=q%1024+1024 := by omega
  rcases hsplit with hz | hz
  · rcases hp0 with hcut | hcut | hok
    · exact False.elim (h8 hcut)
    · exact False.elim (h29 (hz ▸ hcut))
    · exact hz ▸ hok
  · rcases hp1 with hcut | hcut | hok
    · exact False.elim (h8 hcut)
    · exact False.elim (h29 (hz ▸ hcut))
    · exact hz ▸ hok

/-- Necessary reachability condition for the complete blank-root
29(mod32) pre-reset branch. Every q is covered: no finite time horizon
and no assumption of positivity beyond the natural-number counters. -/
theorem rooted_29_q_31_mod2048 (q : Nat)
    (hroot : BB429NewResidue.Reach (32*q+29) (64*q+55)) :
    21 ≤ q ∧ q%2048 ∈ surviving2048 := by
  have h38 := BB429Branch29All.rooted_29_global q hroot
  have h8 : q%1024 ∉ BB429Branch29Extra1024.cutResidues := by
    intro hcut
    exact (BB429Branch29Extra1024.eight_cylinders_unreachable q hcut) hroot
  have h29 : q%2048 ∉ BB429Branch29Extra2048.extra2048 := by
    intro hcut
    exact (BB429Branch29Extra2048.twenty_nine_cylinders_unreachable q hcut) hroot
  exact ⟨h38.1, residue_partition q h38.2 h8 h29⟩

#print axioms rooted_29_q_31_mod2048
end BB429Branch29Roster31
