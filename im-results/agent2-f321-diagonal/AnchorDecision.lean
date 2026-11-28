import PrunedAnchorCover
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321AnchorDecision
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord
open BB6.Agent2F321PrefixSparsity
open BB6.Agent2F321DangerCount
open BB6.Agent2F321AffinePrefix
open BB6.Agent2F321PrunedCover

inductive Outcome where
  | reset | terminal | unknown
  deriving DecidableEq, Repr

/-- The exact H/F suborbit decision, with a conservative unknown outcome.
    A reset here means an Equal or Middle branch is the next source move. -/
def decideTail : Nat → Nat → Nat → Outcome
  | 0, a, d => if a=d+1 then .terminal else .unknown
  | n+1, a, d =>
      if d+2≤a then decideTail n (a-d-2) (2*d+3)
      else if a=d+1 then .terminal
      else if 3*a+1≤d then decideTail n (4*a+6) (d-3*a)
      else .reset

theorem reset_no_terminal {n a d} (hr : decideTail n a d=.reset) :
    ¬∃ w t, WordRun w a d (t+1) t := by
  induction n generalizing a d with
  | zero =>
      unfold decideTail at hr
      split at hr <;> contradiction
  | succ n ih =>
      unfold decideTail at hr
      split at hr
      · rename_i hg
        rintro ⟨w,t,hw⟩
        cases hw with
        | nil => omega
        | high h ht => exact ih hr ⟨_,_,ht⟩
        | far h1 h2 ht => omega
      · rename_i hn
        split at hr
        · contradiction
        · rename_i ht
          split at hr
          · rename_i hg
            rintro ⟨w,t,hw⟩
            cases hw with
            | nil => omega
            | high h ht => omega
            | far h1 h2 ht => exact ih hr ⟨_,_,ht⟩
          · rename_i hf
            rintro ⟨w,t,hw⟩
            cases hw with
            | nil => omega
            | high h ht => omega
            | far h1 h2 ht => omega

theorem terminal_has_word {n a d} (hr : decideTail n a d=.terminal) :
    ∃ w t, WordRun w a d (t+1) t := by
  induction n generalizing a d with
  | zero =>
      unfold decideTail at hr
      split at hr
      · rename_i he
        subst a
        exact ⟨[],d,WordRun.nil _ _⟩
      · contradiction
  | succ n ih =>
      unfold decideTail at hr
      split at hr
      · rename_i hg
        rcases ih hr with ⟨w,t,hw⟩
        exact ⟨.high::w,t,WordRun.high hg hw⟩
      · rename_i hn
        split at hr
        · rename_i he
          subst a
          exact ⟨[],d,WordRun.nil _ _⟩
        · split at hr
          · rename_i hg
            rcases ih hr with ⟨w,t,hw⟩
            exact ⟨.far::w,t,WordRun.far (by omega) hg hw⟩
          · contradiction

theorem high_word {h R c a d} (hh : HighRun h R c a d) :
    WordRun (List.replicate h .high) R c a d := by
  induction hh with
  | nil => exact WordRun.nil _ _
  | step hg ht ih => simpa [List.replicate_succ] using WordRun.high hg ih

theorem dangerous_iff_word {R c} (hc : c=1∨c=2) :
    DangerousAnchor R c ↔ ∃ w t, WordRun w R c (t+1) t := by
  constructor
  · rintro ⟨_,h,w,hd⟩
    rcases danger_iff.mp hd with ⟨_,t,a,d,hh,hw⟩
    exact ⟨_,t,word_append (high_word hh) hw⟩
  · rintro ⟨w,t,hw⟩
    rcases word_split_high hw with ⟨h,u,a,d,_,hh,hu,hs⟩
    exact ⟨hc,h,u,danger_iff.mpr ⟨hs,t,a,d,hh,hu⟩⟩

/-- Retain every potential dangerous pair; only certified reset outcomes
    are discarded. -/
def filteredCover (k fuel : Nat) : List (Nat×Nat) :=
  (prunedCover k).filter (fun p => decideTail fuel p.1 p.2 != .reset)

theorem filtered_cover_complete {k fuel R c} (hk : 2≤k) (hR : R≤2^k)
    (hd : DangerousAnchor R c) : (R,c)∈filteredCover k fuel := by
  have hm := pruned_cover_complete hk hR hd
  have hw := (dangerous_iff_word hd.1).mp hd
  have hn : decideTail fuel R c≠.reset := fun he => reset_no_terminal he hw
  unfold filteredCover
  exact List.mem_filter.mpr ⟨hm,by simp [hn]⟩

/-- A separate exact terminal list, with no false positive on small-second
    anchors. -/
def terminalCover (k fuel : Nat) : List (Nat×Nat) :=
  (prunedCover k).filter (fun p => decideTail fuel p.1 p.2 == .terminal)

theorem terminal_cover_sound {k fuel R c} (hc : c=1∨c=2)
    (hm : (R,c)∈terminalCover k fuel) : DangerousAnchor R c := by
  unfold terminalCover at hm
  have he : decideTail fuel R c=.terminal := by simpa using (List.mem_filter.mp hm).2
  exact (dangerous_iff_word hc).mpr (terminal_has_word he)

/-- When no candidate is unknown, the computed terminal list is complete. -/
theorem exact_cover_of_resolved {k fuel R c} (hk : 2≤k) (hR : R≤2^k)
    (hc : c=1∨c=2)
    (hresolve : ∀ p∈prunedCover k, decideTail fuel p.1 p.2≠.unknown) :
    DangerousAnchor R c ↔ (R,c)∈terminalCover k fuel := by
  constructor
  · intro hd
    have hm := pruned_cover_complete hk hR hd
    have hn := hresolve (R,c) hm
    have hnr : decideTail fuel R c≠.reset := fun he =>
      reset_no_terminal he ((dangerous_iff_word hc).mp hd)
    have he : decideTail fuel R c=.terminal := by
      cases h : decideTail fuel R c <;> simp_all
    exact List.mem_filter.mpr ⟨hm,by simp [he]⟩
  · exact terminal_cover_sound hc

#print axioms reset_no_terminal
#print axioms terminal_has_word
#print axioms dangerous_iff_word
#print axioms exact_cover_of_resolved
end BB6.Agent2F321AnchorDecision
