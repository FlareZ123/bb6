import TotalFastInverse
import SectionMassOriginal
import EvenOddTwoParentRoot
import Std.Data.HashMap.Lemmas
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
namespace BB6.Agent13ExactMemo
abbrev P := Nat × Nat
abbrev Cache := Std.HashMap P Bool

def allVisit (visit : P → Cache → Bool × Cache) : List P → Cache → Bool × Cache
  | [],c => (true,c)
  | p::ps,c => let (v,c'):=visit p c; if v then allVisit visit ps c' else (false,c')

def cacheSound (reach : P → Prop) (c : Cache) : Prop :=
  ∀ p, c[p]?=some true → ¬reach p

private theorem insert_sound (reach : P → Prop) (c : Cache) (p : P)
    (hc : cacheSound reach c) (hp : ¬reach p) : cacheSound reach (c.insert p true) := by
  intro q hq
  rw [Std.HashMap.getElem?_insert] at hq
  by_cases h : p=q
  · subst q; exact hp
  · simp [h] at hq
    exact hc q hq

private theorem allVisit_sound (reach : P → Prop) (visit : P → Cache → Bool × Cache)
    (ps : List P) (c : Cache) (hc : cacheSound reach c)
    (hv : ∀ p∈ps, ∀ c, cacheSound reach c →
      ((visit p c).1=true → ¬reach p) ∧ cacheSound reach (visit p c).2) :
    ((allVisit visit ps c).1=true → ∀ p∈ps, ¬reach p) ∧
      cacheSound reach (allVisit visit ps c).2 := by
  induction ps generalizing c with
  | nil => simp [allVisit,hc]
  | cons p ps ih =>
    obtain ⟨hs,hcs⟩ := hv p (by simp) c hc
    cases he : visit p c with
    | mk v c' =>
      rw [he] at hs hcs
      cases v
      · simp [allVisit,he,hcs]
      · obtain ⟨ht,hct⟩:=ih c' hcs (fun q hq => hv q (by simp [hq]))
        simp only [allVisit,he,ite_true]
        exact ⟨fun h q hq => by
          rcases List.mem_cons.mp hq with hq|hq
          · subst q; exact hs rfl
          · exact ht h q hq,hct⟩

private theorem allVisit_complete (reach : P → Prop) (visit : P → Cache → Bool × Cache)
    (ps : List P) (c : Cache) (hc : cacheSound reach c)
    (hv : ∀ p∈ps, ∀ c, cacheSound reach c →
      ((visit p c).1=true) ∧ cacheSound reach (visit p c).2) :
    (allVisit visit ps c).1=true ∧ cacheSound reach (allVisit visit ps c).2 := by
  induction ps generalizing c with
  | nil => exact ⟨rfl,hc⟩
  | cons p ps ih =>
    obtain ⟨hs,hcs⟩ := hv p (by simp) c hc
    cases he : visit p c with
    | mk v c' =>
      rw [he] at hs hcs
      subst v
      simpa only [allVisit,he,ite_true] using ih c' hcs (fun q hq => hv q (by simp [hq]))

/-- Cache only proved excluded states; failure never contaminates a later call with more fuel. -/
def memo (parents : P → List P) (bad : P → Bool) (seed : P) :
    Nat → P → Cache → Bool × Cache
  | f,p,c =>
    if c[p]? == some true then (true,c)
    else if bad p then (true,c.insert p true)
    else if p=seed then (false,c)
    else match f with
      | 0 => (false,c)
      | f+1 =>
        let (v,c'):=allVisit (memo parents bad seed f) (parents p) c
        if v then (true,c'.insert p true) else (false,c')

theorem memo_sound (parents : P → List P) (bad : P → Bool) (seed : P)
    (reach : P → Prop)
    (hreach : ∀ p, reach p ↔ p=seed ∨ ∃ q∈parents p, reach q)
    (hbad : ∀ p, bad p=true → ¬reach p)
    (f : Nat) (p : P) (c : Cache) (hc : cacheSound reach c) :
    ((memo parents bad seed f p c).1=true → ¬reach p) ∧
      cacheSound reach (memo parents bad seed f p c).2 := by
  induction f generalizing p c with
  | zero =>
    unfold memo
    split
    next h => exact ⟨fun _ => hc p (by simpa using h),hc⟩
    next _ =>
      split
      next h => exact ⟨fun _ => hbad p h,insert_sound reach c p hc (hbad p h)⟩
      next _ => split <;> simp [hc]
  | succ f ih =>
    unfold memo
    split
    next h => exact ⟨fun _ => hc p (by simpa using h),hc⟩
    next _ =>
      split
      next h => exact ⟨fun _ => hbad p h,insert_sound reach c p hc (hbad p h)⟩
      next _ =>
        split
        next h => simp [hc]
        next hp =>
          obtain ⟨hs,hcs⟩:=allVisit_sound reach (memo parents bad seed f) (parents p) c hc
            (fun q _ c hc => ih q c hc)
          cases he : allVisit (memo parents bad seed f) (parents p) c with
          | mk v c' =>
            rw [he] at hs hcs
            cases v
            · simp [he,hcs]
            · have hn : ¬reach p := by
                intro hr
                rcases (hreach p).mp hr with h|⟨q,hm,hq⟩
                · exact hp h
                · exact hs rfl q hm hq
              simp only [he,Prod.fst,Prod.snd,ite_true]
              exact ⟨fun _=>hn,insert_sound reach c' p hcs hn⟩

theorem memo_complete (parents : P → List P) (bad : P → Bool) (seed : P)
    (reach : P → Prop) (rank : P → Nat)
    (hreach : ∀ p, reach p ↔ p=seed ∨ ∃ q∈parents p, reach q)
    (hbad : ∀ p, bad p=true → ¬reach p)
    (hrank : ∀ p q, q∈parents p → rank q < rank p)
    (f : Nat) (p : P) (c : Cache) (hc : cacheSound reach c)
    (hf : rank p < f) (hn : ¬reach p) : (memo parents bad seed f p c).1=true := by
  induction f generalizing p c with
  | zero => omega
  | succ f ih =>
    unfold memo
    split
    · rfl
    · split
      · rfl
      · split
        next h => exact False.elim (hn ((hreach p).mpr (Or.inl h)))
        next _ =>
          have h := allVisit_complete reach (memo parents bad seed f) (parents p) c hc (fun q hm c hc => by
            have hq : ¬reach q := fun hr => hn ((hreach p).mpr (Or.inr ⟨q,hm,hr⟩))
            have hlt := hrank p q hm
            exact ⟨ih q c hc (by omega) hq,(memo_sound parents bad seed reach hreach hbad f q c hc).2⟩)
          cases he : allVisit (memo parents bad seed f) (parents p) c with
          | mk v c' =>
            rw [he] at h
            have hv : v=true := h.1
            subst v
            simp [he]

def exclude (parents : P → List P) (bad : P → Bool) (seed : P) (f : Nat) (p : P) : Bool :=
  (memo parents bad seed f p {}).1

theorem exclude_sound (parents : P → List P) (bad : P → Bool) (seed : P)
    (reach : P → Prop)
    (hreach : ∀ p, reach p ↔ p=seed ∨ ∃ q∈parents p, reach q)
    (hbad : ∀ p, bad p=true → ¬reach p)
    (f : Nat) (p : P) (h : exclude parents bad seed f p=true) : ¬reach p := by
  apply (memo_sound parents bad seed reach hreach hbad f p {} ?_).1 h
  intro q hq; simp at hq

theorem exclude_complete (parents : P → List P) (bad : P → Bool) (seed : P)
    (reach : P → Prop) (rank : P → Nat)
    (hreach : ∀ p, reach p ↔ p=seed ∨ ∃ q∈parents p, reach q)
    (hbad : ∀ p, bad p=true → ¬reach p)
    (hrank : ∀ p q, q∈parents p → rank q < rank p)
    (f : Nat) (p : P) (hf : rank p < f) (hn : ¬reach p) : exclude parents bad seed f p=true := by
  apply memo_complete parents bad seed reach rank hreach hbad hrank f p {} ?_ hf hn
  intro q hq; simp at hq

open BB6.Agent46 BB6.Agent8Section BB6.Agent11Mass BB6.Agent15TotalFast

def sourceParents (p : P) := totalFastCandidates p.1 p.2
def sourceBad (p : P) : Bool := decide (5≤p.2 ∧ p.2%2=1 ∧ ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))
def sourceReach (p : P) : Prop := BB6.Agent3.CReach p.1 p.2
def sourceRank (p : P) : Nat := (p.1+2*p.2)/2

theorem sourceReach_iff (p : P) : sourceReach p ↔ p=(5,1) ∨ ∃ q∈sourceParents p, sourceReach q := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
      left
      simpa [BB6.Agent8Section.run] using hn.symm
    | succ n =>
      change (run secNext n (some (5,1))).bind secNext = some p at hn
      cases he : run secNext n (some (5,1)) with
      | none => simp [he] at hn
      | some q =>
        have hnext : secNext q=some p := by simpa [he] using hn
        right
        exact ⟨q,(totalFastCandidates_exact q.1 q.2 p.1 p.2).mpr hnext,⟨n,he⟩⟩
  · rintro (h|⟨q,hq,⟨n,hn⟩⟩)
    · subst p
      exact ⟨0,rfl⟩
    · refine ⟨n+1,?_⟩
      change (run secNext n (some (5,1))).bind secNext = some p
      rw [hn]
      exact (totalFastCandidates_exact q.1 q.2 p.1 p.2).mp hq

theorem sourceBad_sound (p : P) (h : sourceBad p=true) : ¬sourceReach p := by
  obtain ⟨hy,ho,hs⟩ := of_decide_eq_true h
  exact BB6.Agent13TwoParent.odd_forbidden_image p.1 p.2 hy ho hs

theorem sourceRank_lt (p q : P) (h : q∈sourceParents p) : sourceRank q < sourceRank p := by
  have he := (totalFastCandidates_exact q.1 q.2 p.1 p.2).mp h
  have hg := secNext_weight_growth q.1 q.2 p.1 p.2 he
  unfold sourceRank
  omega

def exactExcluded (f x y : Nat) : Bool := exclude sourceParents sourceBad (5,1) f (x,y)

theorem exactExcluded_sound (f x y : Nat) (h : exactExcluded f x y=true) :
    ¬BB6.Agent3.CReach x y :=
  exclude_sound sourceParents sourceBad (5,1) sourceReach sourceReach_iff sourceBad_sound f (x,y) h

/-- Complete exact decision at source-proved half-weight bound, with
memoization independent of arbitrary remaining depth. -/
def exactDecision (x y : Nat) : Bool := exactExcluded ((x+2*y)/2+1) x y

theorem exactDecision_iff (x y : Nat) :
    exactDecision x y=true ↔ ¬BB6.Agent3.CReach x y := by
  constructor
  · exact exactExcluded_sound _ x y
  · intro hn
    exact exclude_complete sourceParents sourceBad (5,1) sourceReach sourceRank
      sourceReach_iff sourceBad_sound sourceRank_lt _ (x,y) (by simp [sourceRank]) hn

#print axioms exactExcluded_sound
#print axioms exactDecision_iff
set_option maxHeartbeats 0 in
#eval ([0,2,3,6,8,10,15,16,22,27,47,82,91,159,163,170,271,328] : List Nat).filter
  (fun m => exactDecision 1 (2^(2*m+3)-(3*m+4)))
end BB6.Agent13ExactMemo
