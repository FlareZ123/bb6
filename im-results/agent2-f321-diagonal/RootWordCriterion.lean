import WordExactThreshold
import TerminalFeederPartition
import Phase6Bridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321RootWord
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321WordGuard
open BB6.Agent2F321ExactThreshold
open BB6.Agent2F321TerminalFeeder
open BB6.Agent2F321Phase6Bridge

/-- Chronological words concatenate without weakening their guards. -/
theorem word_append {u v a d A D B C} (hu : WordRun u a d A D)
    (hv : WordRun v A D B C) : WordRun (u++v) a d B C := by
  induction hu with
  | nil => exact hv
  | high hg _ ih => exact WordRun.high hg (ih hv)
  | far h1 h2 _ ih => exact WordRun.far h1 h2 (ih hv)

theorem word_reach {s r n w a d A D}
    (hr : CounterReach s r n a d) (hw : WordRun w a d A D) :
    CounterReach s r (n+w.length) A D := by
  induction hw generalizing n with
  | nil => simpa using hr
  | high hg _ ih =>
      have ht := ih (CounterReach.step hr (CounterMove.high _ _ hg))
      simpa [Nat.add_assoc,Nat.add_comm 1] using ht
  | far h1 h2 _ ih =>
      have ht := ih (CounterReach.step hr (CounterMove.far _ _ h1 h2))
      simpa [Nat.add_assoc,Nat.add_comm 1] using ht

/-- A source orbit ends in a reachable small-second reset anchor followed by
    a word of High/Far moves. Preserve the exact total number of moves. -/
theorem reach_anchor_word {n A D} (hr : CounterReach 1 1 n A D) :
    ∃ m R c w, n=m+w.length ∧ CounterReach 1 1 m R c ∧
      (c=1 ∨ c=2) ∧ WordRun w R c A D := by
  induction hr with
  | nil => exact ⟨0,1,1,[],rfl,CounterReach.nil,Or.inl rfl,WordRun.nil _ _⟩
  | @step n a d A D hr hm ih =>
      rcases ih with ⟨m,R,c,w,hn,hroot,hc,hw⟩
      cases hm with
      | high d hg =>
          refine ⟨m,R,c,w++[.high],by simp; omega,hroot,hc,?_⟩
          exact word_append hw (WordRun.high hg (WordRun.nil _ _))
      | far d h1 h2 =>
          refine ⟨m,R,c,w++[.far],by simp; omega,hroot,hc,?_⟩
          exact word_append hw (WordRun.far h1 h2 (WordRun.nil _ _))
      | equal =>
          exact ⟨n+1,_,1,[],by simp,CounterReach.step hr (CounterMove.equal _),Or.inl rfl,WordRun.nil _ _⟩
      | middleEven d h1 h2 hp =>
          exact ⟨n+1,_,2,[],by simp,CounterReach.step hr (CounterMove.middleEven _ _ h1 h2 hp),Or.inr rfl,WordRun.nil _ _⟩
      | middleOdd d h1 h2 hp =>
          exact ⟨n+1,_,1,[],by simp,CounterReach.step hr (CounterMove.middleOdd _ _ h1 h2 hp),Or.inl rfl,WordRun.nil _ _⟩

/-- Strip the entire leading High prefix; the remainder is empty or starts Far. -/
theorem word_split_high {w a d A D} (hw : WordRun w a d A D) :
    ∃ h u B C, w.length=h+u.length ∧ HighRun h a d B C ∧
      WordRun u B C A D ∧ (u=[] ∨ ∃ v, u=.far::v) := by
  induction hw with
  | nil =>
      exact ⟨0,[],_,_,rfl,HighRun.nil _ _,WordRun.nil _ _,Or.inl rfl⟩
  | @high w a d A D hg ht ih =>
      rcases ih with ⟨h,u,B,C,hlen,hh,hu,hshape⟩
      exact ⟨h+1,u,B,C,by simp; omega,HighRun.step hg hh,hu,hshape⟩
  | @far w a d A D h1 h2 ht ih =>
      exact ⟨0,.far::w,a,d,by simp,HighRun.nil _ _,WordRun.far h1 h2 ht,Or.inr ⟨w,rfl⟩⟩

/-- Arithmetic candidate computed from a word and leading High length. -/
def candidateNumerator (h : Nat) (w : List InverseLetter) (c : Nat) : Nat :=
  P w*(2^h*(c+3))+K w

def candidateScale (h : Nat) (w : List InverseLetter) (c : Nat) : Nat :=
  candidateNumerator h w c / Q w

/-- Exact, executable dangerous-anchor test for a particular finite word and
    leading High count. No witness for a terminal state is quantified. -/
def Danger (h : Nat) (w : List InverseLetter) (R c : Nat) : Prop :=
  (w=[] ∨ ∃ v, w=.far::v) ∧
  Q w ∣ candidateNumerator h w c ∧
  3≤candidateScale h w c ∧
  R+c+h+5+L w=2*candidateScale h w c ∧
  exactMin w≤candidateScale h w c ∧
  2^h*(c+3)+L w+2≤2*candidateScale h w c

/-- For fixed word and h, the arithmetic test is exactly the existence of a
    guarded terminal path, with its unique terminal parameter. -/
theorem danger_iff {h w R c} : Danger h w R c ↔
    (w=[] ∨ ∃ v, w=.far::v) ∧ ∃ t, PrefixTail h w R c t := by
  constructor
  · rintro ⟨hs,hd,h3,hx,hm,ha⟩
    let T := candidateScale h w c
    let t := T-3
    have ht : t+3=T := by dsimp [T,t]; omega
    have he : Q w*T=candidateNumerator h w c := by
      unfold T candidateScale
      rw [Nat.mul_comm,Nat.div_mul_cancel hd]
    refine ⟨hs,t,(prefix_tail_iff_exactMin h w R c t).mpr ?_⟩
    rw [ht]
    exact ⟨hx,he,hm,ha⟩
  · rintro ⟨hs,t,hr⟩
    have he := (prefix_tail_iff_exactMin h w R c t).mp hr
    have hn : candidateNumerator h w c=Q w*(t+3) := he.2.1.symm
    have hT : candidateScale h w c=t+3 := by
      unfold candidateScale
      rw [hn,Nat.mul_comm,Nat.mul_div_cancel _ (Q_pos w)]
    refine ⟨hs,⟨t+3,hn⟩,by omega,?_,?_,?_⟩ <;> rw [hT]
    · exact he.1
    · exact he.2.2.1
    · exact he.2.2.2

/-- The missing F321 source decision is exactly root reachability of an
    arithmetically specified dangerous anchor. Both implications preserve
    genuine guards and the original source relation. -/
theorem root_terminal_iff_danger :
    (∃ n t, CounterReach 1 1 n (t+1) t) ↔
    ∃ m R c h w, CounterReach 1 1 m R c ∧ (c=1 ∨ c=2) ∧ Danger h w R c := by
  constructor
  · rintro ⟨n,t,hr⟩
    rcases reach_anchor_word hr with ⟨m,R,c,w,hn,hroot,hc,hw⟩
    rcases word_split_high hw with ⟨h,u,B,C,hlen,hh,hu,hs⟩
    exact ⟨m,R,c,h,u,hroot,hc,danger_iff.mpr ⟨hs,t,B,C,hh,hu⟩⟩
  · rintro ⟨m,R,c,h,w,hroot,hc,hd⟩
    rcases danger_iff.mp hd with ⟨_,t,B,C,hh,hw⟩
    exact ⟨m+h+w.length,t,word_reach (highRun_append hroot hh) hw⟩

#print axioms reach_anchor_word
#print axioms word_split_high
#print axioms danger_iff
#print axioms root_terminal_iff_danger
end BB6.Agent2F321RootWord
