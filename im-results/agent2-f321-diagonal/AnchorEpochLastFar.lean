import TerminalAnchorShape
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2F321AnchorEpochLastFar

open BB6.Agent31F321Density
open BB6.Agent31F321AnchorShape
open BB6.Agent31F321TerminalWordOneFarGeneral
open BB6.Agent2F321AnchorEpoch

private theorem pureHigh_length (b : Nat) :
    (pureHigh b).length = b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [pureHigh, prependHigh, ih]

/-- Every inverse word is either entirely High or has a final Far followed
by a pure-High suffix.  The prefix before that final Far is unrestricted. -/
theorem split_last_far (w : List InverseLetter) :
    (∃ b, w = pureHigh b) ∨
      ∃ p b, w = p ++ (.far :: pureHigh b) := by
  induction w with
  | nil =>
      exact Or.inl ⟨0, rfl⟩
  | cons x xs ih =>
      cases x with
      | high =>
          rcases ih with ⟨b,hb⟩ | ⟨p,b,hp⟩
          · exact Or.inl ⟨b+1, by simp [pureHigh, prependHigh, hb]⟩
          · exact Or.inr ⟨.high::p,b, by simp [hp]⟩
      | far =>
          rcases ih with ⟨b,hb⟩ | ⟨p,b,hp⟩
          · exact Or.inr ⟨[],b, by simp [hb]⟩
          · exact Or.inr ⟨.far::p,b, by simp [hp]⟩

/-- Along an all-High inverse path, the terminal second counter is exactly
doubled after adding three at every step. -/
theorem formalInversePath_pureHigh_denominator
    {b d R c : Nat}
    (hp : FormalInversePath (d:Int) (pureHigh b) (R:Int) (c:Int)) :
    (d:Int)+3 = (2:Int)^b * ((c:Int)+3) := by
  induction b generalizing R c with
  | zero =>
      simp [pureHigh, prependHigh] at hp
      cases hp
      simp
  | succ b ih =>
      simp only [pureHigh, prependHigh] at hp
      cases hp with
      | stepH hpTail ha hd =>
          have htail := ih hpTail
          have hdouble : (D:Int)+3 = 2*((c:Int)+3) := by omega
          calc
            (d:Int)+3 = (2:Int)^b*((D:Int)+3) := htail
            _ = (2:Int)^b*(2*((c:Int)+3)) := by rw [hdouble]
            _ = (2:Int)^(b+1)*((c:Int)+3) := by
              rw [pow_succ]
              ac_rfl

/-- Every root-reachable terminal inverse path has one of two exact tails:
either it is all High, forcing D+3 = 2^m(c+3), or its last Far is followed
by b Highs, forcing the parity-refined 2^b divisibility from the general
last-Far theorem.  The root anchor retains the exact residue shape. -/
theorem terminal_last_anchor_tail_split
    {n D : Nat}
    (h : CounterReach 1 1 (n+1) (D+1) D) :
    ∃ q R c m w,
      AnchorChain q 6 1 R c ∧
      (c=1 ∨ c=2) ∧
      w.length = m ∧
      FormalInversePath (D:Int) w (R:Int) (c:Int) ∧
      ((c=1 ∧ (R%8=6 ∨ R%24=14 ∨ R%24=8)) ∨
       (c=2 ∧ (R%8=2 ∨ R%16=14))) ∧
      ((∃ b, w = pureHigh b ∧
          (D:Int)+3 = (2:Int)^m * ((c:Int)+3)) ∨
       (∃ p b z, w = p ++ (.far :: pureHigh b) ∧
          (D:Int)+3 = (2:Int)^b*z ∧ z%2 = (b:Int)%2)) := by
  rcases terminal_last_anchor_strong_shape h with
    ⟨q,R,c,m,w,hchain,hc,hlen,hformal,hshape⟩
  rcases split_last_far w with hhigh | hfar
  · rcases hhigh with ⟨b,hword⟩
    have hlen' : (pureHigh b).length = m := by
      simpa [hword] using hlen
    have hb : b = m := by
      rw [pureHigh_length] at hlen'
      omega
    have hformal' :
        FormalInversePath (D:Int) (pureHigh b) (R:Int) (c:Int) := by
      simpa [hword] using hformal
    have hden := formalInversePath_pureHigh_denominator hformal'
    have hden' : (D:Int)+3 = (2:Int)^m*((c:Int)+3) := by
      simpa [hb] using hden
    exact ⟨q,R,c,m,w,hchain,hc,hlen,hformal,hshape,
      Or.inl ⟨b,hword,hden'⟩⟩
  · rcases hfar with ⟨p,b,hword⟩
    have hformal' :
        FormalInversePath (D:Int) (p ++ (.far :: pureHigh b))
          (R:Int) (c:Int) := by
      simpa [hword] using hformal
    obtain ⟨z,hz,hparity⟩ := lastFar_near_minus_three_parity hformal'
    exact ⟨q,R,c,m,w,hchain,hc,hlen,hformal,hshape,
      Or.inr ⟨p,b,z,hword,hz,hparity⟩⟩

#print axioms split_last_far
#print axioms formalInversePath_pureHigh_denominator
#print axioms terminal_last_anchor_tail_split

end BB6.Agent2F321AnchorEpochLastFar
