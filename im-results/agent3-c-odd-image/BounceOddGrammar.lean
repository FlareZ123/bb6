import BounceReverse
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

/-- Exact backwards grammar for the odd-middle bounce outputs. -/
inductive OddBack (x y : Nat) : Nat → Nat → Prop
  | terminal (k : Nat) (hk : k%2=1) (hy : 4≤y) (hbd : y≤2*k+6)
      (hx : x=2*k+6-y) : OddBack x y k y
  | step (k c : Nat) (hk : k%2=1) (hc : 4≤c)
      (h : OddBack x y (2*k+3) c) : OddBack x y k (c+2*k+3)

theorem oddBack_sound (x y k c : Nat) (h : OddBack x y k c) :
    (bounce k c).2=some (x,y) := by
  induction h with
  | terminal k hk hy hbd hx =>
    subst x
    have hlow : ¬y<4 := by omega
    rw [bounce]
    simp only [if_neg hlow,if_pos hk,if_pos hbd]
  | step k c hk hc h ih =>
    exact bounce_odd_reverse k c x y hk hc ih

theorem oddBack_complete (c k x y : Nat) (hk:k%2=1)
    (h : (bounce k c).2=some (x,y)) : OddBack x y k c := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at h
    · by_cases hsmall : c≤2*k+6
      · have heq : (x,y)=(2*k+6-c,c) := by
          have hh:=h
          rw [bounce] at hh
          simp only [if_neg hlow,if_pos hk,if_pos hsmall] at hh
          exact Option.some.inj hh.symm
        cases Prod.mk.inj heq with
        | intro hx hyEq =>
          subst x;subst y
          exact OddBack.terminal k hk (by omega) hsmall rfl
      · have hlt : c-(2*k+3)<c := by omega
        have hh : (bounce (2*k+3) (c-(2*k+3))).2=some (x,y) := by
          have hc:=h
          rw [bounce] at hc
          simpa only [if_neg hlow,if_pos hk,if_neg hsmall] using hc
        have hn : OddBack x y (2*k+3) (c-(2*k+3)) :=
          ih _ hlt (2*k+3) x y (by omega) hh
        have heq : c-(2*k+3)+2*k+3=c := by omega
        simpa [heq] using OddBack.step k (c-(2*k+3)) hk (by omega) hn

theorem oddBack_iff_bounce (k c x y : Nat) (hk:k%2=1) :
    OddBack x y k c ↔ (bounce k c).2=some (x,y) := by
  constructor
  · exact oddBack_sound x y k c
  · exact oddBack_complete c k x y hk

#print axioms oddBack_iff_bounce
end BB6.Agent3
