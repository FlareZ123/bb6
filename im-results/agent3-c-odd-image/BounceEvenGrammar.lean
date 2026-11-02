import BounceReverse
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

/-- Exact inverse grammar for successful even-middle bounces, including
    the exceptional height-three terminal branch. -/
inductive EvenBack (x y : Nat) : Nat → Nat → Prop
  | small (k : Nat) (hk : k%2=0) (hx : x=2*k+2) (hy : y=3) :
      EvenBack x y k 4
  | large (k : Nat) (hk : k%2=0) (hy : 5≤y)
      (hbd : y+1≤2*k+8) (hx : x=2*k+7-y) :
      EvenBack x y k (y+1)
  | step (k c : Nat) (hk : k%2=0) (hc : 4≤c)
      (h : EvenBack x y (2*k+4) c) : EvenBack x y k (c+2*k+5)

theorem evenBack_sound (x y k c : Nat) (h : EvenBack x y k c) :
    (bounce k c).2=some (x,y) := by
  induction h with
  | small k hk hx hy =>
    subst x;subst y
    have he : ¬k%2=1 := by omega
    simp [bounce,he]
  | large k hk hy hbd hx =>
    have he : ¬k%2=1 := by omega
    have hlow : ¬y+1<4 := by omega
    have h4 : y+1≠4 := by omega
    have h5 : y+1≠5 := by omega
    rw [bounce]
    simp only [if_neg hlow,if_neg he,if_neg h4,if_neg h5,if_pos hbd,
      Option.some.injEq,Prod.mk.injEq]
    omega
  | step k c hk hc h ih =>
    exact bounce_even_reverse k c x y hk hc ih

theorem evenBack_complete (c k x y : Nat) (hk:k%2=0)
    (h : (bounce k c).2=some (x,y)) : EvenBack x y k c := by
  induction c using Nat.strongRecOn generalizing k x y with
  | ind c ih =>
    by_cases hlow : c<4
    · simp [bounce,hlow] at h
    · have he : ¬k%2=1 := by omega
      by_cases h4 : c=4
      · subst c
        have heq : (x,y)=(2*k+2,3) := by
          have hh:=h
          rw [bounce] at hh
          simp only [if_neg hlow,if_neg he,if_pos rfl] at hh
          exact Option.some.inj hh.symm
        cases Prod.mk.inj heq with
        | intro hx hyEq =>
          subst x;subst y
          exact EvenBack.small k hk rfl rfl
      · by_cases h5 : c=5
        · simp [bounce,hlow,he,h4,h5] at h
        · by_cases hsmall : c≤2*k+8
          · have heq : (x,y)=(2*k+8-c,c-1) := by
              have hh:=h
              rw [bounce] at hh
              simp only [if_neg hlow,if_neg he,if_neg h4,if_neg h5,if_pos hsmall] at hh
              exact Option.some.inj hh.symm
            cases Prod.mk.inj heq with
            | intro hx hyEq =>
              subst x;subst y
              have hy : 5≤c-1 := by omega
              have hcc : c-1+1≤2*k+8 := by omega
              have hX : 2*k+8-c=2*k+7-(c-1) := by omega
              have hc0 : c-1+1=c := by omega
              simpa [hc0] using EvenBack.large k hk hy hcc hX
          · have hlt : c-(2*k+5)<c := by omega
            have hh : (bounce (2*k+4) (c-(2*k+5))).2=some (x,y) := by
              have hc:=h
              rw [bounce] at hc
              simpa only [if_neg hlow,if_neg he,if_neg h4,if_neg h5,if_neg hsmall] using hc
            have hn : EvenBack x y (2*k+4) (c-(2*k+5)) :=
              ih _ hlt (2*k+4) x y (by omega) hh
            have heq : c-(2*k+5)+2*k+5=c := by omega
            simpa [heq] using EvenBack.step k (c-(2*k+5)) hk (by omega) hn

theorem evenBack_iff_bounce (k c x y : Nat) (hk:k%2=0) :
    EvenBack x y k c ↔ (bounce k c).2=some (x,y) := by
  constructor
  · exact evenBack_sound x y k c
  · exact evenBack_complete c k x y hk

#print axioms evenBack_iff_bounce
end BB6.Agent3
