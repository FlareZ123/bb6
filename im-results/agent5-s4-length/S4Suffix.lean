import S4Length
import Lean
import Lean.Elab.Tactic.Omega

namespace S4Length

def Tail2 (t : Nat) (U : List Nat) : Prop :=
  ∃ V : List Nat, U = V ++ [t+2,t-1]

set_option maxHeartbeats 0

private theorem even_factor_zero (q x k t : Nat)
    (h : 2*q + 1 + 2*x = 2^k * (2*t+1)) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Nat.pow_succ] at h
    have hm : (2^k*2)*(2*t+1)=2*(2^k*(2*t+1)) := by ac_rfl
    rw [hm] at h
    omega

theorem done_terminal_tail (a : Nat) (L U : List Nat) (h : Done a L U) :
    ∀ k t : Nat, a+1+2*W L = 2^k*(2*t+1) →
      L.length ≤ k → Tail2 t U := by
  induction h with
  | evenNil q hq =>
      intro k t hp hk
      have hk0 : k=0 := even_factor_zero q 0 k t (by simpa [W] using hp)
      subst k
      have hqt : q=t := by simp [W] at hp; omega
      subst t
      exact ⟨[],rfl⟩
  | evenCons q b S =>
      intro k t hp hk
      have hk0 : k=0 := even_factor_zero q (W (b::S)) k t hp
      simp at hk
      omega
  | oddNil q T h ih =>
      intro k t hp hk
      cases k with
      | zero =>
          simp [W] at hp
          omega
      | succ k =>
          have he : q+1+2*W ([] : List Nat) = 2^k*(2*t+1) := by
            simp [W] at hp ⊢
            rw [Nat.pow_succ] at hp
            have hm : (2^k*2)*(2*t+1)=2*(2^k*(2*t+1)) := by ac_rfl
            rw [hm] at hp
            omega
          obtain ⟨V,hV⟩ := ih k t he (by simp)
          exact ⟨q::V, by simp [hV]⟩
  | oddCons q b S T h ih =>
      intro k t hp hk
      cases k with
      | zero =>
          simp [W] at hp
          omega
      | succ k =>
          have he : (b+q+1)+1+2*W S = 2^k*(2*t+1) := by
            simp [W] at hp
            rw [Nat.pow_succ] at hp
            have hm : (2^k*2)*(2*t+1)=2*(2^k*(2*t+1)) := by ac_rfl
            rw [hm] at hp
            omega
          have hk' : S.length ≤ k := by simp at hk; omega
          obtain ⟨V,hV⟩ := ih k t he hk'
          exact ⟨q::V, by simp [hV]⟩

theorem bump17_tail (t : Nat) (V : List Nat) (ht : Tail2 t V)
    (hlen : 3 ≤ V.length) : Tail2 t (bump17 V) := by
  obtain ⟨P, hP⟩ := ht
  cases P with
  | nil =>
      simp [hP] at hlen
  | cons b S =>
      refine ⟨(b+17)::S, ?_⟩
      simp [hP,bump17]

theorem F_terminal_tail (T U : List Nat) (h : F T = some U)
    (k t : Nat) (hp : W T + 45 = 2^k * (2*t+1))
    (hk : 1 ≤ k) (hlen : T.length ≤ k+1) : Tail2 t U := by
  cases T with
  | nil =>
      have hk0 : k = 0 := even_factor_zero 22 0 k t (by simpa [W] using hp)
      omega
  | cons b S =>
      cases hsub : H (b+45) S with
      | none => simp [F,hsub] at h
      | some V =>
          have hu : U = bump17 V := by simpa [F,hsub] using h.symm
          have hd : Done (b+45) S V := H_to_done S (b+45) V hsub
          have hP : b+45+1+2*W S = 2^k*(2*t+1) := by
            simp [W] at hp
            omega
          have hkS : S.length ≤ k := by simp at hlen; omega
          have ht : Tail2 t V := done_terminal_tail (b+45) S V hd k t hP hkS
          have hl : V.length = max (S.length+1) (k+2) :=
            done_length (b+45) S V hd k t hP
          have hthree : 3 ≤ V.length := by omega
          simpa [hu] using bump17_tail t V ht hthree

#print axioms done_terminal_tail
#print axioms F_terminal_tail
end S4Length
