import Lean
import Lean.Elab.Tactic.Omega

namespace S4Length

def W : List Nat → Nat
  | [] => 0
  | b :: T => b + 1 + 2 * W T

inductive Done : Nat → List Nat → List Nat → Prop where
  | evenNil (q : Nat) (hq : 0 < q) : Done (2*q) [] [q+2,q-1]
  | evenCons (q b : Nat) (T : List Nat) (hq : 0 < q) :
      Done (2*q) (b::T) ((q+2)::(b+q)::T)
  | oddNil (q : Nat) (T : List Nat) :
      Done q [] T → Done (2*q+1) [] (q::T)
  | oddCons (q b : Nat) (S U : List Nat) :
      Done (b+q+1) S U → Done (2*q+1) (b::S) (q::U)

def H (a : Nat) (L : List Nat) : Option (List Nat) :=
  if a % 2 = 0 then
    if a = 0 then none
    else
      match L with
      | [] => some [a/2+2,a/2-1]
      | b::S => some ((a/2+2)::(b+a/2)::S)
  else
    match L with
    | [] =>
        if a = 1 then none
        else (H (a/2) []).map (a/2::·)
    | b::S => (H (b+a/2+1) S).map (a/2::·)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | apply Prod.Lex.left; simp
    | apply Prod.Lex.right; omega

set_option maxHeartbeats 0

theorem H_to_done : ∀ (L : List Nat) (a : Nat) (U : List Nat),
    H a L = some U → Done a L U := by
  intro L
  induction L with
  | nil =>
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
        intro U hs
        by_cases he : a % 2 = 0
        · by_cases hz : a = 0
          · simp [H,hz] at hs
          · have hq : 0 < a/2 := by omega
            have ha : a = 2*(a/2) := by omega
            have hu : U = [a/2+2,a/2-1] := by
              simpa [H,he,hz] using hs.symm
            subst U
            simpa only [←ha]
              using Done.evenNil (a/2) hq
        · by_cases ho : a = 1
          · simp [H,ho] at hs
          · have ha : a = 2*(a/2)+1 := by omega
            have hlt : a/2 < a := by omega
            cases hsub : H (a/2) [] with
            | none => simp [H,he,ho,hsub] at hs
            | some V =>
                have hu : U = (a/2)::V := by
                  simpa [H,he,ho,hsub] using hs.symm
                subst U
                simpa only [←ha]
                  using Done.oddNil (a/2) V (ih (a/2) hlt V hsub)
  | cons b S ih =>
      intro a U hs
      by_cases he : a%2=0
      · by_cases hz : a=0
        · simp [H,hz] at hs
        · have hq : 0 < a/2 := by omega
          have ha : a=2*(a/2) := by omega
          have hu : U = (a/2+2)::(b+a/2)::S := by
            simpa [H,he,hz] using hs.symm
          subst U
          simpa only [←ha]
            using Done.evenCons (a/2) b S hq
      · have ha : a=2*(a/2)+1 := by omega
        cases hsub : H (b+a/2+1) S with
        | none => simp [H,he,hsub] at hs
        | some V =>
            have hu : U = (a/2)::V := by
              simpa [H,he,hsub] using hs.symm
            subst U
            simpa only [←ha]
              using Done.oddCons (a/2) b S V (ih (b+a/2+1) V hsub)

private theorem even_factor_zero (q x k t : Nat)
    (h : 2*q + 1 + 2*x = 2^k * (2*t+1)) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Nat.pow_succ] at h
    have hmul : (2^k * 2)*(2*t+1) = 2*(2^k*(2*t+1)) := by ac_rfl
    rw [hmul] at h
    omega

set_option maxRecDepth 2000
set_option maxHeartbeats 0

theorem done_length (a : Nat) (L U : List Nat) (h : Done a L U) :
    ∀ (k t : Nat), a + 1 + 2 * W L = 2^k * (2*t+1) →
      U.length = max (L.length+1) (k+2) := by
  induction h with
  | evenNil q hq =>
      intro k t hp
      have hk : k=0 := even_factor_zero q 0 k t (by simpa [W] using hp)
      subst k
      simp
  | evenCons q b T hq =>
      intro k t hp
      have hk : k=0 := even_factor_zero q (W (b::T)) k t hp
      subst k
      simp [List.length, Nat.max_eq_left (by omega : 2 ≤ T.length+2)]
  | oddNil q U h ih =>
      intro k t hp
      cases k with
      | zero =>
          simp [W] at hp
          omega
      | succ k =>
          have hsmall : q + 1 + 2*W ([] : List Nat) = 2^k*(2*t+1) := by
            simp [W] at hp ⊢
            rw [Nat.pow_succ] at hp
            have hmul : (2^k * 2)*(2*t+1) = 2*(2^k*(2*t+1)) := by ac_rfl
            rw [hmul] at hp
            omega
          have hr := ih k t hsmall
          simp only [List.length_cons, List.length_nil] at hr ⊢
          omega
  | oddCons q b S U h ih =>
      intro k t hp
      cases k with
      | zero =>
          simp [W] at hp
          omega
      | succ k =>
          have hsmall : (b+q+1) + 1 + 2*W S = 2^k*(2*t+1) := by
            simp [W] at hp
            rw [Nat.pow_succ] at hp
            have hmul : (2^k * 2)*(2*t+1) = 2*(2^k*(2*t+1)) := by ac_rfl
            rw [hmul] at hp
            omega
          have hr := ih k t hsmall
          simp only [List.length_cons] at hr ⊢
          omega

def bump17 : List Nat → List Nat
  | [] => [16]
  | b::S => (b+17)::S

def F : List Nat → Option (List Nat)
  | [] => (H 44 []).map bump17
  | b::S => (H (b+45) S).map bump17

private theorem done_nonempty {a : Nat} {L U : List Nat} (h : Done a L U) : U ≠ [] := by
  cases h <;> simp

private theorem bump17_length (U : List Nat) (h : U ≠ []) :
    (bump17 U).length = U.length := by
  cases U with
  | nil => contradiction
  | cons b S => rfl

theorem F_length (T U : List Nat) (hs : F T = some U)
    (k t : Nat) (hf : W T + 45 = 2^k * (2*t+1)) :
    U.length = max T.length (k+2) := by
  cases T with
  | nil =>
      have hnil : H 44 [] = some [24,21] := by simp [H]
      have hu : U = bump17 [24,21] := by
        simpa [F,hnil] using hs.symm
      have hk : k=0 := even_factor_zero 22 0 k t (by simpa [W] using hf)
      subst k
      subst U
      decide
  | cons b S =>
      cases hsub : H (b+45) S with
      | none => simp [F,hsub] at hs
      | some V =>
          have hu : U = bump17 V := by
            simpa [F,hsub] using hs.symm
          have hd : Done (b+45) S V := H_to_done S (b+45) V hsub
          have hp : (b+45)+1+2*W S = 2^k*(2*t+1) := by
            simp only [W] at hf
            omega
          have hlen := done_length (b+45) S V hd k t hp
          rw [hu,bump17_length V (done_nonempty hd),hlen]
          rfl

#print axioms F_length
#print axioms done_length
end S4Length
