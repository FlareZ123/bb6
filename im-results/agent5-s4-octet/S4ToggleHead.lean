import S4Toggle
import Lean.Elab.Tactic.Omega

namespace S4ToggleHead
open S4Power S4Octet S4Toggle

set_option maxHeartbeats 0

def h (c b : Nat) : Nat :=
  if (b+c)%2=0 then (b+c)/2+2 else (b+c)/2

def f (b : Nat) : Nat := h 219 (h 290 (h 509 b))

private theorem H_head (a : Nat) (L U : List Nat) (hh : H a L = some U) :
    ∃ S, U = (if a%2=0 then a/2+2 else a/2)::S := by
  cases L with
  | nil =>
      by_cases he : a%2=0
      · by_cases hz : a=0
        · simp [H,he,hz] at hh
        · have hu : U = [a/2+2,a/2-1] := by simpa [H,he,hz] using hh.symm
          exact ⟨[a/2-1], by simp [he,hu]⟩
      · by_cases hs : a≤1
        · simp [H,he,hs] at hh
        · have heq : (H (a/2) []).map (a/2::·) = some U := by
            rw [H] at hh
            simp only [he,hs,ite_false] at hh
            exact hh
          obtain ⟨V,hV,heqV⟩ := Option.map_eq_some_iff.mp heq
          subst U
          exact ⟨V, by simp [he]⟩
  | cons b T =>
      by_cases he : a%2=0
      · have hu : U = (a/2+2)::(b+a/2)::T := by simpa [H,he] using hh.symm
        exact ⟨(b+a/2)::T, by simp [he,hu]⟩
      · have heq : (H (b+a/2+1) T).map (a/2::·) = some U := by
          rw [H] at hh
          simp only [he,ite_false] at hh
          exact hh
        obtain ⟨V,hV,heqV⟩ := Option.map_eq_some_iff.mp heq
        subst U
        exact ⟨V, by simp [he]⟩

theorem G_head (c b : Nat) (S U : List Nat) (hh : G c (b::S)=some U) :
    ∃ T, U = h c b::T := by
  change H (b+c) S=some U at hh
  obtain ⟨T,hu⟩ := H_head (b+c) S U hh
  refine ⟨T,?_⟩
  simpa [h,Nat.add_comm] using hu

theorem P_head (b : Nat) (S U : List Nat) (hh : P (b::S)=some U) :
    ∃ T, U = f b::T := by
  cases h1 : G 509 (b::S) with
  | none => simp [P,h1] at hh
  | some V =>
      obtain ⟨Vtail, hV⟩ := G_head 509 b S V h1
      subst V
      cases h2 : G 290 (h 509 b::Vtail) with
      | none => simp [P,h1,h2] at hh
      | some X =>
          obtain ⟨Xtail,hX⟩ := G_head 290 (h 509 b) Vtail X h2
          subst X
          cases h3 : G 219 (h 290 (h 509 b)::Xtail) with
          | none => simp [P,h1,h2,h3] at hh
          | some Y =>
              obtain ⟨Ytail,hY⟩ := G_head 219 (h 290 (h 509 b)) Xtail Y h3
              have : U=Y := by simpa [P,h1,h2,h3] using hh.symm
              subst U
              exact ⟨Ytail, by simpa [f] using hY⟩

def cyc (n : Nat) : Nat :=
  if n%4=0 then 283 else if n%4=1 then 282 else
    if n%4=2 then 280 else 281

private theorem cyc_step (n : Nat) : cyc (n+1) = f (cyc n) := by
  have hmod : (n+1)%4 = (n%4+1)%4 := by omega
  have hn : n%4 < 4 := Nat.mod_lt n (by omega)
  unfold cyc
  rw [hmod]
  rcases (show n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 by omega) with h0 | h1 | h2 | h3
  · simp [h0, f, h]
  · simp [h1, f, h]
  · simp [h2, f, h]
  · simp [h3, f, h]

theorem prun_head_cycle (n : Nat) (U : List Nat)
    (hr : prun (n+1) [301,650,645,322,163,160] = some U) :
    ∃ T, U=cyc n::T := by
  induction n generalizing U with
  | zero =>
      change P (301::[650,645,322,163,160])=some U at hr
      obtain ⟨T,hU⟩ := P_head 301 [650,645,322,163,160] U hr
      refine ⟨T,?_⟩
      simpa [cyc,f,h] using hU
  | succ n ih =>
      change (prun (n+1) [301,650,645,322,163,160]).bind P = some U at hr
      cases hp : prun (n+1) [301,650,645,322,163,160] with
      | none => simp [hp] at hr
      | some V =>
          obtain ⟨T,hV⟩ := ih V hp
          subst V
          have hnext : P (cyc n::T)=some U := by simpa [hp] using hr
          obtain ⟨Utail,hU⟩ := P_head (cyc n) T U hnext
          refine ⟨Utail,?_⟩
          rw [cyc_step]
          exact hU

#print axioms H_head
#print axioms G_head
#print axioms P_head
#print axioms cyc_step
#print axioms prun_head_cycle
end S4ToggleHead
