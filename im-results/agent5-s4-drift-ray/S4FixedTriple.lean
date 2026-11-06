import S4ToggleHead
import Lean.Elab.Tactic.Omega
namespace S4FixedTriple
open S4Power S4Octet S4Toggle S4ToggleHead
set_option maxHeartbeats 0
set_option maxRecDepth 12000

/-- Exact total prefix projection for one S4 odd-drain. -/
def C (c : Nat) : List Nat → List Nat
  | [] => []
  | a::R =>
      let x := a+c
      if x%2=0 then
        match R with
        | [] => [x/2+2]
        | b::T => (x/2+2)::(b+x/2)::T
      else (x/2)::C (x/2+1) R

theorem C_length (c : Nat) (xs : List Nat) : (C c xs).length = xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons a R ih =>
      by_cases he : (a+c)%2=0
      · cases R with
        | nil => simp [C,he]
        | cons b S => simp [C,he]
      · simp [C,he,ih]

def D (xs : List Nat) : List Nat := C 219 (C 290 (C 509 xs))

theorem D_length (xs : List Nat) : (D xs).length=xs.length := by
  simp [D,C_length]

theorem C_causal (c : Nat) (xs ys : List Nat) :
    ∃ zs, C c (xs++ys)=C c xs++zs := by
  induction xs generalizing c ys with
  | nil => exact ⟨C c ys, by simp [C]⟩
  | cons a xs ih =>
      by_cases he : (a+c)%2=0
      · cases xs with
        | nil =>
            cases ys with
            | nil => exact ⟨[], by simp [C, he]⟩
            | cons b T => exact ⟨(b+(a+c)/2)::T, by simp [C,he]⟩
        | cons b T =>
            exact ⟨ys, by simp [C,he]⟩
      · obtain ⟨zs, hz⟩ := ih ((a+c)/2+1) ys
        refine ⟨zs, ?_⟩
        simp only [List.cons_append]
        simp [C,he,hz]

theorem C_take (c : Nat) (xs ys : List Nat) :
    (C c (xs++ys)).take xs.length=C c xs := by
  obtain ⟨zs,hz⟩ := C_causal c xs ys
  rw [hz]
  rw [List.take_append_of_le_length (by simp [C_length])]
  rw [← C_length c xs]
  exact List.take_length

theorem D_causal (xs ys : List Nat) :
    ∃ zs, D (xs++ys) = D xs ++ zs := by
  obtain ⟨T1,h1⟩ := C_causal 509 xs ys
  obtain ⟨T2,h2⟩ := C_causal 290 (C 509 xs) T1
  obtain ⟨T3,h3⟩ := C_causal 219 (C 290 (C 509 xs)) T2
  refine ⟨T3, ?_⟩
  simpa [D,h1,h2] using h3

theorem D_take (xs ys : List Nat) :
    (D (xs++ys)).take xs.length = D xs := by
  obtain ⟨zs,hz⟩ := D_causal xs ys
  rw [hz]
  rw [List.take_append_of_le_length (by simp [D_length])]
  rw [← D_length xs]
  exact List.take_length

private theorem G_cons_even (c a : Nat) (R : List Nat)
    (he : (a+c)%2=0) (hpos : a+c≠0) :
    G c (a::R) = some (match R with
      | [] => [(a+c)/2+2,(a+c)/2-1]
      | b::S => ((a+c)/2+2)::(b+(a+c)/2)::S) := by
  cases R with
  | nil =>
      change H (a+c) [] = some [(a+c)/2+2,(a+c)/2-1]
      rw [H]
      simp [he,hpos]
      omega
  | cons b S => simp [G,H,he]

private theorem G_cons_odd (c a : Nat) (R : List Nat)
    (ho : (a+c)%2≠0) :
    G c (a::R) = (G ((a+c)/2+1) R).map (((a+c)/2)::·) := by
  cases R with
  | nil =>
      by_cases hsmall : a+c≤1
      · have ha : a+c=1 := by omega
        simp [G,H,ha]
      · change H (a+c) [] = (H (((a+c)/2+1)-1) []).map (((a+c)/2)::·)
        rw [H]
        simp only [ho, ite_false, hsmall]
        have hq : (a+c)/2+1-1=(a+c)/2 := by omega
        rw [hq]
  | cons b S =>
      simp only [G,H,ho,ite_false]
      congr 1

/-- Unbounded finite-prefix causality for a single odd-drain.
    This is conditional on success, not a totality theorem. -/
theorem G_causal (c : Nat) (xs ys out : List Nat)
    (hc : 0<c) (hg : G c (xs++ys)=some out) :
    ∃ suffix, out = C c xs ++ suffix := by
  induction xs generalizing c ys out with
  | nil => exact ⟨out, by simp [C]⟩
  | cons a xs ih =>
      by_cases he : (a+c)%2=0
      · have hpos : a+c≠0 := by omega
        have hstep := G_cons_even c a (xs++ys) he hpos
        change G c (a::(xs++ys))=some out at hg
        rw [hstep] at hg
        cases xs with
        | nil =>
            cases ys with
            | nil =>
                refine ⟨[(a+c)/2-1], ?_⟩
                have hu := Option.some.inj hg.symm
                simpa [C,he] using hu
            | cons b T =>
                refine ⟨(b+(a+c)/2)::T, ?_⟩
                have hu := Option.some.inj hg.symm
                simpa [C,he] using hu
        | cons b R =>
            refine ⟨ys, ?_⟩
            have hu := Option.some.inj hg.symm
            simpa [C,he] using hu
      · have hstep := G_cons_odd c a (xs++ys) he
        change G c (a::(xs++ys))=some out at hg
        rw [hstep] at hg
        obtain ⟨U,hU,hu⟩ := Option.map_eq_some_iff.mp hg
        obtain ⟨V,hV⟩ := ih ((a+c)/2+1) ys U (by omega) hU
        subst out
        refine ⟨V, ?_⟩
        simp [C,he,hV]

theorem P_causal (xs ys out : List Nat)
    (hp : P (xs++ys)=some out) :
    ∃ suffix, out = D xs ++ suffix := by
  cases h1 : G 509 (xs++ys) with
  | none => simp [P,h1] at hp
  | some U =>
      obtain ⟨T1,hU⟩ := G_causal 509 xs ys U (by omega) h1
      rw [hU] at h1
      cases h2 : G 290 (C 509 xs++T1) with
      | none => simp [P,h1,h2] at hp
      | some V =>
          obtain ⟨T2,hV⟩ := G_causal 290 (C 509 xs) T1 V (by omega) h2
          rw [hV] at h2
          have h3 : G 219 (C 290 (C 509 xs)++T2)=some out := by
            simpa [P,h1,h2] using hp
          obtain ⟨T3,hout⟩ := G_causal 219 (C 290 (C 509 xs)) T2 out (by omega) h3
          exact ⟨T3, by simpa [D] using hout⟩

theorem C_one (c a : Nat) : C c [a]=[h c a] := by
  by_cases he : (a+c)%2=0
  · simp [C,h,he]
  · simp [C,h,he]

theorem D_one (a : Nat) : D [a]=[f a] := by
  simp only [D,C_one]
  rfl

theorem fixed_head (a : Nat) (hfa : f a = a) : a = 284 := by
  dsimp [f,h] at hfa
  split at hfa <;> split at hfa <;> split at hfa <;> omega

theorem fixed_second (b : Nat) (hb : D [284,b]=[284,b]) : b=1646 ∨ b=1651 := by
  by_cases hpar : (b+397)%2=0
  · simp [D,C,hpar] at hb
    omega
  · simp [D,C,hpar] at hb
    omega

theorem fixed_third_good (c : Nat)
    (hc : D [284,1646,c]=[284,1646,c]) : c=1021 ∨ c=1026 := by
  simp [D,C] at hc
  split at hc <;> simp at hc <;> omega

theorem fixed_third_bad (c : Nat)
    (hc : D [284,1651,c]=[284,1651,c]) : False := by
  simp [D,C] at hc
  all_goals (split at hc <;> simp [C] at hc <;> omega)

theorem classify (a b c : Nat) :
    D [a,b,c] = [a,b,c] ↔
       a=284 ∧ b=1646 ∧ (c=1021 ∨ c=1026) := by
  constructor
  · intro hfix
    have h1 : D [a] = [a] := by
      have ht := D_take [a] [b,c]
      simp only [List.cons_append, List.nil_append] at ht
      rw [hfix] at ht
      simpa using ht.symm
    have hfa : f a = a := by
      simpa [D_one] using h1
    have ha : a=284 := fixed_head a hfa
    subst a
    have h2 : D [284,b]=[284,b] := by
      have ht := D_take [284,b] [c]
      simp only [List.cons_append, List.nil_append] at ht
      rw [hfix] at ht
      simpa using ht.symm
    obtain (hb | hb) := fixed_second b h2
    · subst b
      exact ⟨rfl,rfl,fixed_third_good c hfix⟩
    · subst b
      exact False.elim (fixed_third_bad c hfix)
  · rintro ⟨rfl,rfl,(rfl | rfl)⟩
    · decide
    · decide

/-- A successful full S4 P return preserving a first triple must start in one of
    the two classified total-prefix fixed points. -/
theorem actual_stationary_three (a b c : Nat) (S U : List Nat)
    (hp : P ([a,b,c] ++ S)=some U)
    (hs : ∃ T, U = [a,b,c] ++ T) :
    a=284 ∧ b=1646 ∧ (c=1021 ∨ c=1026) := by
  obtain ⟨T,hU⟩ := hs
  obtain ⟨V,hV⟩ := P_causal [a,b,c] S U hp
  rw [hU] at hV
  have htake := congrArg (List.take 3) hV
  have hfix : D [a,b,c]=[a,b,c] := by
    simpa [List.take_append, D_length] using htake.symm
  exact (classify a b c).mp hfix

#print axioms P_causal
#print axioms actual_stationary_three
#print axioms C_causal
#print axioms D_causal
#print axioms fixed_head
#print axioms fixed_second
#print axioms fixed_third_good
#print axioms fixed_third_bad
#print axioms classify
end S4FixedTriple
