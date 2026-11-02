import CJumpCore
namespace BB6Agent38

def thinS (s : S) : Prop :=
  s.1=0 ∧ s.2.1%2=0 ∧ s.2.2=2*s.2.1+10

def thinB (s : S) : Bool := decide (s.1=0 ∧ s.2.1%2=0 ∧ s.2.2=2*s.2.1+10)

theorem thinS_positive (a k c : Nat) (ha : 0<a) : ¬thinS (a,k,c) := by
  simp only [thinS]
  omega

/-- During a proved sweep the first counter remains positive until the
    terminal point; inspecting shortcut endpoints suffices for safety. -/
theorem jump_no_thin (s : S) (hstart : ¬thinS s)
    (hend : ∀ t, (jump s).2 = some t → ¬thinS t)
    (i : Nat) (hi : i ≤ (jump s).1) (t : S)
    (ht : run i (some s) = some t) : ¬thinS t := by
  rcases s with ⟨a,k,c⟩
  by_cases h : 0<a ∧ 3<c
  · let q := min a (c-3)
    have hqa : q ≤ a := Nat.min_le_left _ _
    have hqc : q+3 ≤ c := by
      have hq:=Nat.min_le_right a (c-3)
      dsimp [q]
      omega
    have hiq : i ≤ q := by
      simpa [jump,h,q] using hi
    have hia : i ≤ a := by omega
    have hic : i+3 ≤ c := by omega
    have he := run_sweep i a k c hia hic
    rw [he] at ht
    have heq : t = (a-i,k+i,c-i) := (Option.some.inj ht.symm)
    by_cases hlt : i < q
    · have ha : 0 < a-i := by omega
      subst t
      exact thinS_positive (a-i) (k+i) (c-i) ha
    · have hiqeq : i=q := by omega
      subst t
      apply hend (a-i,k+i,c-i)
      simpa [jump,h,q,hiqeq]
  · have hi1 : i ≤ 1 := by
      simpa [jump,h] using hi
    cases i with
    | zero =>
        have ht' : (a,k,c)=t := by simpa [run] using ht
        subst t
        exact hstart
    | succ i =>
        have hzero : i=0 := by omega
        subst i
        apply hend t
        simpa [jump,h,run] using ht

#print axioms jump_no_thin
end BB6Agent38

namespace BB6Agent38

/-- Finite shortcut execution plus a Boolean absence-of-Thin certificate
    checked at every shortcut endpoint. -/
def checkedPath : Nat → S → Bool × (Nat × Option S)
  | 0,s => (!thinB s, (0,some s))
  | n+1,s =>
      let j := jump s
      match j.2 with
      | none => (false, (j.1,none))
      | some t =>
          let p := checkedPath n t
          (!thinB s && p.1, (p.2.1+j.1,p.2.2))

theorem thinB_false (s : S) (h : thinB s = false) : ¬thinS s := by
  rcases s with ⟨a,k,c⟩
  intro hh
  have he : a=0 ∧ k%2=0 ∧ c=2*k+10 := hh
  simp [thinB,he] at h

/-- Verified shortcut endpoint safety lifts to *every intermediate*
    uncompressed Machine C accelerator state, including swept-over states. -/
theorem checkedPath_safe (n : Nat) (s : S)
    (h : (checkedPath n s).1 = true) :
    ∀ i, i ≤ (checkedPath n s).2.1 → ∀ t,
      run i (some s) = some t → ¬thinS t := by
  induction n generalizing s with
  | zero =>
      intro i hi t ht
      have hi0 : i=0 := by simpa [checkedPath] using hi
      subst i
      have hstart : thinB s = false := by
        simpa [checkedPath] using h
      have hs : s=t := by simpa [run] using ht
      subst t
      exact thinB_false s hstart
  | succ n ih =>
      intro i hi t ht
      cases hj : jump s with
      | mk q opt =>
        cases opt with
        | none =>
            simp [checkedPath,hj] at h
        | some v =>
            have hstart : thinB s = false := by
              have hh : !thinB s && (checkedPath n v).1 = true := by
                simpa [checkedPath,hj] using h
              cases hs : thinB s <;> simp [hs] at hh ⊢
            have htail : (checkedPath n v).1 = true := by
              have hh : !thinB s && (checkedPath n v).1 = true := by
                simpa [checkedPath,hj] using h
              simp [hstart] at hh
              exact hh
            have hjump : run q (some s) = some v := by
              simpa [hj] using jump_sound s
            have hnext : ¬thinS v := by
              have hh := ih v htail 0 (by simp [checkedPath]) v
              exact hh (by rfl)
            have hbound : i ≤ (checkedPath n v).2.1+q := by
              simpa [checkedPath,hj] using hi
            by_cases hshort : i ≤ q
            · apply jump_no_thin s (thinB_false s hstart)
                (fun w hw => by
                  have heq : v=w := by simpa [hj] using hw
                  subst w
                  exact hnext) i (by simpa [hj] using hshort) t ht
            · have hafter : i = (i-q)+q := by omega
              have hlim : i-q ≤ (checkedPath n v).2.1 := by omega
              have ht2 : run (i-q) (some v) = some t := by
                rw [hafter,run_add,hjump] at ht
                exact ht
              exact ih v htail (i-q) hlim t ht2

#print axioms checkedPath_safe
end BB6Agent38
