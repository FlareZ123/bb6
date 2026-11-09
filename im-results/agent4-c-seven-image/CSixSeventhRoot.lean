import CSixSeventhStrict
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Seven
open BB6.Agent46

/-- Any genuinely performed first-return sequence supplies that many incoming edges. -/
private theorem root_run_incoming (n : Nat) (s p : Nat × Nat)
    (h : BB6.Agent8Section.run secNext n (some s) = some p) :
    Incoming n p := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
      change (BB6.Agent8Section.run secNext n (some s)).bind secNext = some p at h
      cases hp : BB6.Agent8Section.run secNext n (some s) with
      | none => simp [hp] at h
      | some q =>
          have he : secNext q = some p := by simpa [hp] using h
          exact ⟨q,ih q hp,he⟩

private theorem incoming_drop_root (n : Nat) (p : Nat × Nat) :
    Incoming (n+1) p → Incoming n p := by
  induction n generalizing p with
  | zero => simp [Incoming]
  | succ n ih =>
      rintro ⟨q,hq,hedge⟩
      exact ⟨q,ih q hq,hedge⟩

private theorem incoming_shrink (n m : Nat) (p : Nat × Nat) :
    Incoming (n+m) p → Incoming n p := by
  induction m with
  | zero => simpa using id
  | succ m ih =>
      intro h
      have h' : Incoming (n+m) p := incoming_drop_root (n+m) p (by
        simpa only [Nat.add_succ] using h)
      exact ih h'

/-- Actual blank-origin Machine C sections avoid this strict image band at every time. -/
theorem blank_ne_six_seven_band (u v time : Nat) (hpair : (u+v)%4=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
    some (641+1024*u,574+1024*v) := by
  intro ht
  by_cases hshort : time<7
  · have hex : time=0 ∨ time=1 ∨ time=2 ∨ time=3 ∨
        time=4 ∨ time=5 ∨ time=6 := by omega
    rcases hex with h0|h1|h2|h3|h4|h5|h6
    · subst time
      have he : BB6.Agent8Section.run secNext 0 (some (5,1)) = some (5,1) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 1 (some (5,1)) = some (3,4) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 2 (some (5,1)) = some (4,7) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 3 (some (5,1)) = some (20,4) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 4 (some (5,1)) = some (12,10) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 5 (some (5,1)) = some (17,11) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 6 (some (5,1)) = some (32,7) :=
        by simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at ht
      have hk := congrArg Prod.snd (Option.some.inj ht)
      omega
  · have hlong : 7+(time-7)=time := by omega
    have hh : Incoming time (641+1024*u,574+1024*v) :=
      root_run_incoming time (5,1) _ ht
    rw [←hlong] at hh
    exact no_seven_incoming u v hpair (incoming_shrink 7 (time-7) _ hh)

#print axioms blank_ne_six_seven_band
end BB6.Agent4Seven
