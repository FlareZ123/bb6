import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429NoTwentyFive
set_option maxHeartbeats 4000000

/-- The affine family (20k+10,88k+62) has just one possible parent. -/
theorem parent_even_target (k x y : Nat)
    (hs : BB429.next (x,y)=some (20*k+10,88*k+62)) :
    x=42*k+22 ∧ y=44*k+31 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Parent of the odd-second-counter family (40k+23,48k+39). -/
theorem parent_odd_target (k x y : Nat)
    (hs : BB429.next (x,y)=some (40*k+23,48*k+39)) :
    x=20*k+10 ∧ y=88*k+62 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Every predecessor of (16k+11,96k+74), for k>0,
    belongs to one of these two exact affine families. -/
theorem parent_seed (k x y : Nat) (hk : 0<k)
    (hs : BB429.next (x,y)=some (16*k+11,96*k+74)) :
    (x=8*k+4 ∧ y=112*k+85) ∨
    (x=40*k+23 ∧ y=48*k+39) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- The parent of the even family violates an all-time parity condition. -/
theorem no_reach_even_target (n k : Nat) :
    BB429.run n (0,0) ≠ some (20*k+10,88*k+62) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_even_target k p.1 p.2 hs
      have hpos : 0<p.1 := by omega
      have hev : p.1%2=0 := by omega
      have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos hev
      omega

theorem no_reach_odd_target (n k : Nat) :
    BB429.run n (0,0) ≠ some (40*k+23,48*k+39) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_odd_target k p.1 p.2 hs
      have hbad : BB429.run n (0,0) = some (20*k+10,88*k+62) := by
        have hpEq : p=(20*k+10,88*k+62) := Prod.ext hx hy
        simpa [hpEq] using hp
      exact (no_reach_even_target n k) hbad

theorem no_reach_positive_seed (n k : Nat) (hk : 0<k) :
    BB429.run n (0,0) ≠ some (16*k+11,96*k+74) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain hcase := parent_seed k p.1 p.2 hk hs
      rcases hcase with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have hpos : 0<p.1 := by omega
        have hev : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos hev
        omega
      · have hbad : BB429.run n (0,0) = some (40*k+23,48*k+39) := by
          have hpEq : p=(40*k+23,48*k+39) := Prod.ext hx hy
          simpa [hpEq] using hp
        exact (no_reach_odd_target n k) hbad

/-- The unique finite exceptional feeder is disallowed by an exact
    15-step prefix plus monotone rank. -/
theorem no_reach_eleven_seventyfour (n : Nat) :
    BB429.run n (0,0) ≠ some (11,74) := by
  intro hs
  by_cases hn : n<15
  · have hf : ∀ i : Fin 15, BB429.run i.val (0,0) ≠ some (11,74) := by decide
    exact (hf ⟨n,hn⟩) hs
  · have h15 : BB429.run 15 (0,0) = some (23,51) := by decide
    have hc : BB429.run n (0,0) = BB429.run (n-15) (23,51) := by
      calc
        BB429.run n (0,0) = BB429.run (15+(n-15)) (0,0) := by
          congr 1
          omega
        _ = BB429.run (n-15) (23,51) := by
          rw [BB429.run_add,h15]
          rfl
    rw [hc] at hs
    have hr := (BB429.run_rank_bounds (23,51) (11,74) (n-15) hs).1
    simp only [BB429.rank] at hr
    omega

/-- Entire infinite affine feeder cylinder excluded from the blank root. -/
theorem no_reach_all_seed (n k : Nat) :
    BB429.run n (0,0) ≠ some (16*k+11,96*k+74) := by
  by_cases hk : k=0
  · subst k
    simpa using no_reach_eleven_seventyfour n
  · exact no_reach_positive_seed n k (by omega)

/-- A halt at first counter 25 mod32 must be preceded by the excluded feeder. -/
theorem parent_twentyfive_halt (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (hg : b+1=2*a) (hm : a%32=25) :
    x%16=11 ∧ y=6*x+8 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- An entire previously unresolved congruence class of halts is excluded. -/
theorem blank_halt_not_twentyfive (n a b : Nat)
    (hreach : BB429.run n (0,0)=some (a,b))
    (hhalt : BB429.next (a,b)=none) : a%32 ≠ 25 := by
  intro hm
  have hl := (BB429.next_none_iff_halt_line a b).mp hhalt
  cases n with
  | zero => simp [BB429.run] at hreach; omega
  | succ n =>
    simp only [BB429.run] at hreach
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hreach
    | some p =>
      simp only [hp,Option.bind_some] at hreach
      obtain ⟨hmod,hy⟩ := parent_twentyfive_halt p.1 p.2 a b hreach hl hm
      let k := p.1/16
      have hx : p.1=16*k+11 := by dsimp [k]; omega
      have hpy : p.2=96*k+74 := by omega
      have heq : p=(16*k+11,96*k+74) := Prod.ext hx hpy
      have hbad : BB429.run n (0,0)=some (16*k+11,96*k+74) := by
        simpa [heq] using hp
      exact (no_reach_all_seed n k) hbad

#print axioms parent_even_target
#print axioms parent_odd_target
#print axioms parent_seed
#print axioms no_reach_all_seed
#print axioms parent_twentyfive_halt
#print axioms blank_halt_not_twentyfive
end BB429NoTwentyFive
