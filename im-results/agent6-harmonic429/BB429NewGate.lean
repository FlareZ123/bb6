import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429NewGate
set_option maxHeartbeats 8000000

theorem parent_seed17 (k x y : Nat)
    (hs : BB429.next (x,y)=some (16*k+7,96*k+50)) :
    (x=8*k+2 ∧ y=112*k+57) ∨ (x=40*k+13 ∧ y=48*k+27) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_odd17 (k x y : Nat)
    (hs : BB429.next (x,y)=some (40*k+13,48*k+27)) :
    x=20*k+5 ∧ y=88*k+40 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_divfour17 (k x y : Nat)
    (hs : BB429.next (x,y)=some (20*k+5,88*k+40)) :
    x=10*k+1 ∧ y=108*k+45 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_odd17_deep (k x y : Nat) (hk : k%2=1)
    (hs : BB429.next (x,y)=some (10*k+1,108*k+45)) :
    x=5*k-1 ∧ y=118*k+46 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem no_reach_deep17 (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (10*k+1,108*k+45) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_odd17_deep k p.1 p.2 hk hs
      have hpos : 0<p.1 := by omega
      have he : p.1%2=0 := by omega
      have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
      omega

theorem no_reach_divfour17 (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (20*k+5,88*k+40) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_divfour17 k p.1 p.2 hs
      have heq : p=(10*k+1,108*k+45) := Prod.ext hx hy
      have hbad : BB429.run n (0,0)=some (10*k+1,108*k+45) := by simpa [heq] using hp
      exact (no_reach_deep17 n k hk) hbad

theorem no_reach_odd17 (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (40*k+13,48*k+27) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_odd17 k p.1 p.2 hs
      have heq : p=(20*k+5,88*k+40) := Prod.ext hx hy
      have hbad : BB429.run n (0,0)=some (20*k+5,88*k+40) := by simpa [heq] using hp
      exact (no_reach_divfour17 n k hk) hbad

theorem no_reach_seed17_odd (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (16*k+7,96*k+50) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      rcases parent_seed17 k p.1 p.2 hs with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega
      · have heq : p=(40*k+13,48*k+27) := Prod.ext hx hy
        have hbad : BB429.run n (0,0)=some (40*k+13,48*k+27) := by simpa [heq] using hp
        exact (no_reach_odd17 n k hk) hbad

/-- Incoming family to a 9(mod64) halt feeder. -/
theorem parent_seed9 (k x y : Nat) (hk : k%2=1)
    (hs : BB429.next (x,y)=some (16*k+3,96*k+26)) :
    (x=8*k ∧ y=112*k+29) ∨ (x=40*k+3 ∧ y=48*k+15) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_odd9 (k x y : Nat) (hk : k%2=1)
    (hs : BB429.next (x,y)=some (40*k+3,48*k+15)) :
    x=20*k ∧ y=88*k+18 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_even9 (k x y : Nat) (hk : k%2=1)
    (hs : BB429.next (x,y)=some (20*k,88*k+18)) :
    x=42*k+1 ∧ y=44*k+9 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_odd9_deep (k x y : Nat) (hk : k%2=1)
    (hs : BB429.next (x,y)=some (42*k+1,44*k+9)) :
    x=21*k-1 ∧ y=86*k+10 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem no_reach_deep9 (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (42*k+1,44*k+9) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_odd9_deep k p.1 p.2 hk hs
      have hpos : 0<p.1 := by omega
      have he : p.1%2=0 := by omega
      have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
      omega

theorem no_reach_even9 (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (20*k,88*k+18) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_even9 k p.1 p.2 hk hs
      have heq : p=(42*k+1,44*k+9) := Prod.ext hx hy
      have hbad : BB429.run n (0,0)=some (42*k+1,44*k+9) := by simpa [heq] using hp
      exact (no_reach_deep9 n k hk) hbad

theorem no_reach_odd9 (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (40*k+3,48*k+15) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      obtain ⟨hx,hy⟩ := parent_odd9 k p.1 p.2 hk hs
      have heq : p=(20*k,88*k+18) := Prod.ext hx hy
      have hbad : BB429.run n (0,0)=some (20*k,88*k+18) := by simpa [heq] using hp
      exact (no_reach_even9 n k hk) hbad

theorem no_reach_seed9_odd (n k : Nat) (hk : k%2=1) :
    BB429.run n (0,0) ≠ some (16*k+3,96*k+26) := by
  intro hs
  cases n with
  | zero => simp [BB429.run] at hs
  | succ n =>
    simp only [BB429.run] at hs
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      rcases parent_seed9 k p.1 p.2 hk hs with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega
      · have heq : p=(40*k+3,48*k+15) := Prod.ext hx hy
        have hbad : BB429.run n (0,0)=some (40*k+3,48*k+15) := by simpa [heq] using hp
        exact (no_reach_odd9 n k hk) hbad

theorem every_halt_incoming_is_first (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (hg : b+1=2*a) : a=2*x+3 ∧ y=6*x+8 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- The full blank-root halting line excludes residue 41 modulo 64. -/
theorem no_blank_halt_41_mod64 (n a b : Nat)
    (hreach : BB429.run n (0,0)=some (a,b))
    (hline : b+1=2*a) : a%64≠41 := by
  intro hmod
  cases n with
  | zero => simp [BB429.run] at hreach; omega
  | succ n =>
    simp only [BB429.run] at hreach
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hreach
    | some p =>
      simp only [hp, Option.bind_some] at hreach
      obtain ⟨ha,hy⟩ := every_halt_incoming_is_first p.1 p.2 a b hreach hline
      let k := p.1 / 16
      have hx : p.1=16*k+3 := by dsimp [k]; omega
      have hk : k%2=1 := by dsimp [k]; omega
      have hpy : p.2=96*k+26 := by omega
      have heq : p=(16*k+3,96*k+26) := Prod.ext hx hpy
      have hbad : BB429.run n (0,0)=some (16*k+3,96*k+26) := by simpa [heq] using hp
      exact (no_reach_seed9_odd n k hk) hbad

/-- The full blank-root halting line excludes residue 49 modulo 64. -/
theorem no_blank_halt_49_mod64 (n a b : Nat)
    (hreach : BB429.run n (0,0)=some (a,b))
    (hline : b+1=2*a) : a%64≠49 := by
  intro hmod
  cases n with
  | zero => simp [BB429.run] at hreach; omega
  | succ n =>
    simp only [BB429.run] at hreach
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hreach
    | some p =>
      simp only [hp, Option.bind_some] at hreach
      obtain ⟨ha,hy⟩ := every_halt_incoming_is_first p.1 p.2 a b hreach hline
      let k := p.1 / 16
      have hx : p.1=16*k+7 := by dsimp [k]; omega
      have hk : k%2=1 := by dsimp [k]; omega
      have hpy : p.2=96*k+50 := by omega
      have heq : p=(16*k+7,96*k+50) := Prod.ext hx hpy
      have hbad : BB429.run n (0,0)=some (16*k+7,96*k+50) := by simpa [heq] using hp
      exact (no_reach_seed17_odd n k hk) hbad

#print axioms no_reach_seed17_odd
#print axioms no_reach_seed9_odd
#print axioms no_blank_halt_41_mod64
#print axioms no_blank_halt_49_mod64
end BB429NewGate
