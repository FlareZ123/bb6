import BB429NewGate
import Lean.Elab.Tactic.Omega
namespace BB429NoSixtyOne128
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

/-- An incoming zero-counter step has even second counter. -/
theorem zero_step_even (x y b : Nat)
    (hs : BB429.next (x,y)=some (0,b)) : b%2=0 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem root_zero_even (n b : Nat)
    (hr : BB429.run n (0,0)=some (0,b)) : b%2=0 := by
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      exact zero_step_even p.1 p.2 b hr

theorem feeder_parent (q x y : Nat)
    (hs : BB429.next (x,y)=some (64*q+29,384*q+182)) :
    (x=32*q+13 ∧ y=448*q+211) ∨
    (x=160*q+68 ∧ y=192*q+93) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_A (q x y : Nat)
    (hs : BB429.next (x,y)=some (32*q+13,448*q+211)) :
    x=16*q+5 ∧ y=480*q+224 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_B (q x y : Nat)
    (hs : BB429.next (x,y)=some (16*q+5,480*q+224)) :
    x=8*q+1 ∧ y=496*q+229 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_C (q x y : Nat)
    (hs : BB429.next (x,y)=some (8*q+1,496*q+229)) :
    0<q ∧ x=4*q-1 ∧ y=504*q+230 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_D (q x y : Nat) (hq : 0<q) (h3 : q≠3)
    (hs : BB429.next (x,y)=some (4*q-1,504*q+230)) :
    (x=2*q-2 ∧ y=508*q+229) ∨
    (x=130*q+50 ∧ y=252*q+117) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Special first-counter-11 q=3 branch, resolved by finite prefix plus rank. -/
theorem no_reach_eleven1742 (n : Nat) :
    BB429.run n (0,0) ≠ some (11,1742) := by
  intro h
  by_cases hn : n<351
  · have hf : ∀ i : Fin 351, BB429.run i.val (0,0) ≠ some (11,1742) := by decide
    exact (hf ⟨n,hn⟩) h
  · have h351 : BB429.run 351 (0,0)=some (21,1723) := by decide
    have hc : BB429.run n (0,0)=BB429.run (n-351) (21,1723) := by
      calc
        BB429.run n (0,0)=BB429.run (351+(n-351)) (0,0) := by
          congr 1
          omega
        _ = BB429.run (n-351) (21,1723) := by
          rw [BB429.run_add,h351]
          rfl
    rw [hc] at h
    have hbound := (BB429.run_rank_bounds (21,1723) (11,1742) (n-351) h).1
    simp only [BB429.rank] at hbound
    omega

theorem no_reach_D (n q : Nat) (hq : 0<q) :
    BB429.run n (0,0) ≠ some (4*q-1,504*q+230) := by
  by_cases h3 : q=3
  · subst q
    simpa using no_reach_eleven1742 n
  · intro h
    cases n with
    | zero => simp [BB429.run] at h
    | succ n =>
      simp only [BB429.run] at h
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at h
      | some p =>
        simp only [hp,Option.bind_some] at h
        rcases parent_D q p.1 p.2 hq h3 h with ⟨hx,hy⟩ | ⟨hx,hy⟩
        · by_cases hone : q=1
          · have hz : p.1=0 := by omega
            have hpr : BB429.run n (0,0)=some (0,p.2) := by
              rw [hp]
              exact congrArg some (Prod.ext hz rfl)
            have hbad := root_zero_even n p.2 hpr
            omega
          · have hpos : 0<p.1 := by omega
            have he : p.1%2=0 := by omega
            have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
            omega
        · have hpos : 0<p.1 := by omega
          have he : p.1%2=0 := by omega
          have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
          omega

theorem no_reach_C (n q : Nat) :
    BB429.run n (0,0) ≠ some (8*q+1,496*q+229) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hq,hx,hy⟩ := parent_C q p.1 p.2 h
      have heq : p=(4*q-1,504*q+230) := Prod.ext hx hy
      exact (no_reach_D n q hq) (by simpa [heq] using hp)

theorem no_reach_B (n q : Nat) :
    BB429.run n (0,0) ≠ some (16*q+5,480*q+224) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_B q p.1 p.2 h
      have heq : p=(8*q+1,496*q+229) := Prod.ext hx hy
      exact (no_reach_C n q) (by simpa [heq] using hp)

theorem no_reach_A (n q : Nat) :
    BB429.run n (0,0) ≠ some (32*q+13,448*q+211) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_A q p.1 p.2 h
      have heq : p=(16*q+5,480*q+224) := Prod.ext hx hy
      exact (no_reach_B n q) (by simpa [heq] using hp)

theorem no_reach_feeder (n q : Nat) :
    BB429.run n (0,0) ≠ some (64*q+29,384*q+182) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      rcases feeder_parent q p.1 p.2 h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have heq : p=(32*q+13,448*q+211) := Prod.ext hx hy
        exact (no_reach_A n q) (by simpa [heq] using hp)
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega

theorem blank_halt_not_61_mod128 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%128≠61 := by
  intro hm
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := BB429NewGate.every_halt_incoming_is_first p.1 p.2 a b hr hg
      let q := p.1/64
      have hx : p.1=64*q+29 := by dsimp [q]; omega
      have hpy : p.2=384*q+182 := by omega
      have heq : p=(64*q+29,384*q+182) := Prod.ext hx hpy
      exact (no_reach_feeder n q) (by simpa [heq] using hp)

#print axioms zero_step_even
#print axioms root_zero_even
#print axioms no_reach_eleven1742
#print axioms blank_halt_not_61_mod128
end BB429NoSixtyOne128
