import BB429NewGate
import Lean.Elab.Tactic.Omega
namespace BB429NoNinetyThree128
set_option maxHeartbeats 9000000

/-- Two inverse families for the 93-mod128 terminal feeder. -/
theorem feeder_parent (q x y : Nat)
    (hs : BB429.next (x,y)=some (64*q+45,384*q+278)) :
    (x=32*q+21 ∧ y=448*q+323) ∨
    (x=160*q+108 ∧ y=192*q+141) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_A (q x y : Nat)
    (hs : BB429.next (x,y)=some (32*q+21,448*q+323)) :
    x=16*q+9 ∧ y=480*q+344 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_B (q x y : Nat)
    (hs : BB429.next (x,y)=some (16*q+9,480*q+344)) :
    x=8*q+3 ∧ y=496*q+353 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_C (q x y : Nat)
    (hs : BB429.next (x,y)=some (8*q+3,496*q+353)) :
    x=4*q ∧ y=504*q+356 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- A finite exact root prefix plus strict rank increase rules out the
    exceptional q=0 state (0,356) for all time. -/
theorem no_reach_zero356 (n : Nat) :
    BB429.run n (0,0) ≠ some (0,356) := by
  intro h
  by_cases hn : n<63
  · have hf : ∀ i : Fin 63, BB429.run i.val (0,0) ≠ some (0,356) := by decide
    exact (hf ⟨n,hn⟩) h
  · have h63 : BB429.run 63 (0,0) = some (93,173) := by decide
    have hc : BB429.run n (0,0)=BB429.run (n-63) (93,173) := by
      calc
        BB429.run n (0,0)=BB429.run (63+(n-63)) (0,0) := by
          congr 1
          omega
        _ = BB429.run (n-63) (93,173) := by
          rw [BB429.run_add,h63]
          rfl
    rw [hc] at h
    have hr := (BB429.run_rank_bounds (93,173) (0,356) (n-63) h).1
    simp only [BB429.rank] at hr
    omega

theorem no_reach_C (n q : Nat) :
    BB429.run n (0,0) ≠ some (8*q+3,496*q+353) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_C q p.1 p.2 h
      by_cases hq : q=0
      · subst q
        have heq : p=(0,356) := by apply Prod.ext <;> omega
        exact (no_reach_zero356 n) (by simpa [heq] using hp)
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega

theorem no_reach_B (n q : Nat) :
    BB429.run n (0,0) ≠ some (16*q+9,480*q+344) := by
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
      have heq : p=(8*q+3,496*q+353) := Prod.ext hx hy
      exact (no_reach_C n q) (by simpa [heq] using hp)

theorem no_reach_A (n q : Nat) :
    BB429.run n (0,0) ≠ some (32*q+21,448*q+323) := by
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
      have heq : p=(16*q+9,480*q+344) := Prod.ext hx hy
      exact (no_reach_B n q) (by simpa [heq] using hp)

theorem no_reach_feeder (n q : Nat) :
    BB429.run n (0,0) ≠ some (64*q+45,384*q+278) := by
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
      · have heq : p=(32*q+21,448*q+323) := Prod.ext hx hy
        exact (no_reach_A n q) (by simpa [heq] using hp)
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega

/-- No terminal from true blank start may have first counter 93 modulo128. -/
theorem blank_halt_not_93_mod128 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%128≠93 := by
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
      have hx : p.1=64*q+45 := by dsimp [q]; omega
      have hpy : p.2=384*q+278 := by omega
      have heq : p=(64*q+45,384*q+278) := Prod.ext hx hpy
      exact (no_reach_feeder n q) (by simpa [heq] using hp)

#print axioms feeder_parent
#print axioms no_reach_zero356
#print axioms blank_halt_not_93_mod128
end BB429NoNinetyThree128
