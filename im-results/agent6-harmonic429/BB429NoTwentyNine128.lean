import BB429NewGate
import Lean.Elab.Tactic.Omega
namespace BB429NoTwentyNine128
set_option maxHeartbeats 9000000

/-- Exact two-way inverse at the 29-mod128 terminal predecessor. -/
theorem feeder_parent (q x y : Nat)
    (hs : BB429.next (x,y)=some (64*q+13,384*q+86)) :
    (x=32*q+5 ∧ y=448*q+99) ∨
    (x=160*q+28 ∧ y=192*q+45) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_A (q x y : Nat)
    (hs : BB429.next (x,y)=some (32*q+5,448*q+99)) :
    x=16*q+1 ∧ y=480*q+104 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_B (q x y : Nat)
    (hs : BB429.next (x,y)=some (16*q+1,480*q+104)) :
    0<q ∧ x=8*q-1 ∧ y=496*q+105 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem parent_C (q x y : Nat) (hq : 0<q)
    (hs : BB429.next (x,y)=some (8*q-1,496*q+105)) :
    x=4*q-2 ∧ y=504*q+104 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Final family lies behind forbidden even-positive odd-parity predecessor. -/
theorem no_reach_C (n q : Nat) (hq : 0<q) :
    BB429.run n (0,0) ≠ some (8*q-1,496*q+105) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_C q p.1 p.2 hq h
      have hpos : 0<p.1 := by omega
      have he : p.1%2=0 := by omega
      have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
      omega

theorem no_reach_B (n q : Nat) :
    BB429.run n (0,0) ≠ some (16*q+1,480*q+104) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hq,hx,hy⟩ := parent_B q p.1 p.2 h
      have heq : p=(8*q-1,496*q+105) := Prod.ext hx hy
      exact (no_reach_C n q hq) (by simpa [heq] using hp)

theorem no_reach_A (n q : Nat) :
    BB429.run n (0,0) ≠ some (32*q+5,448*q+99) := by
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
      have heq : p=(16*q+1,480*q+104) := Prod.ext hx hy
      exact (no_reach_B n q) (by simpa [heq] using hp)

theorem no_reach_feeder (n q : Nat) :
    BB429.run n (0,0) ≠ some (64*q+13,384*q+86) := by
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
      · have heq : p=(32*q+5,448*q+99) := Prod.ext hx hy
        exact (no_reach_A n q) (by simpa [heq] using hp)
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega

/-- No terminal from true blank start may have first counter 29 modulo128. -/
theorem blank_halt_not_29_mod128 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%128≠29 := by
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
      have hx : p.1=64*q+13 := by dsimp [q]; omega
      have hpy : p.2=384*q+86 := by omega
      have heq : p=(64*q+13,384*q+86) := Prod.ext hx hpy
      exact (no_reach_feeder n q) (by simpa [heq] using hp)

#print axioms feeder_parent
#print axioms no_reach_feeder
#print axioms blank_halt_not_29_mod128
end BB429NoTwentyNine128
