import BB429NewGate
import Lean.Elab.Tactic.Omega
namespace BB429Deep17
set_option maxHeartbeats 8000000

theorem parent_quart (s x y : Nat) (hs : 0<s)
   (h : BB429.next (x,y)=some (20*s-1,472*s+46)) :
   (x=10*s-2 ∧ y=492*s+45) ∨ (x=138*s+4 ∧ y=236*s+25) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem no_reach_quart_parent (n s : Nat) (hs : 0<s) :
  BB429.run n (0,0) ≠ some (20*s-1,472*s+46) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      rcases parent_quart s p.1 p.2 hs h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega

theorem parent_quart_deep (s x y : Nat) (hs : 0<s)
   (h : BB429.next (x,y)=some (40*s+1,432*s+45)) :
   x=20*s-1 ∧ y=472*s+46 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem no_reach_quart_deep (n s : Nat) (hs : 0<s) :
  BB429.run n (0,0) ≠ some (40*s+1,432*s+45) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_quart_deep s p.1 p.2 hs h
      have heq : p=(20*s-1,472*s+46) := Prod.ext hx hy
      have hbad : BB429.run n (0,0)=some (20*s-1,472*s+46) := by simpa [heq] using hp
      exact (no_reach_quart_parent n s hs) hbad

theorem no_input_one (x y : Nat) (h : BB429.next (x,y)=some (1,45)) : False := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem no_reach_one_fortyfive (n : Nat) :
  BB429.run n (0,0) ≠ some (1,45) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      exact no_input_one p.1 p.2 h

theorem no_reach_deep17_4 (n s : Nat) :
  BB429.run n (0,0) ≠ some (40*s+1,432*s+45) := by
  cases s with
  | zero => simpa using no_reach_one_fortyfive n
  | succ s => exact no_reach_quart_deep n (s+1) (by omega)

theorem no_reach_17_of_deep (n k : Nat)
    (hdeep : ∀ i, BB429.run i (0,0) ≠ some (10*k+1,108*k+45)) :
    BB429.run n (0,0) ≠ some (16*k+7,96*k+50) := by
  have hdiv : ∀ i, BB429.run i (0,0) ≠ some (20*k+5,88*k+40) := by
    intro i hi
    cases i with
    | zero => simp [BB429.run] at hi
    | succ i =>
      simp only [BB429.run] at hi
      cases hp : BB429.run i (0,0) with
      | none => simp [hp] at hi
      | some p =>
        simp only [hp, Option.bind_some] at hi
        obtain ⟨hx,hy⟩ := BB429NewGate.parent_divfour17 k p.1 p.2 hi
        have heq : p=(10*k+1,108*k+45) := Prod.ext hx hy
        exact (hdeep i) (by simpa [heq] using hp)
  have hodd : ∀ i, BB429.run i (0,0) ≠ some (40*k+13,48*k+27) := by
    intro i hi
    cases i with
    | zero => simp [BB429.run] at hi
    | succ i =>
      simp only [BB429.run] at hi
      cases hp : BB429.run i (0,0) with
      | none => simp [hp] at hi
      | some p =>
        simp only [hp, Option.bind_some] at hi
        obtain ⟨hx,hy⟩ := BB429NewGate.parent_odd17 k p.1 p.2 hi
        have heq : p=(20*k+5,88*k+40) := Prod.ext hx hy
        exact (hdiv i) (by simpa [heq] using hp)
  intro hi
  cases n with
  | zero => simp [BB429.run] at hi
  | succ n =>
    simp only [BB429.run] at hi
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hi
    | some p =>
      simp only [hp, Option.bind_some] at hi
      rcases BB429NewGate.parent_seed17 k p.1 p.2 hi with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have hpos : 0<p.1 := by omega
        have he : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
        omega
      · have heq : p=(40*k+13,48*k+27) := Prod.ext hx hy
        exact (hodd n) (by simpa [heq] using hp)

theorem no_reach_seed17_4 (n s : Nat) :
  BB429.run n (0,0) ≠ some (64*s+7,384*s+50) := by
  have h1 : 10*(4*s)+1 = 40*s+1 := by omega
  have h2 : 108*(4*s)+45 = 432*s+45 := by omega
  have h3 : 16*(4*s)+7 = 64*s+7 := by omega
  have h4 : 96*(4*s)+50 = 384*s+50 := by omega
  have hd : ∀ i, BB429.run i (0,0) ≠ some (10*(4*s)+1,108*(4*s)+45) := by
    intro i
    simpa only [h1,h2] using no_reach_deep17_4 i s
  have h := no_reach_17_of_deep n (4*s) hd
  simpa only [h3,h4] using h

/-- Any blank terminal in the 17(mod32) sector must be 81(mod128). -/
theorem blank_17_sector_must_81 (n a b : Nat)
  (hr : BB429.run n (0,0)=some (a,b))
  (hg : b+1=2*a)
  (h17 : a%32=17) : a%128=81 := by
  have h49 := BB429NewGate.no_blank_halt_49_mod64 n a b hr hg
  have h17mod128 : a%128≠17 := by
    intro hmod
    cases n with
    | zero => simp [BB429.run] at hr; omega
    | succ n =>
      simp only [BB429.run] at hr
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hr
      | some p =>
        simp only [hp, Option.bind_some] at hr
        obtain ⟨ha,hy⟩ := BB429NewGate.every_halt_incoming_is_first p.1 p.2 a b hr hg
        let s := p.1 / 64
        have hx : p.1=64*s+7 := by dsimp [s]; omega
        have hpy : p.2=384*s+50 := by omega
        have heq : p=(64*s+7,384*s+50) := Prod.ext hx hpy
        exact (no_reach_seed17_4 n s) (by simpa [heq] using hp)
  have h113mod128 : a%128≠113 := by omega
  omega

#print axioms no_reach_seed17_4
#print axioms blank_17_sector_must_81
end BB429Deep17
