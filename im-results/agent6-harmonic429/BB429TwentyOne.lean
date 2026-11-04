import BB429NewGate
import Lean.Elab.Tactic.Omega
namespace BB429TwentyOne
set_option maxHeartbeats 8000000

/-- The only inputs of a generic preterminal 21-sector seed. -/
theorem parent_seed (k x y : Nat)
    (h : BB429.next (x,y)=some (16*k+9,96*k+62)) :
    (x=8*k+3 ∧ y=112*k+71) ∨ (x=40*k+18 ∧ y=48*k+33) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Unique input of the odd-second-counter branch. -/
theorem parent_odd (k x y : Nat)
    (h : BB429.next (x,y)=some (8*k+3,112*k+71)) :
    x=4*k ∧ y=120*k+74 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Unique input of the positive even-counter branch, for k≥2. -/
theorem parent_even (k x y : Nat) (hk : 2≤k)
    (h : BB429.next (x,y)=some (4*k,120*k+74)) :
    x=34*k+15 ∧ y=60*k+37 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Another odd-second-counter step has a unique parent. -/
theorem parent_even_odd (k x y : Nat)
    (h : BB429.next (x,y)=some (34*k+15,60*k+37)) :
    x=17*k+6 ∧ y=94*k+52 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- Even k forces its deep predecessor to have positive even first counter
    and second counter 0 modulo 4, contradictory to blank reachability. -/
theorem no_reach_neardepth (n k : Nat) (hk : k%2=0) :
    BB429.run n (0,0) ≠ some (34*k+15,60*k+37) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_even_odd k p.1 p.2 h
      have hpos : 0<p.1 := by omega
      have he : p.1%2=0 := by omega
      have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
      omega

theorem no_reach_even (n k : Nat) (hk : 2≤k) (he : k%2=0) :
    BB429.run n (0,0) ≠ some (4*k,120*k+74) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_even k p.1 p.2 hk h
      have heq : p=(34*k+15,60*k+37) := Prod.ext hx hy
      exact (no_reach_neardepth n k he) (by simpa [heq] using hp)

theorem no_reach_odd (n k : Nat) (hk : 2≤k) (he : k%2=0) :
    BB429.run n (0,0) ≠ some (8*k+3,112*k+71) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_odd k p.1 p.2 h
      have heq : p=(4*k,120*k+74) := Prod.ext hx hy
      exact (no_reach_even n k hk he) (by simpa [heq] using hp)

theorem no_reach_seed (n k : Nat) (hk : 2≤k) (he : k%2=0) :
    BB429.run n (0,0) ≠ some (16*k+9,96*k+62) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      rcases parent_seed k p.1 p.2 h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have heq : p=(8*k+3,112*k+71) := Prod.ext hx hy
        exact (no_reach_odd n k hk he) (by simpa [heq] using hp)
      · have hpos : 0<p.1 := by omega
        have hev : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos hev
        omega

/-- Every reachable halting line counter u≡21(mod64) with u>21 is excluded. -/
theorem blank_no_twentyone_mod64_above21 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) (hm : a%64=21) (ha : 21<a) : False := by
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      have hparent := BB429NewGate.every_halt_incoming_is_first p.1 p.2 a b hr hg
      let k := p.1/16
      have hx : p.1=16*k+9 := by dsimp [k]; omega
      have he : k%2=0 := by dsimp [k]; omega
      have hk : 2≤k := by omega
      have hy : p.2=96*k+62 := by omega
      have heq : p=(16*k+9,96*k+62) := Prod.ext hx hy
      exact (no_reach_seed n k hk he) (by simpa [heq] using hp)

/-- Exact short-prefix exclusion of the only zero-first-counter exception. -/
theorem no_reach_zero_seventyfour (n : Nat) :
    BB429.run n (0,0) ≠ some (0,74) := by
  intro h
  by_cases hn : n<12
  · have hf : ∀ i : Fin 12, BB429.run i.val (0,0) ≠ some (0,74) := by decide
    exact (hf ⟨n,hn⟩) h
  · have h12 : BB429.run 12 (0,0) = some (11,62) := by decide
    have hc : BB429.run n (0,0)=BB429.run (n-12) (11,62) := by
      calc
        BB429.run n (0,0)=BB429.run (12+(n-12)) (0,0) := by
          congr 1
          omega
        _ = BB429.run (n-12) (11,62) := by
          rw [BB429.run_add,h12]
          rfl
    rw [hc] at h
    have hr := (BB429.run_rank_bounds (11,62) (0,74) (n-12) h).1
    simp only [BB429.rank] at hr
    omega

theorem no_reach_odd_zero (n : Nat) :
    BB429.run n (0,0) ≠ some (3,71) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      obtain ⟨hx,hy⟩ := parent_odd 0 p.1 p.2 h
      have heq : p=(0,74) := by apply Prod.ext <;> omega
      exact (no_reach_zero_seventyfour n) (by simpa [heq] using hp)

theorem no_reach_seed_zero (n : Nat) :
    BB429.run n (0,0) ≠ some (9,62) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      rcases parent_seed 0 p.1 p.2 h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have heq : p=(3,71) := Prod.ext hx hy
        exact (no_reach_odd_zero n) (by simpa [heq] using hp)
      · have hpos : 0<p.1 := by omega
        have hev : p.1%2=0 := by omega
        have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos hev
        omega

/-- Full all-time exclusion of the 21(mod64) blank-tape terminal sector. -/
theorem blank_no_twentyone_mod64 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%64≠21 := by
  intro hm
  by_cases ha : a=21
  · cases n with
    | zero => simp [BB429.run] at hr; omega
    | succ n =>
      simp only [BB429.run] at hr
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hr
      | some p =>
        simp only [hp,Option.bind_some] at hr
        obtain ⟨hx,hy⟩ := BB429NewGate.every_halt_incoming_is_first p.1 p.2 a b hr hg
        have heq : p=(9,62) := by apply Prod.ext <;> omega
        exact (no_reach_seed_zero n) (by simpa [heq] using hp)
  · exact blank_no_twentyone_mod64_above21 n a b hr hg hm (by omega)

#print axioms no_reach_zero_seventyfour
#print axioms no_reach_seed_zero
#print axioms blank_no_twentyone_mod64

#print axioms no_reach_seed
#print axioms blank_no_twentyone_mod64_above21
end BB429TwentyOne
