import BB429LowOddMod8
import Lean.Elab.Tactic.Omega
namespace BB429No125mod1024
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

theorem odd_first_only (n x y a b : Nat)
    (hp : BB429.run n (0,0)=some (x,y))
    (hs : BB429.next (x,y)=some (a,b))
    (ha : a%2=1) (hage : 13≤a) (hb : b%8≠2) :
    a=2*x+3 ∧ y=b+a := by
  have h := BB429LowOddMod8.admissible_odd_predecessor x y a b
    hs ha hage (fun hx he => BB429LowOddMod8.rooted_even_parity n x y hp hx he)
  rcases h with hfirst | hh
  · exact hfirst
  · exact False.elim (hb hh)

theorem parent_S4 (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (32*t+1,4032*t+482)) :
    (x=16*t-1 ∧ y=4064*t+483) ∨
    (x=1040*t+115 ∧ y=2016*t+243) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem parent_S6A (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (8*t-2,4080*t+482)) :
    x=1028*t+115 ∧ y=2040*t+241 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem parent_S6B (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (520*t+56,3056*t+358)) :
    x=1284*t+142 ∧ y=1528*t+179 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem halt_has_first_parent (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (hg : b+1=2*a) : a=2*x+3 ∧ y=6*x+8 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem no_reach_P7A (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (1028*t+115,2040*t+241) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (1028*t+115)
        (2040*t+241) hp hr (by omega) (by omega) (by omega)
      have hpos : 0<p.1 := by omega
      have he : p.1%2=0 := by omega
      have hm := BB429LowOddMod8.rooted_even_parity n p.1 p.2 hp hpos he
      omega

theorem no_reach_S6A (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (8*t-2,4080*t+482) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := parent_S6A t p.1 p.2 ht hr
      have hpre : BB429.run n (0,0)=some (1028*t+115,2040*t+241) := by
        have hpeq : p=(1028*t+115,2040*t+241) := Prod.ext ha hy
        rw [hpeq] at hp
        exact hp
      exact (no_reach_P7A n t ht) hpre

theorem no_reach_S5A (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (16*t-1,4064*t+483) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (16*t-1)
        (4064*t+483) hp hr (by omega) (by omega) (by omega)
      have hpre : BB429.run n (0,0)=some (8*t-2,4080*t+482) := by
        have hpeq : p=(8*t-2,4080*t+482) := Prod.ext (by omega) (by omega)
        rw [hpeq] at hp
        exact hp
      exact (no_reach_S6A n t ht) hpre

theorem no_reach_S6B (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (520*t+56,3056*t+358) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := parent_S6B t p.1 p.2 ht hr
      have hm := BB429LowOddMod8.rooted_even_parity n p.1 p.2 hp
        (by omega) (by omega)
      omega

theorem no_reach_S5B (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (1040*t+115,2016*t+243) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (1040*t+115)
        (2016*t+243) hp hr (by omega) (by omega) (by omega)
      have hpre : BB429.run n (0,0)=some (520*t+56,3056*t+358) := by
        have hpeq : p=(520*t+56,3056*t+358) := Prod.ext (by omega) (by omega)
        rw [hpeq] at hp
        exact hp
      exact (no_reach_S6B n t ht) hpre

theorem no_reach_S4 (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (32*t+1,4032*t+482) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      rcases parent_S4 t p.1 p.2 ht hr with ⟨ha,hy⟩ | ⟨ha,hy⟩
      · have hpre : BB429.run n (0,0)=some (16*t-1,4064*t+483) := by
          have hpeq : p=(16*t-1,4064*t+483) := Prod.ext ha hy
          rw [hpeq] at hp
          exact hp
        exact (no_reach_S5A n t ht) hpre
      · have hpre : BB429.run n (0,0)=some (1040*t+115,2016*t+243) := by
          have hpeq : p=(1040*t+115,2016*t+243) := Prod.ext ha hy
          rw [hpeq] at hp
          exact hp
        exact (no_reach_S5B n t ht) hpre

theorem no_reach_S3 (n t : Nat) :
    BB429.run n (0,0) ≠ some (64*t+5,3968*t+477) := by
  cases t with
  | zero => simpa using BB429LowOddMod8.root_ne_five n 477
  | succ t =>
    intro hr
    cases n with
    | zero => simp [BB429.run] at hr
    | succ n =>
      simp only [BB429.run] at hr
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hr
      | some p =>
        simp only [hp,Option.bind_some] at hr
        obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (64*(t+1)+5)
          (3968*(t+1)+477) hp hr (by omega) (by omega) (by omega)
        have hpre : BB429.run n (0,0)=some (32*(t+1)+1,4032*(t+1)+482) := by
          have hpeq : p=(32*(t+1)+1,4032*(t+1)+482) := Prod.ext (by omega) (by omega)
          rw [hpeq] at hp
          exact hp
        exact (no_reach_S4 n (t+1) (by omega)) hpre

theorem no_reach_S2 (n t : Nat) :
    BB429.run n (0,0) ≠ some (128*t+13,3840*t+464) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (128*t+13)
        (3840*t+464) hp hr (by omega) (by omega) (by omega)
      have hpre : BB429.run n (0,0)=some (64*t+5,3968*t+477) := by
        have hpeq : p=(64*t+5,3968*t+477) := Prod.ext (by omega) (by omega)
        rw [hpeq] at hp
        exact hp
      exact (no_reach_S3 n t) hpre

theorem no_reach_S1 (n t : Nat) :
    BB429.run n (0,0) ≠ some (256*t+29,3584*t+435) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (256*t+29)
        (3584*t+435) hp hr (by omega) (by omega) (by omega)
      have hpre : BB429.run n (0,0)=some (128*t+13,3840*t+464) := by
        have hpeq : p=(128*t+13,3840*t+464) := Prod.ext (by omega) (by omega)
        rw [hpeq] at hp
        exact hp
      exact (no_reach_S2 n t) hpre

theorem no_reach_S0 (n t : Nat) :
    BB429.run n (0,0) ≠ some (512*t+61,3072*t+374) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := odd_first_only n p.1 p.2 (512*t+61)
        (3072*t+374) hp hr (by omega) (by omega) (by omega)
      have hpre : BB429.run n (0,0)=some (256*t+29,3584*t+435) := by
        have hpeq : p=(256*t+29,3584*t+435) := Prod.ext (by omega) (by omega)
        rw [hpeq] at hp
        exact hp
      exact (no_reach_S1 n t) hpre

theorem blank_halt_not_125_mod1024 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%1024≠125 := by
  intro hm
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := halt_has_first_parent p.1 p.2 a b hr hg
      let t := a/1024
      have he : p=(512*t+61,3072*t+374) := by
        apply Prod.ext
        · dsimp [t]; omega
        · dsimp [t]; omega
      have hpre : BB429.run n (0,0)=some (512*t+61,3072*t+374) := by
        rw [he] at hp
        exact hp
      exact (no_reach_S0 n t) hpre

#print axioms parent_S4
#print axioms parent_S6A
#print axioms parent_S6B
#print axioms no_reach_S0
#print axioms blank_halt_not_125_mod1024
end BB429No125mod1024
