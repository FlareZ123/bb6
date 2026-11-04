import BB429LowOddMod8
import Lean.Elab.Tactic.Omega
namespace BB429No381mod1024
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

theorem no_root_zero_1502 (n : Nat) :
    BB429.run n (0,0) ≠ some (0,1502) := by
  intro hs
  by_cases hn : n≤297
  · have hr297 : BB429.run 297 (0,0)=some (299,903) := by decide
    have heq : 297=n+(297-n) := by omega
    rw [heq,BB429.run_add,hs] at hr297
    simp only [Option.bind_some] at hr297
    have hm := (BB429.run_rank_bounds (0,1502) (299,903) (297-n) hr297).1
    simp only [BB429.rank] at hm
    omega
  · have hr298 : BB429.run 298 (0,0)=some (601,302) := by decide
    have heq : n=298+(n-298) := by omega
    rw [heq,BB429.run_add,hr298] at hs
    simp only [Option.bind_some] at hs
    have hm := (BB429.run_rank_bounds (601,302) (0,1502) (n-298) hs).1
    simp only [BB429.rank] at hm
    omega

theorem odd_first_only (n x y a b : Nat)
    (hp : BB429.run n (0,0)=some (x,y))
    (hs : BB429.next (x,y)=some (a,b))
    (ha : a%2=1) (hage : 13≤a) (hb : b%8≠2) :
    a=2*x+3 ∧ y=b+a := by
  rcases BB429LowOddMod8.admissible_odd_predecessor x y a b hs ha hage
      (fun hx he => BB429LowOddMod8.rooted_even_parity n x y hp hx he) with hfirst | hh
  · exact hfirst
  · exact False.elim (hb hh)

theorem parent_S4_pos (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (32*t+9,4032*t+1490)) :
    (x=16*t+3 ∧ y=4064*t+1499) ∨
    (x=1040*t+375 ∧ y=2016*t+747) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem parent_S4_zero (x y : Nat)
    (hs : BB429.next (x,y)=some (9,1490)) :
    x=3 ∧ y=1499 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem parent_S5_zero (x y : Nat)
    (hs : BB429.next (x,y)=some (3,1499)) :
    x=0 ∧ y=1502 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem parent_S6A (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (8*t,4080*t+1502)) :
    x=1028*t+372 ∧ y=2040*t+751 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem parent_S6B (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (520*t+186,3056*t+1122)) :
    x=1284*t+463 ∧ y=1528*t+561 := by
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

theorem no_reach_odd_of_no_parent (n a b x y : Nat)
    (ha : a%2=1) (hage : 13≤a) (hb : b%8≠2)
    (hx : a=2*x+3) (hy : y=b+a)
    (hno : ∀ k, BB429.run k (0,0) ≠ some (x,y)) :
    BB429.run n (0,0) ≠ some (a,b) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨hi,hj⟩ := odd_first_only k p.1 p.2 a b hp hr ha hage hb
      have heq : p=(x,y) := Prod.ext (by omega) (by omega)
      rw [heq] at hp
      exact (hno k) hp

theorem no_reach_S6A (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (8*t,4080*t+1502) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := parent_S6A t p.1 p.2 ht hr
      have hm := BB429LowOddMod8.rooted_even_parity k p.1 p.2 hp (by omega) (by omega)
      omega

theorem no_reach_P7B (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (1284*t+463,1528*t+561) := by
  apply no_reach_odd_of_no_parent n (1284*t+463) (1528*t+561)
      (642*t+230) (2812*t+1024) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  intro k hr
  have hm := BB429LowOddMod8.rooted_even_parity k (642*t+230) (2812*t+1024)
    hr (by omega) (by omega)
  omega

theorem no_reach_S6B (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (520*t+186,3056*t+1122) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := parent_S6B t p.1 p.2 ht hr
      have hpre : BB429.run k (0,0)=some (1284*t+463,1528*t+561) := by
        have heq : p=(1284*t+463,1528*t+561) := Prod.ext ha hy
        rw [heq] at hp
        exact hp
      exact (no_reach_P7B k t ht) hpre

theorem no_reach_S4_pos (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (32*t+9,4032*t+1490) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      rcases parent_S4_pos t p.1 p.2 ht hr with ⟨ha,hy⟩ | ⟨ha,hy⟩
      · have hpre : BB429.run k (0,0)=some (16*t+3,4064*t+1499) := by
          have heq : p=(16*t+3,4064*t+1499) := Prod.ext ha hy
          rw [heq] at hp
          exact hp
        exact no_reach_odd_of_no_parent k (16*t+3) (4064*t+1499)
          (8*t) (4080*t+1502) (by omega) (by omega) (by omega)
          (by omega) (by omega) (fun k => no_reach_S6A k t ht) hpre
      · have hpre : BB429.run k (0,0)=some (1040*t+375,2016*t+747) := by
          have heq : p=(1040*t+375,2016*t+747) := Prod.ext ha hy
          rw [heq] at hp
          exact hp
        exact no_reach_odd_of_no_parent k (1040*t+375) (2016*t+747)
          (520*t+186) (3056*t+1122) (by omega) (by omega) (by omega)
          (by omega) (by omega) (fun k => no_reach_S6B k t ht) hpre

theorem no_reach_S4_zero (n : Nat) :
    BB429.run n (0,0) ≠ some (9,1490) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨hx,hy⟩ := parent_S4_zero p.1 p.2 hr
      have hpre : BB429.run k (0,0)=some (3,1499) := by
        have heq : p=(3,1499) := Prod.ext hx hy
        rw [heq] at hp
        exact hp
      cases k with
      | zero => simp [BB429.run] at hpre
      | succ j =>
        simp only [BB429.run] at hpre
        cases hq : BB429.run j (0,0) with
        | none => simp [hq] at hpre
        | some q =>
          simp only [hq,Option.bind_some] at hpre
          obtain ⟨hx,hy⟩ := parent_S5_zero q.1 q.2 hpre
          have hzero : BB429.run j (0,0)=some (0,1502) := by
            have heq : q=(0,1502) := Prod.ext hx hy
            rw [heq] at hq
            exact hq
          exact (no_root_zero_1502 j) hzero

theorem no_reach_S4 (n t : Nat) :
    BB429.run n (0,0) ≠ some (32*t+9,4032*t+1490) := by
  cases t with
  | zero => simpa using no_reach_S4_zero n
  | succ t => exact no_reach_S4_pos n (t+1) (by omega)

theorem no_reach_S3 (n t : Nat) :
    BB429.run n (0,0) ≠ some (64*t+21,3968*t+1469) := by
  exact no_reach_odd_of_no_parent n (64*t+21) (3968*t+1469)
    (32*t+9) (4032*t+1490) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun k => no_reach_S4 k t)

theorem no_reach_S2 (n t : Nat) :
    BB429.run n (0,0) ≠ some (128*t+45,3840*t+1424) := by
  exact no_reach_odd_of_no_parent n (128*t+45) (3840*t+1424)
    (64*t+21) (3968*t+1469) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun k => no_reach_S3 k t)

theorem no_reach_S1 (n t : Nat) :
    BB429.run n (0,0) ≠ some (256*t+93,3584*t+1331) := by
  exact no_reach_odd_of_no_parent n (256*t+93) (3584*t+1331)
    (128*t+45) (3840*t+1424) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun k => no_reach_S2 k t)

theorem no_reach_S0 (n t : Nat) :
    BB429.run n (0,0) ≠ some (512*t+189,3072*t+1142) := by
  exact no_reach_odd_of_no_parent n (512*t+189) (3072*t+1142)
    (256*t+93) (3584*t+1331) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun k => no_reach_S1 k t)

theorem blank_halt_not_381_mod1024 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%1024≠381 := by
  intro hmod
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := halt_has_first_parent p.1 p.2 a b hr hg
      let t := a/1024
      have heq : p=(512*t+189,3072*t+1142) := by
        apply Prod.ext
        · dsimp [t]; omega
        · dsimp [t]; omega
      have hpre : BB429.run k (0,0)=some (512*t+189,3072*t+1142) := by
        rw [heq] at hp
        exact hp
      exact (no_reach_S0 k t) hpre

#print axioms no_root_zero_1502
#print axioms no_reach_S0
#print axioms blank_halt_not_381_mod1024
end BB429No381mod1024
