import BB429No381mod1024
import Lean.Elab.Tactic.Omega
namespace BB429No509mod1024
set_option maxHeartbeats 50000000
set_option maxRecDepth 30000

private theorem no_zero6104 (n : Nat) :
    BB429.run n (0,0) ≠ some (0,6104) := by
  intro h
  by_cases hn : n≤1306
  · have hf : BB429.run 1306 (0,0)=some (51,5999) := by decide
    have he : 1306=n+(1306-n) := by omega
    rw [he,BB429.run_add,h] at hf
    simp only [Option.bind_some] at hf
    have hm := (BB429.run_rank_bounds (0,6104) (51,5999) (1306-n) hf).1
    simp only [BB429.rank] at hm
    omega
  · by_cases hn2 : n=1307
    · subst n
      have hf : BB429.run 1307 (0,0)=some (105,5894) := by decide
      rw [hf] at h
      cases h
    · have hf : BB429.run 1307 (0,0)=some (105,5894) := by decide
      have he : n=1307+(n-1307) := by omega
      rw [he,BB429.run_add,hf] at h
      simp only [Option.bind_some] at h
      have hm := (BB429.run_rank_bounds (105,5894) (0,6104) (n-1307) h).1
      simp only [BB429.rank] at hm
      omega

private theorem parent_A2 (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (8*t+1,4080*t+2012)) :
    x=4*t-1 ∧ y=4088*t+2013 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem parent_A3 (t x y : Nat) (ht : 0<t)
    (hs : BB429.next (x,y)=some (4*t-1,4088*t+2013)) :
    x=2*t-2 ∧ y=4092*t+2012 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem parent_split (t x y : Nat)
    (hs : BB429.next (x,y)=some (32*t+13,4032*t+1994)) :
    (x=16*t+5 ∧ y=4064*t+2007) ∨
    (x=1040*t+505 ∧ y=2016*t+999) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem no_reach_A3 (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (4*t-1,4088*t+2013) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := parent_A3 t p.1 p.2 ht hr
      have hpre : BB429.run n (0,0)=some (2*t-2,4092*t+2012) := by
        have hpeq : p=(2*t-2,4092*t+2012) := Prod.ext ha hy
        rw [hpeq] at hp
        exact hp
      by_cases h1 : t=1
      · subst t
        simpa using (no_zero6104 n hpre)
      · have hm := BB429LowOddMod8.rooted_even_parity n (2*t-2) (4092*t+2012)
          hpre (by omega) (by omega)
        omega

private theorem no_reach_A2 (n t : Nat) (ht : 0<t) :
    BB429.run n (0,0) ≠ some (8*t+1,4080*t+2012) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := parent_A2 t p.1 p.2 ht hr
      have hpre : BB429.run n (0,0)=some (4*t-1,4088*t+2013) := by
        have hpeq : p=(4*t-1,4088*t+2013) := Prod.ext ha hy
        rw [hpeq] at hp
        exact hp
      exact (no_reach_A3 n t ht) hpre

private theorem no_reach_A (n t : Nat) :
    BB429.run n (0,0) ≠ some (16*t+5,4064*t+2007) := by
  cases t with
  | zero => simpa using BB429LowOddMod8.root_ne_five n 2007
  | succ t =>
    exact BB429No381mod1024.no_reach_odd_of_no_parent n
      (16*(t+1)+5) (4064*(t+1)+2007)
      (8*(t+1)+1) (4080*(t+1)+2012)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun k => no_reach_A2 k (t+1) (by omega))

private theorem no_reach_B2 (n t : Nat) :
    BB429.run n (0,0) ≠ some (260*t+124,3576*t+1755) := by
  intro hr
  have hm := BB429LowOddMod8.rooted_even_parity n (260*t+124) (3576*t+1755)
    hr (by omega) (by omega)
  omega

private theorem no_reach_B1 (n t : Nat) :
    BB429.run n (0,0) ≠ some (520*t+251,3056*t+1504) := by
  exact BB429No381mod1024.no_reach_odd_of_no_parent n
    (520*t+251) (3056*t+1504)
    (260*t+124) (3576*t+1755)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k => no_reach_B2 k t)

private theorem no_reach_B (n t : Nat) :
    BB429.run n (0,0) ≠ some (1040*t+505,2016*t+999) := by
  exact BB429No381mod1024.no_reach_odd_of_no_parent n
    (1040*t+505) (2016*t+999)
    (520*t+251) (3056*t+1504)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k => no_reach_B1 k t)

private theorem no_reach_S4 (n t : Nat) :
    BB429.run n (0,0) ≠ some (32*t+13,4032*t+1994) := by
  intro hr
  cases n with
  | zero => simp [BB429.run] at hr
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      rcases parent_split t p.1 p.2 hr with ⟨ha,hy⟩ | ⟨ha,hy⟩
      · have hpre : BB429.run n (0,0)=some (16*t+5,4064*t+2007) := by
          have he : p=(16*t+5,4064*t+2007) := Prod.ext ha hy
          rw [he] at hp
          exact hp
        exact (no_reach_A n t) hpre
      · have hpre : BB429.run n (0,0)=some (1040*t+505,2016*t+999) := by
          have he : p=(1040*t+505,2016*t+999) := Prod.ext ha hy
          rw [he] at hp
          exact hp
        exact (no_reach_B n t) hpre

private theorem no_reach_S3 (n t : Nat) :
    BB429.run n (0,0) ≠ some (64*t+29,3968*t+1965) := by
  exact BB429No381mod1024.no_reach_odd_of_no_parent n
    (64*t+29) (3968*t+1965) (32*t+13) (4032*t+1994)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k => no_reach_S4 k t)

private theorem no_reach_S2 (n t : Nat) :
    BB429.run n (0,0) ≠ some (128*t+61,3840*t+1904) := by
  exact BB429No381mod1024.no_reach_odd_of_no_parent n
    (128*t+61) (3840*t+1904) (64*t+29) (3968*t+1965)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k => no_reach_S3 k t)

private theorem no_reach_S1 (n t : Nat) :
    BB429.run n (0,0) ≠ some (256*t+125,3584*t+1779) := by
  exact BB429No381mod1024.no_reach_odd_of_no_parent n
    (256*t+125) (3584*t+1779) (128*t+61) (3840*t+1904)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k => no_reach_S2 k t)

private theorem no_reach_S0 (n t : Nat) :
    BB429.run n (0,0) ≠ some (512*t+253,3072*t+1526) := by
  exact BB429No381mod1024.no_reach_odd_of_no_parent n
    (512*t+253) (3072*t+1526) (256*t+125) (3584*t+1779)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun k => no_reach_S1 k t)

private theorem terminal_parent (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b)) (hg : b+1=2*a) :
    a=2*x+3 ∧ y=6*x+8 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem blank_halt_not_509_mod1024 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%1024≠509 := by
  intro hm
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := terminal_parent p.1 p.2 a b hr hg
      let t := a/1024
      have hpe : p=(512*t+253,3072*t+1526) := by
        apply Prod.ext
        · dsimp [t]; omega
        · dsimp [t]; omega
      have hpr : BB429.run n (0,0)=some (512*t+253,3072*t+1526) := by
        rw [hpe] at hp
        exact hp
      exact (no_reach_S0 n t) hpr

#print axioms no_zero6104
#print axioms blank_halt_not_509_mod1024
end BB429No509mod1024
