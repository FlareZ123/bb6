import BB429Mod8
import BB429LowOddMod8
import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429No509
set_option maxHeartbeats 10000000
set_option maxRecDepth 6000

private def Reach (u w : Nat) : Prop :=
  ∃ n, BB429.run n (0,0) = some (u,w)

private theorem predecessor (u w : Nat) (hu : 0<u)
    (hr : Reach u w) :
    ∃ n x y, BB429.run n (0,0)=some (x,y) ∧
      BB429.next (x,y)=some (u,w) := by
  rcases hr with ⟨n,hn⟩
  cases n with
  | zero =>
    simp [BB429.run] at hn
    omega
  | succ k =>
    simp only [BB429.run] at hn
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hn
    | some p =>
      simp only [hp, Option.bind_some] at hn
      exact ⟨k,p.1,p.2,hp,hn⟩

private theorem unique_parent (u w x y : Nat)
    (hu : 0<u) (hr : Reach u w)
    (hp : ∀ a b, BB429.next (a,b)=some (u,w) → a=x ∧ b=y) : Reach x y := by
  obtain ⟨n,a,b,ha,hb⟩ := predecessor u w hu hr
  obtain ⟨rfl,rfl⟩ := hp a b hb
  exact ⟨n,ha⟩

private theorem two_parents (u w x y x' y' : Nat)
    (hu : 0<u) (hr : Reach u w)
    (hp : ∀ a b, BB429.next (a,b)=some (u,w) →
      (a=x ∧ b=y) ∨ (a=x' ∧ b=y')) :
    Reach x y ∨ Reach x' y' := by
  obtain ⟨n,a,b,ha,hb⟩ := predecessor u w hu hr
  rcases hp a b hb with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨n,ha⟩
  · exact Or.inr ⟨n,ha⟩



private theorem p0 (q x y : Nat)
  (h : BB429.next (x,y)=some (1024*q+509,2048*q+1017)) :
  x=512*q+253 ∧ y=3072*q+1526 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p1 (q x y : Nat)
  (h : BB429.next (x,y)=some (512*q+253,3072*q+1526)) :
  (x=256*q+125 ∧ y=3584*q+1779) ∨
  (x=1280*q+628 ∧ y=1536*q+765) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p2 (q x y : Nat)
  (h : BB429.next (x,y)=some (256*q+125,3584*q+1779)) :
  x=128*q+61 ∧ y=3840*q+1904 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p3 (q x y : Nat)
  (h : BB429.next (x,y)=some (128*q+61,3840*q+1904)) :
  x=64*q+29 ∧ y=3968*q+1965 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p4 (q x y : Nat)
  (h : BB429.next (x,y)=some (64*q+29,3968*q+1965)) :
  x=32*q+13 ∧ y=4032*q+1994 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p5 (q x y : Nat)
  (h : BB429.next (x,y)=some (32*q+13,4032*q+1994)) :
  (x=16*q+5 ∧ y=4064*q+2007) ∨
  (x=1040*q+505 ∧ y=2016*q+999) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p6 (q x y : Nat)
  (h : BB429.next (x,y)=some (16*q+5,4064*q+2007)) :
  x=8*q+1 ∧ y=4080*q+2012 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p7 (q x y : Nat) (hq : 1≤q)
  (h : BB429.next (x,y)=some (8*q+1,4080*q+2012)) :
  x=4*q-1 ∧ y=4088*q+2013 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p8 (q x y : Nat) (hq : 1≤q)
  (h : BB429.next (x,y)=some (4*q-1,4088*q+2013)) :
  x=2*q-2 ∧ y=4092*q+2012 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem no_reach_zero_6104 (n : Nat) :
  BB429.run n (0,0) ≠ some (0,6104) := by
  intro h
  by_cases hn : n<1308
  · have hfin : ∀ i : Fin 1308, BB429.run i.val (0,0) ≠ some (0,6104) := by decide
    exact hfin ⟨n,hn⟩ h
  · have h1308 : BB429.run 1308 (0,0)=some (213,5681) := by decide
    have hc : BB429.run n (0,0)=BB429.run (n-1308) (213,5681) := by
      calc
        BB429.run n (0,0)=BB429.run (1308+(n-1308)) (0,0) := by congr 1; omega
        _ = BB429.run (n-1308) (213,5681) := by
          rw [BB429.run_add,h1308]
          rfl
    rw [hc] at h
    have hr := (BB429.run_rank_bounds (213,5681) (0,6104) (n-1308) h).1
    simp only [BB429.rank] at hr
    omega

/-- Uniform genuine blank-root exclusion of a third strict subfamily of
    Agent6's surviving 125 modulo128 terminal sector. -/
theorem blank_halt_not_509_mod1024 (n q : Nat)
  (hr : BB429.run n (0,0)=some (1024*q+509,2048*q+1017)) : False := by
  have a0 : Reach (1024*q+509) (2048*q+1017) := ⟨n,hr⟩
  have a1 : Reach (512*q+253) (3072*q+1526) :=
    unique_parent _ _ _ _ (by omega) a0 (fun x y hs => p0 q x y hs)
  have a2 : Reach (256*q+125) (3584*q+1779) ∨
            Reach (1280*q+628) (1536*q+765) :=
    two_parents _ _ _ _ _ _ (by omega) a1 (fun x y hs => p1 q x y hs)
  rcases a2 with a2 | a2
  · have a3 : Reach (128*q+61) (3840*q+1904) :=
      unique_parent _ _ _ _ (by omega) a2 (fun x y hs => p2 q x y hs)
    have a4 : Reach (64*q+29) (3968*q+1965) :=
      unique_parent _ _ _ _ (by omega) a3 (fun x y hs => p3 q x y hs)
    have a5 : Reach (32*q+13) (4032*q+1994) :=
      unique_parent _ _ _ _ (by omega) a4 (fun x y hs => p4 q x y hs)
    have a6 : Reach (16*q+5) (4064*q+2007) ∨
              Reach (1040*q+505) (2016*q+999) :=
      two_parents _ _ _ _ _ _ (by omega) a5 (fun x y hs => p5 q x y hs)
    rcases a6 with a6 | a6
    · have a7 : Reach (8*q+1) (4080*q+2012) :=
        unique_parent _ _ _ _ (by omega) a6 (fun x y hs => p6 q x y hs)
      cases q with
      | zero =>
        obtain ⟨k,hk⟩ := a7
        exact (BB429LowOddMod8.root_ne_one k 2012) (by simpa using hk)
      | succ q =>
        have a8 : Reach (4*(q+1)-1) (4088*(q+1)+2013) :=
          unique_parent _ _ _ _ (by omega) a7
            (fun x y hs => p7 (q+1) x y (by omega) hs)
        cases q with
        | zero =>
          have a9 : Reach 0 6104 := by
            have a9' : Reach (2*1-2) (4092*1+2012) :=
              unique_parent _ _ _ _ (by omega) a8
                (fun x y hs => p8 1 x y (by omega) hs)
            simpa using a9'
          obtain ⟨k,hk⟩ := a9
          exact (no_reach_zero_6104 k) hk
        | succ q =>
          have a9 : Reach (2*(q+2)-2) (4092*(q+2)+2012) :=
            unique_parent _ _ _ _ (by omega) a8
              (fun x y hs => p8 (q+2) x y (by omega) hs)
          obtain ⟨k,hk⟩ := a9
          have hm := BB429NoThree.reachable_even_positive k
            (2*(q+2)-2) (4092*(q+2)+2012) hk (by omega) (by omega)
          omega
    · obtain ⟨k,hk⟩ := a6
      have hm := BB429Mod8.all_blank_returns_allowed k
        (1040*q+505) (2016*q+999) hk
      unfold BB429Mod8.Allowed at hm
      omega
  · obtain ⟨k,hk⟩ := a2
    have hm := BB429NoThree.reachable_even_positive k
      (1280*q+628) (1536*q+765) hk (by omega) (by omega)
    omega

theorem blank_halt_mod1024_ne_509 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%1024 ≠ 509 := by
  intro hm
  let q := a/1024
  have ha : a=1024*q+509 := by dsimp [q]; omega
  have hb : b=2048*q+1017 := by omega
  exact blank_halt_not_509_mod1024 n q (by simpa [ha,hb] using hr)

#print axioms p0
#print axioms p1
#print axioms p5
#print axioms blank_halt_not_509_mod1024
#print axioms blank_halt_mod1024_ne_509
end BB429No509
