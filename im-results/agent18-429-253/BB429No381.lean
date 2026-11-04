import BB429Mod8
import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429No381
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
  (h : BB429.next (x,y)=some (1024*q+381,2048*q+761)) :
  x=512*q+189 ∧ y=3072*q+1142 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p1 (q x y : Nat)
  (h : BB429.next (x,y)=some (512*q+189,3072*q+1142)) :
  (x=256*q+93 ∧ y=3584*q+1331) ∨
  (x=1280*q+468 ∧ y=1536*q+573) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p2 (q x y : Nat)
  (h : BB429.next (x,y)=some (256*q+93,3584*q+1331)) :
  x=128*q+45 ∧ y=3840*q+1424 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p3 (q x y : Nat)
  (h : BB429.next (x,y)=some (128*q+45,3840*q+1424)) :
  x=64*q+21 ∧ y=3968*q+1469 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p4 (q x y : Nat)
  (h : BB429.next (x,y)=some (64*q+21,3968*q+1469)) :
  x=32*q+9 ∧ y=4032*q+1490 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p5 (q x y : Nat)
  (h : BB429.next (x,y)=some (32*q+9,4032*q+1490)) :
  (x=16*q+3 ∧ y=4064*q+1499) ∨
  (x=1040*q+375 ∧ y=2016*q+747) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p6F (q x y : Nat)
  (h : BB429.next (x,y)=some (16*q+3,4064*q+1499)) :
  x=8*q ∧ y=4080*q+1502 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p7F (q x y : Nat) (hq : 1≤q)
  (h : BB429.next (x,y)=some (8*q,4080*q+1502)) :
  x=1028*q+372 ∧ y=2040*q+751 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p6E (q x y : Nat) (hq : 1≤q)
  (h : BB429.next (x,y)=some (1040*q+375,2016*q+747)) :
  x=520*q+186 ∧ y=3056*q+1122 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p7E (q x y : Nat) (hq : 1≤q)
  (h : BB429.next (x,y)=some (520*q+186,3056*q+1122)) :
  x=1284*q+463 ∧ y=1528*q+561 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p8E (q x y : Nat) (hq : 1≤q)
  (h : BB429.next (x,y)=some (1284*q+463,1528*q+561)) :
  x=642*q+230 ∧ y=2812*q+1024 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem no_reach_zero_1502 (n : Nat) :
  BB429.run n (0,0) ≠ some (0,1502) := by
  intro h
  by_cases hn : n<351
  · have hfin : ∀ i : Fin 351, BB429.run i.val (0,0) ≠ some (0,1502) := by decide
    exact hfin ⟨n,hn⟩ h
  · have h351 : BB429.run 351 (0,0)=some (21,1723) := by decide
    have hc : BB429.run n (0,0) = BB429.run (n-351) (21,1723) := by
      calc
        BB429.run n (0,0)=BB429.run (351+(n-351)) (0,0) := by congr 1; omega
        _ = BB429.run (n-351) (21,1723) := by
          rw [BB429.run_add,h351]
          rfl
    rw [hc] at h
    have hr := (BB429.run_rank_bounds (21,1723) (0,1502) (n-351) h).1
    simp only [BB429.rank] at hr
    omega

private theorem no_reach_375_747 (n : Nat) :
  BB429.run n (0,0) ≠ some (375,747) := by
  intro h
  by_cases hn : n<351
  · have hfin : ∀ i : Fin 351, BB429.run i.val (0,0) ≠ some (375,747) := by decide
    exact hfin ⟨n,hn⟩ h
  · have h351 : BB429.run 351 (0,0)=some (21,1723) := by decide
    have hc : BB429.run n (0,0) = BB429.run (n-351) (21,1723) := by
      calc
        BB429.run n (0,0)=BB429.run (351+(n-351)) (0,0) := by congr 1; omega
        _ = BB429.run (n-351) (21,1723) := by
          rw [BB429.run_add,h351]
          rfl
    rw [hc] at h
    have hr := (BB429.run_rank_bounds (21,1723) (375,747) (n-351) h).1
    simp only [BB429.rank] at hr
    omega

/-- All blank-root terminal gateways with first counter 381 mod1024 are impossible. -/
theorem blank_halt_not_381_mod1024 (n q : Nat)
  (hr : BB429.run n (0,0)=some (1024*q+381,2048*q+761)) : False := by
  have a0 : Reach (1024*q+381) (2048*q+761) := ⟨n,hr⟩
  have a1 : Reach (512*q+189) (3072*q+1142) :=
    unique_parent _ _ _ _ (by omega) a0 (fun x y hs => p0 q x y hs)
  have a2 : Reach (256*q+93) (3584*q+1331) ∨
            Reach (1280*q+468) (1536*q+573) :=
    two_parents _ _ _ _ _ _ (by omega) a1 (fun x y hs => p1 q x y hs)
  rcases a2 with a2 | a2
  · have a3 : Reach (128*q+45) (3840*q+1424) :=
      unique_parent _ _ _ _ (by omega) a2 (fun x y hs => p2 q x y hs)
    have a4 : Reach (64*q+21) (3968*q+1469) :=
      unique_parent _ _ _ _ (by omega) a3 (fun x y hs => p3 q x y hs)
    have a5 : Reach (32*q+9) (4032*q+1490) :=
      unique_parent _ _ _ _ (by omega) a4 (fun x y hs => p4 q x y hs)
    have a6 : Reach (16*q+3) (4064*q+1499) ∨
              Reach (1040*q+375) (2016*q+747) :=
      two_parents _ _ _ _ _ _ (by omega) a5 (fun x y hs => p5 q x y hs)
    rcases a6 with a6 | a6
    · have a7 : Reach (8*q) (4080*q+1502) :=
        unique_parent _ _ _ _ (by omega) a6 (fun x y hs => p6F q x y hs)
      cases q with
      | zero =>
        obtain ⟨k,hk⟩ := a7
        exact (no_reach_zero_1502 k) (by simpa using hk)
      | succ q =>
        have a8 : Reach (1028*(q+1)+372) (2040*(q+1)+751) :=
          unique_parent _ _ _ _ (by omega) a7
            (fun x y hs => p7F (q+1) x y (by omega) hs)
        obtain ⟨k,hk⟩ := a8
        have hm := BB429NoThree.reachable_even_positive k
          (1028*(q+1)+372) (2040*(q+1)+751) hk (by omega) (by omega)
        omega
    · cases q with
      | zero =>
        have hnum : Reach 375 747 := a6
        obtain ⟨k,hk⟩ := hnum
        exact (no_reach_375_747 k) hk
      | succ q =>
        have a7 : Reach (520*(q+1)+186) (3056*(q+1)+1122) :=
          unique_parent _ _ _ _ (by omega) a6
            (fun x y hs => p6E (q+1) x y (by omega) hs)
        have a8 : Reach (1284*(q+1)+463) (1528*(q+1)+561) :=
          unique_parent _ _ _ _ (by omega) a7
            (fun x y hs => p7E (q+1) x y (by omega) hs)
        have a9 : Reach (642*(q+1)+230) (2812*(q+1)+1024) :=
          unique_parent _ _ _ _ (by omega) a8
            (fun x y hs => p8E (q+1) x y (by omega) hs)
        obtain ⟨k,hk⟩ := a9
        have hm := BB429NoThree.reachable_even_positive k
          (642*(q+1)+230) (2812*(q+1)+1024) hk (by omega) (by omega)
        omega
  · obtain ⟨k,hk⟩ := a2
    have hm := BB429NoThree.reachable_even_positive k
      (1280*q+468) (1536*q+573) hk (by omega) (by omega)
    omega

theorem blank_halt_mod1024_ne_381 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%1024 ≠ 381 := by
  intro hm
  let q := a/1024
  have ha : a=1024*q+381 := by dsimp [q]; omega
  have hb : b=2048*q+761 := by omega
  exact blank_halt_not_381_mod1024 n q (by simpa [ha,hb] using hr)

#print axioms blank_halt_mod1024_ne_381
#print axioms p0
#print axioms p1
#print axioms p5
#print axioms p6E
#print axioms blank_halt_not_381_mod1024
end BB429No381
