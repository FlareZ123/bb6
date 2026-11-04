import BB429Mod8
import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429No253
set_option maxHeartbeats 10000000

private def Reach (u w : Nat) : Prop :=
  ∃ n, BB429.run n (0,0) = some (u,w)

private theorem reachable_predecessor (u w : Nat) (hu : 0<u)
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

private theorem unique_reachable_parent (u w x y : Nat)
    (hu : 0<u) (hr : Reach u w)
    (hp : ∀ a b, BB429.next (a,b)=some (u,w) → a=x ∧ b=y) : Reach x y := by
  obtain ⟨n,a,b,ha,hb⟩ := reachable_predecessor u w hu hr
  obtain ⟨rfl,rfl⟩ := hp a b hb
  exact ⟨n,ha⟩

private theorem two_reachable_parents (u w x y x' y' : Nat)
    (hu : 0<u) (hr : Reach u w)
    (hp : ∀ a b, BB429.next (a,b)=some (u,w) →
      (a=x ∧ b=y) ∨ (a=x' ∧ b=y')) :
    Reach x y ∨ Reach x' y' := by
  obtain ⟨n,a,b,ha,hb⟩ := reachable_predecessor u w hu hr
  rcases hp a b hb with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨n,ha⟩
  · exact Or.inr ⟨n,ha⟩

private theorem p_terminal (q x y : Nat)
    (h : BB429.next (x,y)=some (1024*q+253,2048*q+505)) :
    x=512*q+125 ∧ y=3072*q+758 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_one (q x y : Nat)
    (h : BB429.next (x,y)=some (512*q+125,3072*q+758)) :
    (x=256*q+61 ∧ y=3584*q+883) ∨
    (x=1280*q+308 ∧ y=1536*q+381) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_two (q x y : Nat)
    (h : BB429.next (x,y)=some (256*q+61,3584*q+883)) :
    x=128*q+29 ∧ y=3840*q+944 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_three (q x y : Nat)
    (h : BB429.next (x,y)=some (128*q+29,3840*q+944)) :
    x=64*q+13 ∧ y=3968*q+973 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_four (q x y : Nat)
    (h : BB429.next (x,y)=some (64*q+13,3968*q+973)) :
    x=32*q+5 ∧ y=4032*q+986 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_five (q x y : Nat)
    (h : BB429.next (x,y)=some (32*q+5,4032*q+986)) :
    (x=16*q+1 ∧ y=4064*q+991) ∨
    (x=1040*q+245 ∧ y=2016*q+495) := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_six_alt (q x y : Nat)
    (h : BB429.next (x,y)=some (1040*q+245,2016*q+495)) :
    x=520*q+121 ∧ y=3056*q+740 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_seven (q x y : Nat)
    (h : BB429.next (x,y)=some (520*q+121,3056*q+740)) :
    x=260*q+59 ∧ y=3576*q+861 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem p_eight (q x y : Nat)
    (h : BB429.next (x,y)=some (260*q+59,3576*q+861)) :
    x=130*q+28 ∧ y=3836*q+920 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- All finite blank-root returns exclude the terminal congruence class
    u = 1024*q+253 on the exact #429 halting line. -/
theorem blank_halt_not_253_mod1024 (n q : Nat)
    (hr : BB429.run n (0,0)=some (1024*q+253,2048*q+505)) : False := by
  have a0 : Reach (1024*q+253) (2048*q+505) := ⟨n,hr⟩
  have a1 : Reach (512*q+125) (3072*q+758) :=
    unique_reachable_parent _ _ _ _ (by omega) a0 (fun x y hs => p_terminal q x y hs)
  have a2 : Reach (256*q+61) (3584*q+883) ∨
            Reach (1280*q+308) (1536*q+381) :=
    two_reachable_parents _ _ _ _ _ _ (by omega) a1 (fun x y hs => p_one q x y hs)
  rcases a2 with a2 | a2
  · have a3 : Reach (128*q+29) (3840*q+944) :=
      unique_reachable_parent _ _ _ _ (by omega) a2 (fun x y hs => p_two q x y hs)
    have a4 : Reach (64*q+13) (3968*q+973) :=
      unique_reachable_parent _ _ _ _ (by omega) a3 (fun x y hs => p_three q x y hs)
    have a5 : Reach (32*q+5) (4032*q+986) :=
      unique_reachable_parent _ _ _ _ (by omega) a4 (fun x y hs => p_four q x y hs)
    have a6 : Reach (16*q+1) (4064*q+991) ∨
              Reach (1040*q+245) (2016*q+495) :=
      two_reachable_parents _ _ _ _ _ _ (by omega) a5 (fun x y hs => p_five q x y hs)
    rcases a6 with a6 | a6
    · rcases a6 with ⟨k,hk⟩
      have hm := BB429Mod8.all_blank_returns_allowed k (16*q+1) (4064*q+991) hk
      unfold BB429Mod8.Allowed at hm
      omega
    · have a7 : Reach (520*q+121) (3056*q+740) :=
        unique_reachable_parent _ _ _ _ (by omega) a6 (fun x y hs => p_six_alt q x y hs)
      have a8 : Reach (260*q+59) (3576*q+861) :=
        unique_reachable_parent _ _ _ _ (by omega) a7 (fun x y hs => p_seven q x y hs)
      have a9 : Reach (130*q+28) (3836*q+920) :=
        unique_reachable_parent _ _ _ _ (by omega) a8 (fun x y hs => p_eight q x y hs)
      rcases a9 with ⟨k,hk⟩
      have hm := BB429NoThree.reachable_even_positive k (130*q+28) (3836*q+920)
        hk (by omega) (by omega)
      omega
  · rcases a2 with ⟨k,hk⟩
    have hm := BB429NoThree.reachable_even_positive k (1280*q+308) (1536*q+381)
      hk (by omega) (by omega)
    omega

/-- Under the exact rank-compatible source semantics, the remaining
    125 mod128 halting class cannot occupy 253 mod1024. -/
theorem blank_halt_mod1024_ne_253 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%1024 ≠ 253 := by
  intro hmod
  let q := a/1024
  have ha : a=1024*q+253 := by dsimp [q]; omega
  have hb : b=2048*q+505 := by omega
  exact blank_halt_not_253_mod1024 n q (by simpa [ha,hb] using hr)

#print axioms p_terminal
#print axioms p_one
#print axioms p_five
#print axioms blank_halt_not_253_mod1024
#print axioms blank_halt_mod1024_ne_253
end BB429No253
