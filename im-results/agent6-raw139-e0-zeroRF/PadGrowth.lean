import PartialAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6PadGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6Coverage.Agent10ZipAudit

def EqW (a b : List Bool) : Prop := ∀ i, a.getD i false = b.getD i false
def EqZ (a b : Z0) : Prop := a.q = b.q ∧ EqW a.l b.l ∧ EqW a.r b.r

theorem eqW_tail {a b : List Bool} (h : EqW a b) : EqW a.tail b.tail := by
  intro i
  have hi := h (i+1)
  cases a <;> cases b <;> simpa using hi

theorem eqW_cons {a b : List Bool} {x y : Bool} (hxy : x=y) (h : EqW a b) : EqW (x::a) (y::b) := by
  intro i
  cases i with
  | zero => exact hxy
  | succ i => exact h i

theorem eqW_head {a b : List Bool} (h : EqW a b) : a.headD false = b.headD false := by
  simpa only [List.headD_eq_getD] using h 0

theorem eqZ_refl (a : Z0) : EqZ a a := ⟨rfl,fun _ => rfl,fun _ => rfl⟩
theorem eqZ_symm {a b : Z0} (h : EqZ a b) : EqZ b a := ⟨h.1.symm,fun i => (h.2.1 i).symm,fun i => (h.2.2 i).symm⟩
theorem eqZ_trans {a b c : Z0} (h : EqZ a b) (g : EqZ b c) : EqZ a c := ⟨h.1.trans g.1,fun i => (h.2.1 i).trans (g.2.1 i),fun i => (h.2.2 i).trans (g.2.2 i)⟩
theorem eqZ_move (mv : Move) {a b : Z0} (h : EqZ a b) : EqZ (move0 mv a) (move0 mv b) := by
  unfold move0
  split
  · exact ⟨rfl,eqW_cons (eqW_head h.2.2) (eqW_cons rfl (eqW_tail h.2.1)),eqW_tail h.2.2⟩
  · exact ⟨rfl,eqW_tail h.2.1,eqW_cons rfl h.2.2⟩

theorem step_eq (p : PartialMachine) {a b a' : Z0} (h : EqZ a b) (hr : step0 p a = some a') : ∃ b', step0 p b = some b' ∧ EqZ a' b' := by
  unfold step0 at hr ⊢
  rw [←h.1,←eqW_head h.2.1]
  cases hx : (p (a.q,a.l.headD false)).bind id with
  | none => rw [hx] at hr; contradiction
  | some mv =>
    simp only [hx,Option.map_some,Option.some.injEq] at hr
    subst a'
    exact ⟨move0 mv b,rfl,eqZ_move mv h⟩

theorem run_eq (p : PartialMachine) (n : Nat) {a b a' : Z0} (h : EqZ a b) (hr : run0 p n a = some a') : ∃ b', run0 p n b = some b' ∧ EqZ a' b' := by
  induction n generalizing a b with
  | zero => simp only [run0.eq_1,Option.some.injEq] at hr; subst a'; exact ⟨b,rfl,h⟩
  | succ n ih =>
    rw [run0.eq_2] at hr ⊢
    cases hs : step0 p a with
    | none => rw [hs] at hr; contradiction
    | some t =>
      obtain ⟨u,hu,he⟩ := step_eq p h hs
      rw [hs,Option.bind_some] at hr
      obtain ⟨v,hv,hv'⟩ := ih he hr
      exact ⟨v,by simpa only [hu,Option.bind_some] using hv,hv'⟩

def Reach (p : PartialMachine) (n : Nat) (a b : Z0) : Prop := ∃ t, run0 p n a = some t ∧ EqZ t b

theorem exactRun {p n a b} (h : run0 p n a = some b) : Reach p n a b := ⟨b,h,eqZ_refl b⟩
theorem padRun {p n a b} (h : Reach p n a b) {a' b'} (ha : EqZ a' a) (hb : EqZ b b') : Reach p n a' b' := by
  obtain ⟨t,ht,he⟩ := h
  obtain ⟨u,hu,hu'⟩ := run_eq p n (eqZ_symm ha) ht
  exact ⟨u,hu,eqZ_trans (eqZ_symm hu') (eqZ_trans he hb)⟩
theorem join {p n m a b c} (h : Reach p n a b) (g : Reach p m b c) : Reach p (n+m) a c := by
  obtain ⟨t,ht,he⟩ := h
  obtain ⟨u,hu,hue⟩ := padRun g he (eqZ_refl c)
  exact ⟨u,join0 ht hu,hue⟩

theorem never_of_pad_growth (p : PartialMachine) (family : Nat → Z0) (entry : Nat) (cost : Nat → Nat)
    (first : Reach p entry ⟨0,[],[]⟩ (family 0)) (positive : ∀ k, 0 < cost k)
    (growth : ∀ k, Reach p (cost k) (family k) (family (k+1))) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary (k : Nat) : ∃ t, k ≤ t ∧ Reach p t ⟨0,[],[]⟩ (family k) := by
    induction k with
    | zero => exact ⟨entry,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,ht,hr⟩ := ih
      have hp := positive k
      exact ⟨t+cost k,by omega,join hr (growth k)⟩
  intro n
  obtain ⟨t,ht,u,hr,_⟩ := arbitrary n
  have hz := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    cases he : run m n blank with
    | none =>
      have H' : run m (n+(t-n)) blank = some (embed z) := by rwa [show n+(t-n)=t by omega]
      rw [run_append,he] at H'; contradiction
    | some c => rfl

end BB6.Agent6PadGrowth
