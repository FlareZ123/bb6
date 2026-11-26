import PadGrowth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6TwoSidedGuard
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth

/-- Left excludes the scanned cell; right includes it. A finite tape is padded by zeros. -/
structure Z1 where
  q : Fin 6
  l : List Bool
  r : List Bool
  deriving DecidableEq

def embed1 (z : Z1) : Z0 := ⟨z.q,z.r.headD false::z.l,z.r.tail⟩
def move1 (mv : Move) (z : Z1) : Z1 :=
  if mv.right then ⟨mv.next,mv.write::z.l,z.r.tail⟩
  else ⟨mv.next,z.l.tail,z.l.headD false::mv.write::z.r.tail⟩

def step1 (p : PartialMachine) (z : Z1) : Option Z1 :=
  ((p (z.q,z.r.headD false)).bind id).map (fun mv => move1 mv z)
def run1 (p : PartialMachine) : Nat → Z1 → Option Z1
  | 0,z => some z
  | n+1,z => (step1 p z).bind (run1 p n)

/-- Every guarded read and left pop is inside the supplied finite prefix. -/
def gstep (p : PartialMachine) (z : Z1) : Option Z1 :=
  if z.r.isEmpty then none else
    ((p (z.q,z.r.headD false)).bind id).bind (fun mv =>
      if !mv.right && z.l.isEmpty then none else some (move1 mv z))
def grun (p : PartialMachine) : Nat → Z1 → Option Z1
  | 0,z => some z
  | n+1,z => (gstep p z).bind (grun p n)

def appendBoth (z : Z1) (L R : List Bool) : Z1 := ⟨z.q,z.l++L,z.r++R⟩

theorem gstep_append (p : PartialMachine) {z t : Z1} (L R : List Bool)
    (h : gstep p z = some t) : step1 p (appendBoth z L R) = some (appendBoth t L R) := by
  rcases z with ⟨q,l,r⟩
  cases r with
  | nil => simp [gstep] at h
  | cons a r =>
    simp only [gstep,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.headD_cons] at h
    unfold step1
    change ((p (q,a)).bind id).map (fun mv => move1 mv ⟨q,l++L,a::r++R⟩) = _
    cases hm : (p (q,a)).bind id with
    | none => simp [hm] at h
    | some mv =>
      simp only [hm,Option.bind_some,Option.map_some] at h ⊢
      cases hd : mv.right with
      | true =>
        simp only [hd,Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false,Option.some.injEq] at h
        rw [←h]
        simp [move1,hd,appendBoth,List.cons_append]
      | false =>
        cases l with
        | nil => simp [hd] at h
        | cons b l =>
          simp only [hd,Bool.not_false,Bool.true_and,List.isEmpty_cons,Bool.false_eq_true,ite_false,Option.some.injEq] at h
          rw [←h]
          simp [move1,hd,appendBoth,List.cons_append]

theorem grun_append (p : PartialMachine) (n : Nat) {z t : Z1} (L R : List Bool)
    (h : grun p n z = some t) : run1 p n (appendBoth z L R) = some (appendBoth t L R) := by
  induction n generalizing z t with
  | zero => simp only [grun,Option.some.injEq] at h; subst t; rfl
  | succ n ih =>
    rw [grun] at h
    rw [run1]
    cases hs : gstep p z with
    | none => simp [hs] at h
    | some u =>
      rw [hs,Option.bind_some] at h
      rw [gstep_append p L R hs,Option.bind_some]
      exact ih h

theorem move1_embed (mv : Move) (z : Z1) : EqZ (move0 mv (embed1 z)) (embed1 (move1 mv z)) := by
  rcases z with ⟨q,l,r⟩
  cases hd : mv.right
  · simp only [move0,embed1,move1,hd, Bool.false_eq_true,ite_false,List.tail_cons,List.headD_cons]
    cases l with
    | nil =>
      refine ⟨rfl,?_,fun _ => rfl⟩
      intro i; cases i <;> rfl
    | cons a l => exact eqZ_refl _
  · simp only [move0,embed1,move1,hd,ite_true,List.tail_cons,List.headD_cons]
    exact eqZ_refl _

theorem step1_embed (p : PartialMachine) {z t : Z1} (h : step1 p z = some t) : Reach p 1 (embed1 z) (embed1 t) := by
  unfold step1 at h
  cases hm : (p (z.q,z.r.headD false)).bind id with
  | none => rw [hm] at h; contradiction
  | some mv =>
    simp only [hm,Option.map_some,Option.some.injEq] at h
    subst t
    refine ⟨move0 mv (embed1 z),?_,move1_embed mv z⟩
    rw [run0.eq_2]
    change (((p (z.q,z.r.headD false)).bind id).map (fun mv => move0 mv (embed1 z))).bind (run0 p 0) = _
    rw [hm]; rfl

theorem run1_embed (p : PartialMachine) (n : Nat) {z t : Z1} (h : run1 p n z = some t) : Reach p n (embed1 z) (embed1 t) := by
  induction n generalizing z t with
  | zero => simp only [run1,Option.some.injEq] at h; subst t; exact exactRun rfl
  | succ n ih =>
    rw [run1] at h
    cases hs : step1 p z with
    | none => simp [hs] at h
    | some u =>
      rw [hs,Option.bind_some] at h
      have hh := join (step1_embed p hs) (ih h)
      simpa only [Nat.one_add] using hh

/-- A guarded finite prefix rewrite transports to any finite tails. -/
theorem guarded_rule (p : PartialMachine) (n : Nat) {z t : Z1} (h : grun p n z = some t) (L R : List Bool) :
    Reach p n (embed1 (appendBoth z L R)) (embed1 (appendBoth t L R)) :=
  run1_embed p n (grun_append p n L R h)

#print axioms guarded_rule
end BB6.Agent6TwoSidedGuard
