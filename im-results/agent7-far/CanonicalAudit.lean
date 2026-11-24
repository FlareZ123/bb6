import Canonical
import FrontierMass
namespace BB6Coverage.Canonical

/-- Every child representing a new target stands for the unused labels. -/
def weight (k : Nat) (t : Transition) : Nat :=
  match t with
  | none => 1
  | some mv => if mv.next.val = k then 6-k else 1

theorem weights_sum (k : Nat) (hk : 0<k ∧ k≤6) :
    ((canonChoices k).map (weight k)).sum = 25 := by
  have h : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

inductive Audit (bound : Nat) : PartialMachine → Nat → Type where
  | certified (p : PartialMachine) (k : Nat) (cert : Cover (DecidedBelow bound) p) : Audit bound p k
  | unresolved (p : PartialMachine) (k : Nat) : Audit bound p k
  | branch (p : PartialMachine) (k : Nat) (s : Slot) (fresh : p s = none)
      (scope : Scoped k p) (hs : s.1.val < k) (hk : 0<k ∧ k≤6)
      (kids : ∀ t, t ∈ canonChoices k → Audit bound (refine p s t) (nextK k t)) : Audit bound p k

def Audit.open {bound : Nat} {p : PartialMachine} {k : Nat} (a : Audit bound p k) (m : Machine) : Prop :=
  match a with
  | .certified _ _ _ => False
  | .unresolved _ _ => True
  | .branch _ k s _ _ hs _ kids =>
    let m' := normalize k m s
    (kids (m' s) (normalize_choice k m s hs)).open m'

theorem Audit.exhaustive {bound : Nat} {p : PartialMachine} {k : Nat} (a : Audit bound p k)
    (m : Machine) (hm : compatible p m) : DecidedBelow bound m ∨ a.open m := by
  induction a generalizing m with
  | certified p k cert => exact Or.inl (cert.sound m hm)
  | unresolved p k => exact Or.inr trivial
  | branch p k s fresh scope hs hk kids ih =>
    let m' := normalize k m s
    have hc := normalize_compatible k p m s scope hm
    rcases ih (m' s) (normalize_choice k m s hs) m' (compatible_refine p m' s hc) with h|h
    · exact Or.inl ((normalize_decided_iff k bound m s hk.1).mp h)
    · exact Or.inr h

def addPair (a b : Nat × Nat) : Nat × Nat := (a.1+b.1,a.2+b.2)
def scalePair (w : Nat) (a : Nat × Nat) : Nat × Nat := (w*a.1,w*a.2)

def Audit.report {bound : Nat} {p : PartialMachine} {k : Nat} : Audit bound p k → Nat × Nat
  | .certified p _ _ => (cylinderMass p,0)
  | .unresolved p _ => (0,cylinderMass p)
  | .branch _ k _ _ _ _ _ kids =>
    ((canonChoices k).attach.map (fun t => scalePair (weight k t.val) (kids t.val t.property).report)).foldl addPair (0,0)

private theorem foldPair_sum (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl addPair (a,b)).1 + (xs.foldl addPair (a,b)).2 = a+b+(xs.map (fun x => x.1+x.2)).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    rw [show addPair (a,b) hd = (a+hd.1,b+hd.2) by rfl, ih]
    omega

theorem Audit.conserves {bound : Nat} {p : PartialMachine} {k : Nat} (a : Audit bound p k) :
    a.report.1+a.report.2 = cylinderMass p := by
  induction a with
  | certified p k cert => simp [Audit.report]
  | unresolved p k => simp [Audit.report]
  | branch p k s fresh scope hs hk kids ih =>
    let w := cylinderMass (refine p s none)
    have hchild (t : Transition) : cylinderMass (refine p s t) = w := by
      unfold w cylinderMass
      have a := freeSlotCount_refine p s t fresh
      have b := freeSlotCount_refine p s none fresh
      have heq : freeSlotCount (refine p s t) = freeSlotCount (refine p s none) := by omega
      rw [heq]
    have hsum (xs : List {t : Transition // t ∈ canonChoices k}) :
        ((xs.map (fun x => scalePair (weight k x.val) (kids x.val x.property).report)).map
          (fun x => x.1+x.2)).sum = (xs.map (fun x => weight k x.val)).sum*w := by
      induction xs with
      | nil => simp
      | cons hd tl ihtl =>
        simp only [List.map_cons,List.sum_cons,scalePair]
        simp only [scalePair] at ihtl
        rw [← Nat.mul_add,ih hd.val hd.property,hchild hd.val,ihtl,Nat.add_mul]
    change (((canonChoices k).attach.map _).foldl addPair (0,0)).1 +
      (((canonChoices k).attach.map _).foldl addPair (0,0)).2 = cylinderMass p
    rw [foldPair_sum]
    simp only [Nat.zero_add]
    rw [hsum]
    have he : ((canonChoices k).attach.map (fun x => weight k x.val)).sum = 25 := by
      have h : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [he]
    exact (cylinderMass_refine p s none fresh).symm

theorem weight_positive (k : Nat) (t : Transition) (ht : t ∈ canonChoices k) : 0 < weight k t := by
  cases t with
  | none => simp [weight]
  | some mv =>
    by_cases h : mv.next.val = k
    · have hlt := mv.next.isLt
      simp [weight,h]
      omega
    · simp [weight,h]

private theorem foldPair_snd (xs : List (Nat × Nat)) (a b : Nat) :
    (xs.foldl addPair (a,b)).2 = b+(xs.map Prod.snd).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    rw [show addPair (a,b) hd = (a+hd.1,b+hd.2) by rfl, ih]
    omega

private theorem mem_le_sum (xs : List Nat) (n : Nat) (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with he|ht
    · subst n; simp
    · have hh := ih ht; simp; omega

/-- A zero unresolved mass is a source-level universal closure, not just a count. -/
theorem Audit.closed_of_zero {bound : Nat} {p : PartialMachine} {k : Nat} (a : Audit bound p k)
    (h : a.report.2 = 0) : Cover (DecidedBelow bound) p := by
  induction a with
  | certified p k cert => exact cert
  | unresolved p k =>
    have hp : 0 < cylinderMass p := Nat.pow_pos (by decide)
    simp [Audit.report] at h
    omega
  | branch p k s fresh scope hs hk kids ih =>
    apply cover_branch bound k p s scope hs hk.1
    intro t ht
    apply ih t ht
    have hsnd : (((canonChoices k).attach.map (fun x => scalePair (weight k x.val) (kids x.val x.property).report)).map Prod.snd).sum = 0 := by
      simpa only [Audit.report,foldPair_snd,Nat.zero_add] using h
    have hz : weight k t * (kids t ht).report.2 = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hsnd]
      apply mem_le_sum
      apply List.mem_map.mpr
      refine ⟨scalePair (weight k t) (kids t ht).report,?_,rfl⟩
      apply List.mem_map.mpr
      exact ⟨⟨t,ht⟩,by simp,rfl⟩
    exact (Nat.mul_eq_zero.mp hz).resolve_left (Nat.ne_of_gt (weight_positive k t ht))

#print axioms Audit.closed_of_zero
#print axioms Audit.exhaustive
#print axioms Audit.conserves
end BB6Coverage.Canonical
