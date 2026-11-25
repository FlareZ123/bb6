import WeightedTNFCertificate
import SourceFiniteSemantics

namespace BB6.Agent50TranslatedCycler

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent32FiniteSource

/-- Equality of the first k cells on the left, with missing cells blank. -/
def LeftEq (k : Nat) (xs ys : List Bool) : Prop :=
  ∀ i, i < k → xs[i]?.getD false = ys[i]?.getD false

/-- Equality of the entire right-hand blank-padded side. -/
def SideEq (xs ys : List Bool) : Prop :=
  ∀ i, xs[i]?.getD false = ys[i]?.getD false

/-- Coq TranslatedCyclers.EqLimit, in the finite blank-padded tape model.
The left side is compared only for k cells; the current cell and entire
right side are compared exactly. -/
structure EqLimit (k : Nat) (c d : FiniteCfg) : Prop where
  state_eq : c.state = d.state
  left_eq : LeftEq k c.left d.left
  current_eq : c.cur = d.cur
  right_eq : SideEq c.right d.right

theorem LeftEq_refl (k : Nat) (xs : List Bool) : LeftEq k xs xs := by
  intro i hi
  rfl

theorem LeftEq_symm {k : Nat} {xs ys : List Bool}
    (h : LeftEq k xs ys) : LeftEq k ys xs := by
  intro i hi
  exact (h i hi).symm

theorem LeftEq_trans {k : Nat} {xs ys zs : List Bool}
    (h₁ : LeftEq k xs ys) (h₂ : LeftEq k ys zs) : LeftEq k xs zs := by
  intro i hi
  exact (h₁ i hi).trans (h₂ i hi)

theorem SideEq_refl (xs : List Bool) : SideEq xs xs := by
  intro i
  rfl

theorem SideEq_symm {xs ys : List Bool} (h : SideEq xs ys) : SideEq ys xs := by
  intro i
  exact (h i).symm

theorem SideEq_trans {xs ys zs : List Bool}
    (h₁ : SideEq xs ys) (h₂ : SideEq ys zs) : SideEq xs zs := by
  intro i
  exact (h₁ i).trans (h₂ i)

theorem LeftEq_head {k : Nat} {xs ys : List Bool}
    (h : LeftEq (k+1) xs ys) :
    xs.headD false = ys.headD false := by
  have h0 := h 0 (by omega)
  simpa [get_head] using h0

theorem LeftEq_tail {k : Nat} {xs ys : List Bool}
    (h : LeftEq (k+1) xs ys) :
    LeftEq k xs.tail ys.tail := by
  intro i hi
  have h' := h (i+1) (by omega)
  simpa [get_tail] using h'

theorem LeftEq_cons {k : Nat} {xs ys : List Bool} {a b : Bool}
    (hab : a = b) (h : LeftEq k xs ys) :
    LeftEq (k+1) (a::xs) (b::ys) := by
  intro i hi
  cases i with
  | zero => simp [hab]
  | succ i => exact h i (by omega)

theorem SideEq_head {xs ys : List Bool} (h : SideEq xs ys) :
    xs.headD false = ys.headD false := by
  simpa [get_head] using h 0

theorem SideEq_tail {xs ys : List Bool} (h : SideEq xs ys) :
    SideEq xs.tail ys.tail := by
  intro i
  have h' := h (i+1)
  simpa [get_tail] using h'

theorem SideEq_cons {xs ys : List Bool} {a b : Bool}
    (hab : a = b) (h : SideEq xs ys) :
    SideEq (a::xs) (b::ys) := by
  intro i
  cases i with
  | zero => simp [hab]
  | succ i => exact h i

theorem EqLimit_refl (k : Nat) (c : FiniteCfg) : EqLimit k c c :=
  ⟨rfl, LeftEq_refl k c.left, rfl, SideEq_refl c.right⟩

theorem EqLimit_symm {k : Nat} {c d : FiniteCfg}
    (h : EqLimit k c d) : EqLimit k d c :=
  ⟨h.state_eq.symm, LeftEq_symm h.left_eq, h.current_eq.symm,
    SideEq_symm h.right_eq⟩

theorem EqLimit_trans {k : Nat} {c d e : FiniteCfg}
    (h₁ : EqLimit k c d) (h₂ : EqLimit k d e) : EqLimit k c e :=
  ⟨h₁.state_eq.trans h₂.state_eq,
    LeftEq_trans h₁.left_eq h₂.left_eq,
    h₁.current_eq.trans h₂.current_eq,
    SideEq_trans h₁.right_eq h₂.right_eq⟩

theorem EqLimit_less {k k' : Nat} {c d : FiniteCfg}
    (hbudget : k ≤ k') (h : EqLimit k' c d) : EqLimit k c d :=
  ⟨h.state_eq,
    (fun i hi => h.left_eq i (Nat.lt_of_lt_of_le hi hbudget)),
    h.current_eq, h.right_eq⟩

/-- A bounded step is exactly a BusyCoq lstep: left consumes one unit
of budget, right adds one. -/
inductive BStep (m : Machine) : Nat → FiniteCfg → Nat → FiniteCfg → Prop where
  | left {k : Nat} {c : FiniteCfg} {mv : Move}
      (hm : m (query c) = some mv) (hr : mv.right = false) :
      BStep m (k+1) c k (move c mv)
  | right {k : Nat} {c : FiniteCfg} {mv : Move}
      (hm : m (query c) = some mv) (hr : mv.right = true) :
      BStep m k c (k+1) (move c mv)

theorem BStep_replay {m : Machine} {k k' : Nat}
    {c c' d : FiniteCfg}
    (hstep : BStep m k c k' c') (heq : EqLimit k c d) :
    ∃ d', BStep m k d k' d' ∧ EqLimit k' c' d' := by
  cases hstep with
  | @left k c mv hm hr =>
      have hquery : query c = query d := by
        cases c with
        | mk l r cur st =>
          cases d with
          | mk l' r' cur' st' =>
            exact ⟨heq.state_eq, heq.current_eq⟩
      have hm' : m (query d) = some mv := by
        simpa [← hquery] using hm
      refine ⟨move d mv, BStep.left hm' hr, ?_⟩
      refine ⟨by simp [move, hr], ?_, ?_, ?_⟩
      · simpa [move, hr] using LeftEq_tail heq.left_eq
      · simpa [move, hr] using LeftEq_head heq.left_eq
      · simpa [move, hr] using SideEq_cons rfl heq.right_eq
  | @right k c mv hm hr =>
      have hquery : query c = query d := by
        cases c with
        | mk l r cur st =>
          cases d with
          | mk l' r' cur' st' =>
            exact ⟨heq.state_eq, heq.current_eq⟩
      have hm' : m (query d) = some mv := by
        simpa [← hquery] using hm
      refine ⟨move d mv, BStep.right hm' hr, ?_⟩
      refine ⟨by simp [move, hr], ?_, ?_, ?_⟩
      · simpa [move, hr] using LeftEq_cons rfl heq.left_eq
      · simpa [move, hr] using SideEq_head heq.right_eq
      · simpa [move, hr] using SideEq_tail heq.right_eq

/-- A finite sequence of bounded steps, with the same indexing convention
as BusyCoq's lmultistep. -/
inductive BRun (m : Machine) : Nat → Nat → FiniteCfg → Nat → FiniteCfg → Prop where
  | zero (k : Nat) (c : FiniteCfg) : BRun m 0 k c k c
  | succ {n k k₁ k₂ : Nat} {c c₁ c₂ : FiniteCfg}
      (hstep : BStep m k c k₁ c₁)
      (hrest : BRun m n k₁ c₁ k₂ c₂) :
      BRun m (n+1) k c k₂ c₂

theorem BRun_replay {m : Machine} {n k k' : Nat}
    {c c' d : FiniteCfg}
    (hRun : BRun m n k c k' c') (heq : EqLimit k c d) :
    ∃ k'' d', BRun m n k d k'' d' ∧ EqLimit k' c' d' := by
  induction hRun generalizing d with
  | zero =>
      exact ⟨k,d,BRun.zero k d,heq⟩
  | succ hstep hrest ih =>
      obtain ⟨d₁,hstep',heq₁⟩ := BStep_replay hstep heq
      obtain ⟨k₂,d₂,hrest',heq₂⟩ := ih d₁ heq₁
      exact ⟨k₂,d₂,BRun.succ hstep' hrest',heq₂⟩

theorem BRun_finiteRun {m : Machine} {n k k' : Nat}
    {c d : FiniteCfg}
    (h : BRun m n k c k' d) :
    finiteRun m n c = some d := by
  induction h with
  | zero => rfl
  | succ hstep hrest ih =>
      cases hstep with
      | left hm hr => simp [finiteRun, step, hm, ih]
      | right hm hr => simp [finiteRun, step, hm, ih]

/-- A successful boundedRun computation is a kernel-checkable BRun proof. -/
def boundedStep (m : Machine) (k : Nat) (c : FiniteCfg) :
    Option (Nat × FiniteCfg) :=
  match m (query c) with
  | none => none
  | some mv =>
      if mv.right then some (k+1, move c mv)
      else match k with
        | 0 => none
        | k+1 => some (k, move c mv)

def boundedRun (m : Machine) : Nat → Nat → FiniteCfg →
    Option (Nat × FiniteCfg)
  | 0, k, c => some (k,c)
  | n+1, k, c =>
      (boundedStep m k c).bind (fun (k',c') => boundedRun m n k' c')

theorem boundedStep_sound {m : Machine} {k : Nat} {c : FiniteCfg}
    {k' : Nat} {d : FiniteCfg}
    (h : boundedStep m k c = some (k',d)) :
    BStep m k c k' d := by
  unfold boundedStep at h
  cases hm : m (query c) with
  | none => simp [hm] at h
  | some mv =>
      cases hv : mv.right with
      | true =>
          have hp : (k+1,move c mv) = (k',d) := by
            simpa [hm,hv] using h
          cases hp
          exact BStep.right hm hv
      | false =>
          cases k with
          | zero => simp [hm,hv] at h
          | succ k =>
              have hp : (k,move c mv) = (k',d) := by
                simpa [hm,hv] using h
              cases hp
              exact BStep.left hm hv

theorem boundedRun_sound {m : Machine} {n k k' : Nat} {c d : FiniteCfg}
    (h : boundedRun m n k c = some (k',d)) :
    BRun m n k c k' d := by
  induction n generalizing k c k' d with
  | zero =>
      have hp : (k,c) = (k',d) := by
        simpa [boundedRun] using h
      cases hp
      exact BRun.zero k c
  | succ n ih =>
      simp only [boundedRun] at h
      cases hs : boundedStep m k c with
      | none => simp [hs] at h
      | some z =>
          rcases z with ⟨k₁,c₁⟩
          simp [hs] at h
          have hstep : BStep m k c k₁ c₁ := boundedStep_sound hs
          exact BRun.succ hstep (ih h)

theorem finiteRun_append (m : Machine) (c : FiniteCfg) (a b : Nat) :
    finiteRun m (a+b) c =
      (finiteRun m a c).bind (finiteRun m b) := by
  induction a generalizing c with
  | zero => simp [finiteRun]
  | succ a ih =>
      simp only [Nat.succ_add, finiteRun]
      have ih' : finiteRun m (a+b) =
          fun c' => (finiteRun m a c').bind (finiteRun m b) := by
        funext c'
        exact ih c'
      rw [ih']
      simp [Option.bind_assoc]

theorem finiteRun_none_add (m : Machine) (c : FiniteCfg) (n k : Nat)
    (h : finiteRun m n c = none) :
    finiteRun m (n+k) c = none := by
  rw [finiteRun_append]
  simp [h]

/-- The translated-cycle hypothesis used by BusyCoq's verify_tcycler:
a positive bounded period, nondecreasing budget, same control state, and
EqLimit on the tape. -/
structure TranslatedCycle (m : Machine) (period budget : Nat)
    (c : FiniteCfg) : Type where
  endBudget : Nat
  endConfig : FiniteCfg
  run : BRun m period budget c endBudget endConfig
  budget_mono : budget ≤ endBudget
  tape_eq : EqLimit budget c endConfig

theorem TranslatedCycle.repeat {m : Machine} {period budget : Nat}
    {c : FiniteCfg} (h : TranslatedCycle m period budget c) :
    ∀ r, ∃ d, finiteRun m (period*r) c = some d ∧ EqLimit budget c d := by
  intro r
  induction r with
  | zero =>
      exact ⟨c,rfl,EqLimit_refl budget c⟩
  | succ r ih =>
      obtain ⟨d,hrun,heqd⟩ := ih
      obtain ⟨k₂,d₂,hrep,heq₂⟩ := BRun_replay h.run heqd
      have hperiod : finiteRun m period d = some d₂ := BRun_finiteRun hrep
      have heq' : EqLimit budget c d₂ :=
        EqLimit_trans h.tape_eq (EqLimit_less h.budget_mono heq₂)
      have hcombined := finiteRun_append m c (period*r) period
      simp [hrun,hperiod] at hcombined
      have hindex : period*r + period = period*(r+1) := by
        rw [Nat.mul_succ]
      refine ⟨d₂, ?_, heq'⟩
      rw [← hindex]
      exact hcombined

theorem TranslatedCycle.neverFrom {m : Machine} {period budget : Nat}
    {c : FiniteCfg} (hperiod : 0 < period)
    (h : TranslatedCycle m period budget c) :
    ∀ n, ∃ d, finiteRun m n c = some d := by
  intro n
  obtain ⟨d,hrun,_⟩ := h.repeat n
  cases hn : finiteRun m n c with
  | some d₀ => exact ⟨d₀,rfl⟩
  | none =>
    have hp : 1 ≤ period := by omega
    have hmul := Nat.mul_le_mul_right n hp
    have hle : n ≤ period*n := by simpa using hmul
    have hlarge := finiteRun_none_add m c n (period*n-n) hn
    have hindex : n + (period*n-n) = period*n := by omega
    rw [hindex,hrun] at hlarge
    contradiction

/-- A translated cycler reached from the blank start proves every finite
prefix exists. This is the source-side nonhalting leaf consumed by TNF. -/
theorem TranslatedCycle.neverBlank {m : Machine} {entry period budget : Nat}
    {c : FiniteCfg} (hentry : finiteRun m entry finiteBlank = some c)
    (hperiod : 0 < period)
    (h : TranslatedCycle m period budget c) : NeverHalts m := by
  have hfinite : ∀ n, ∃ d, finiteRun m n finiteBlank = some d := by
    intro n
    obtain ⟨d,hrun,_⟩ := h.repeat n
    have hlarge : finiteRun m (entry + period*n) finiteBlank = some d := by
      rw [finiteRun_append,hentry]
      exact hrun
    cases hn : finiteRun m n finiteBlank with
    | some d₀ => exact ⟨d₀,rfl⟩
    | none =>
      have hp : 1 ≤ period := by omega
      have hmul := Nat.mul_le_mul_right n hp
      have hle : n ≤ entry + period*n := by omega
      have hnone' := finiteRun_none_add m finiteBlank n (entry+period*n-n) hn
      have hindex : n + (entry+period*n-n) = entry+period*n := by omega
      rw [hindex,hlarge] at hnone'
      contradiction
  exact (finite_never_iff m).mp hfinite

/-- The finite Boolean checker for the Coq EqLimit predicate. -/
def leftEqB (k : Nat) (xs ys : List Bool) : Bool :=
  (List.range k).all (fun i => decide (xs[i]?.getD false = ys[i]?.getD false))

def sideEqB (xs ys : List Bool) : Bool :=
  (List.range (max xs.length ys.length)).all
    (fun i => decide (xs[i]?.getD false = ys[i]?.getD false))

def eqLimitB (k : Nat) (c d : FiniteCfg) : Bool :=
  decide (c.state = d.state) &&
    (leftEqB k c.left d.left &&
      (decide (c.cur = d.cur) && sideEqB c.right d.right))

theorem allRange_sound {n : Nat} {f : Nat → Bool}
    (h : (List.range n).all f = true) :
    ∀ i, i < n → f i = true := by
  intro i hi
  have hmem : i ∈ List.range n := by simp [hi]
  exact (List.all_eq_true.mp h) i hmem

theorem leftEqB_sound {k : Nat} {xs ys : List Bool}
    (h : leftEqB k xs ys = true) : LeftEq k xs ys := by
  intro i hi
  have h' := allRange_sound h i hi
  exact of_decide_eq_true h'

theorem sideEqB_sound {xs ys : List Bool}
    (h : sideEqB xs ys = true) : SideEq xs ys := by
  unfold SideEq
  intro i
  by_cases hi : i < max xs.length ys.length
  · have h' := allRange_sound h i hi
    exact of_decide_eq_true h'
  · have hnotx : ¬ i < xs.length := by
      intro hx
      exact hi (lt_of_lt_of_le hx (Nat.le_max_left _ _))
    have hnoty : ¬ i < ys.length := by
      intro hy
      exact hi (lt_of_lt_of_le hy (Nat.le_max_right _ _))
    have hxl : xs.length ≤ i := Nat.le_of_not_lt hnotx
    have hyl : ys.length ≤ i := Nat.le_of_not_lt hnoty
    simp [hxl,hyl]

theorem and_true_parts {a b : Bool} (h : a && b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem eqLimitB_sound {k : Nat} {c d : FiniteCfg}
    (h : eqLimitB k c d = true) : EqLimit k c d := by
  unfold eqLimitB at h
  have h₁ := and_true_parts h
  have h₂ := and_true_parts h₁.2
  have h₃ := and_true_parts h₂.2
  exact ⟨of_decide_eq_true h₁.1, leftEqB_sound h₂.1,
    of_decide_eq_true h₃.1, sideEqB_sound h₃.2⟩

/-- Exact finite analogue of TranslatedCyclers.verify_tcycler_r. -/
def translatedCyclerCheckRight (m : Machine)
    (entry period budget : Nat) : Bool :=
  match finiteRun m entry finiteBlank with
  | none => false
  | some c =>
      match boundedRun m period budget c with
      | none => false
      | some (endBudget,endConfig) =>
          decide (0 < period) &&
            (decide (budget ≤ endBudget) && eqLimitB budget c endConfig)

/-- Coq's left-oriented checker is the right-oriented checker after tape
reflection. -/
def translatedCyclerCheck (m : Machine) (right : Bool)
    (entry period budget : Nat) : Bool :=
  if right then translatedCyclerCheckRight m entry period budget
  else translatedCyclerCheckRight (reflectTable m) entry period budget

theorem reflect_never_iff (m : Machine) :
    NeverHalts (reflectTable m) ↔ NeverHalts m := by
  constructor
  · intro h n
    have heq : run (reflectTable m) n blank =
        (run m n blank).map mirrorConfig := by
      simpa only [mirror_blank] using mirror_run m blank n
    cases hr : run m n blank with
    | none =>
        have hn := h n
        simp [heq,hr] at hn
    | some c => simp [heq,hr]
  · intro h n
    have heq : run (reflectTable m) n blank =
        (run m n blank).map mirrorConfig := by
      simpa only [mirror_blank] using mirror_run m blank n
    cases hr : run m n blank with
    | none =>
        have hn := h n
        simp [heq,hr] at hn
    | some c => simp [heq,hr]

theorem translatedCyclerCheckRight_sound {m : Machine}
    {entry period budget : Nat}
    (hcheck : translatedCyclerCheckRight m entry period budget = true) :
    NeverHalts m := by
  unfold translatedCyclerCheckRight at hcheck
  cases hentry : finiteRun m entry finiteBlank with
  | none => simp [hentry] at hcheck
  | some c =>
      cases hcycle : boundedRun m period budget c with
      | none => simp [hentry,hcycle] at hcheck
      | some result =>
          rcases result with ⟨endBudget,endConfig⟩
          have hcheck' :
              decide (0 < period) &&
                (decide (budget ≤ endBudget) && eqLimitB budget c endConfig) = true := by
            simpa [hentry,hcycle] using hcheck
          have h₁ := and_true_parts hcheck'
          have h₂ := and_true_parts h₁.2
          have hp' : 0 < period := of_decide_eq_true h₁.1
          have hbudget' : budget ≤ endBudget := of_decide_eq_true h₂.1
          have heq' : EqLimit budget c endConfig := eqLimitB_sound h₂.2
          have hrun' : BRun m period budget c endBudget endConfig :=
            boundedRun_sound hcycle
          exact TranslatedCycle.neverBlank hentry hp'
            ⟨endBudget,endConfig,hrun',hbudget',heq'⟩

theorem translatedCyclerCheck_sound {m : Machine} {right : Bool}
    {entry period budget : Nat}
    (hcheck : translatedCyclerCheck m right entry period budget = true) :
    NeverHalts m := by
  cases right with
  | true => exact translatedCyclerCheckRight_sound hcheck
  | false =>
      exact (reflect_never_iff m).mp
        (translatedCyclerCheckRight_sound hcheck)

/-- The source TM's undefined rows are exactly unknown sparse rows; its
default completion is the total machine used by the finite checker. -/
def sourcePartial (m : Machine) : PartialMachine :=
  fun s => (m s).map some

theorem sourceDefaultCompletion (m : Machine) :
    weightedTNFDefaultCompletion (sourcePartial m) = m := by
  funext s
  cases h : m s <;> simp [weightedTNFDefaultCompletion,sourcePartial,h]

theorem sourcePartial_noAssignedHalt (m : Machine) :
    weightedTNFNoAssignedHalt (sourcePartial m) := by
  intro s h
  unfold sourcePartial at h
  cases hm : m s <;> simp [hm] at h

/-- Import a checked BusyCoq SWside witness as an actual Lean nonhalting TNF
leaf. No Coq proof term is trusted: the finite run, budget, and tape match are
recomputed by the Lean checker above. -/
def sourceSideLeaf {B : Nat} {p : PartialMachine} {cut : Nat}
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hsupport : TNFSupport p cut)
    (hnohalt : weightedTNFNoAssignedHalt p)
    (m : Machine) (right : Bool) (entry period budget : Nat)
    (hpartial : sourcePartial m = p)
    (hcheck : translatedCyclerCheck m right entry period budget = true) :
    WeightedTNFCertificate B p cut := by
  have hdefault : weightedTNFDefaultCompletion p = m := by
    rw [← hpartial]
    exact sourceDefaultCompletion m
  have hneverDefault : NeverHalts (weightedTNFDefaultCompletion p) := by
    rw [hdefault]
    exact translatedCyclerCheck_sound hcheck
  have hknown : weightedTNFKnownRunForever p := by
    intro n
    have hn : (run (weightedTNFDefaultCompletion p) n blank).isSome = true :=
      hneverDefault n
    rw [← weightedTNFKnownRun_eq_defaultRun p n] at hn
    cases hr : knownRun p n with
    | none => simp [hr] at hn
    | some c => exact ⟨c,rfl⟩
  exact WeightedTNFCertificate.nonhalt hroot hsupport hnohalt
    ((weightedTNFKnownRunForever_iff p).mp hknown)

/-- The concrete BusyCoq SWside table
    1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------. -/
def sampleMachine : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true,true,1⟩
  | 0, true  => some ⟨true,true,3⟩
  | 1, false => some ⟨true,true,2⟩
  | 1, true  => some ⟨true,false,1⟩
  | 2, false => some ⟨false,false,0⟩
  | 2, true  => some ⟨false,false,4⟩
  | 3, false => some ⟨true,false,0⟩
  | 3, true  => some ⟨false,false,1⟩
  | 4, false => none
  | 4, true  => some ⟨true,false,0⟩
  | 5, false => none
  | 5, true  => none
  | _, _ => none

def samplePartial : PartialMachine := sourcePartial sampleMachine

theorem sampleRoot :
    samplePartial initialSlot = some (some ⟨true,true,1⟩) := by
  rfl

theorem sampleSupport : TNFSupport samplePartial 6 := by
  decide

theorem sampleCyclerCheck :
    translatedCyclerCheck sampleMachine false 7 6 0 = true := by
  decide

/-- The imported source-side witness is now a kernel-checked TNF leaf. -/
def sampleSourceLeaf (B : Nat) :
    WeightedTNFCertificate B samplePartial 6 :=
  sourceSideLeaf
    (hroot := sampleRoot)
    (hsupport := sampleSupport)
    (hnohalt := sourcePartial_noAssignedHalt sampleMachine)
    sampleMachine false 7 6 0 rfl sampleCyclerCheck

#print axioms translatedCyclerCheck_sound
#print axioms sampleSourceLeaf

end BB6.Agent50TranslatedCycler
