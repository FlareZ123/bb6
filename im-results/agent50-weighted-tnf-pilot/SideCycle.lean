import RayFinite
import RootShift
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent50SideCycle
open BB6Coverage

/-- The retained half-line. Cells behind its boundary may differ arbitrarily. -/
def side (right : Bool) (boundary x : Int) : Prop :=
  if right then boundary ≤ x else x ≤ boundary

instance (right : Bool) (boundary x : Int) : Decidable (side right boundary x) := by
  unfold side
  infer_instance

/-- Translation by a nonnegative oriented displacement preserves the retained half-line. -/
theorem side_add (right : Bool) (boundary x δ : Int)
    (hx : side right boundary x) (hδ : side right 0 δ) :
    side right boundary (x+δ) := by
  cases right <;> simp [side] at * <;> omega

/-- Equality modulo translation on the retained half-line only. -/
def TailRel (right : Bool) (boundary δ : Int) (c d : Config) : Prop :=
  c.state = d.state ∧ d.head = c.head + δ ∧
    ∀ x, side right boundary x → d.tape (x+δ) = c.tape x

theorem tailRel_zero (right : Bool) (boundary : Int) (c : Config) :
    TailRel right boundary 0 c c := by
  exact ⟨rfl, by simp, fun x _ => by simp⟩

theorem tailRel_comp (right : Bool) (boundary δ j : Int) (a b c : Config)
    (hδ : side right 0 δ) (hab : TailRel right boundary δ a b)
    (hbc : TailRel right boundary j b c) : TailRel right boundary (δ+j) a c := by
  refine ⟨hab.1.trans hbc.1, ?_, ?_⟩
  · rw [hbc.2.1,hab.2.1]; omega
  · intro x hx
    have heq : x+(δ+j) = (x+δ)+j := by omega
    rw [heq, hbc.2.2 (x+δ) (side_add right boundary x δ hx hδ),hab.2.2 x hx]

theorem tailRel_step (m : Machine) (right : Bool) (boundary δ : Int)
    (c d c' : Config) (hrel : TailRel right boundary δ c d)
    (hhead : side right boundary c.head) (hstep : rawStep m c = some c') :
    ∃ d', rawStep m d = some d' ∧ TailRel right boundary δ c' d' := by
  have hslot : readSlot d = readSlot c := by
    change (d.state,d.tape d.head) = (c.state,c.tape c.head)
    rw [hrel.1,hrel.2.1,hrel.2.2 c.head hhead]
  cases hm : m (readSlot c) with
  | none => simp [rawStep,hm] at hstep
  | some mv =>
    have hc : c' = applyMove c mv := by simpa [rawStep,hm] using hstep.symm
    subst c'
    refine ⟨applyMove d mv, by simp [rawStep,hslot,hm], rfl, ?_, ?_⟩
    · simp only [applyMove,hrel.2.1]; omega
    · intro x hx
      simp only [applyMove,hrel.2.1]
      have heq : (x+δ = c.head+δ) ↔ x = c.head := by omega
      simp [heq,hrel.2.2 x hx]

theorem tailRel_run (m : Machine) (right : Bool) (boundary δ : Int)
    (c d : Config) (hrel : TailRel right boundary δ c d) (n : Nat)
    (hwindow : ∀ j < n, ∀ e, run m j c = some e → side right boundary e.head)
    (c' : Config) (hrun : run m n c = some c') :
    ∃ d', run m n d = some d' ∧ TailRel right boundary δ c' d' := by
  induction n generalizing c' with
  | zero =>
    have he : c = c' := Option.some.inj hrun
    subst c'
    exact ⟨d,rfl,hrel⟩
  | succ n ih =>
    cases hc : run m n c with
    | none => simp [run,hc] at hrun
    | some e =>
      have he : rawStep m e = some c' := by simpa [run,hc] using hrun
      obtain ⟨f,hf,hef⟩ := ih (fun j hj => hwindow j (by omega)) e hc
      obtain ⟨g,hg,hcg⟩ := tailRel_step m right boundary δ e f c' hef
        (hwindow n (by omega) e hc) he
      exact ⟨g,by simp [run,hf,hg],hcg⟩

/-- Every positive-length oriented half-line recurrence yields arbitrarily long
    live executions, even with unbounded accumulation of marks behind it. -/
theorem sideCycle_iter (m : Machine) (right : Bool) (boundary δ : Int)
    (c d : Config) (n : Nat) (hδ : side right 0 δ)
    (hwindow : ∀ j < n, ∀ e, run m j c = some e → side right boundary e.head)
    (hloop : run m n c = some d) (hcycle : TailRel right boundary δ c d) :
    ∀ k, ∃ e, run m (n*k) c = some e ∧ TailRel right boundary (δ*(k:Int)) c e := by
  intro k
  induction k with
  | zero => exact ⟨c,by simp [run],by simpa using tailRel_zero right boundary c⟩
  | succ k ih =>
    obtain ⟨e,he,hce⟩ := ih
    obtain ⟨f,hf,hdf⟩ := tailRel_run m right boundary (δ*(k:Int)) c e hce n hwindow d hloop
    refine ⟨f,?_,?_⟩
    · rw [Nat.mul_succ,run_append,he]; exact hf
    · have hc := tailRel_comp right boundary δ (δ*(k:Int)) c d f hδ hcycle hdf
      have hj : δ*((k+1:Nat):Int) = δ+δ*(k:Int) := by
        rw [Int.natCast_succ,Int.mul_add,Int.mul_one,Int.add_comm]
      rw [hj]
      exact hc

theorem sideCycle_never (m : Machine) (right : Bool) (boundary δ : Int)
    (c d : Config) (entry n : Nat) (hn : 0 < n) (hδ : side right 0 δ)
    (hstart : run m entry blank = some c)
    (hwindow : ∀ j < n, ∀ e, run m j c = some e → side right boundary e.head)
    (hloop : run m n c = some d) (hcycle : TailRel right boundary δ c d) : NeverHalts m := by
  intro t
  obtain ⟨e,he,_⟩ := sideCycle_iter m right boundary δ c d n hδ hwindow hloop hcycle (t+1)
  have hlong : run m (entry+n*(t+1)) blank = some e := by
    rw [run_append,hstart]; exact he
  have hle : t ≤ entry+n*(t+1) := by
    have h := Nat.mul_le_mul_right (t+1) (show 1 ≤ n by omega)
    simp only [Nat.one_mul] at h
    omega
  cases ht : run m t blank with
  | some f => rfl
  | none =>
    have heq : entry+n*(t+1) = t+(entry+n*(t+1)-t) := by omega
    rw [heq,run_append,ht] at hlong
    contradiction

/-- Exact bidirectional support inclusion on the retained half-line. -/
def finiteTailEq (right : Bool) (boundary : Int) (c d : FinRayCfg) : Bool :=
  let δ := d.head-c.head
  decide (c.state = d.state) && decide (side right 0 δ) &&
    c.ones.all (fun x => if side right boundary x then d.ones.contains (x+δ) else true) &&
    d.ones.all (fun y => if side right boundary (y-δ) then c.ones.contains (y-δ) else true)

theorem finiteTailEq_sound (right : Bool) (boundary : Int) (c d : FinRayCfg)
    (h : finiteTailEq right boundary c d = true) :
    side right 0 (d.head-c.head) ∧
      TailRel right boundary (d.head-c.head) (embedFinRay c) (embedFinRay d) := by
  let δ := d.head-c.head
  simp only [finiteTailEq,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hs,hδ⟩,hl⟩,hr⟩
  refine ⟨hδ,hs,?_,?_⟩
  · change d.head = c.head + (d.head-c.head); omega
  · intro x hx
    change d.ones.contains (x+δ) = c.ones.contains x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hy
      have ht := List.all_eq_true.mp hr (x+δ) (List.contains_iff_mem.mp hy)
      have heq : x+δ-(d.head-c.head) = x := by dsimp [δ]; omega
      simpa [heq,hx] using ht
    · intro hy
      have ht := List.all_eq_true.mp hl x (List.contains_iff_mem.mp hy)
      simpa [hx,δ] using ht

/-- A positive-length observed cycle; boundary and direction are untrusted
    witness data. Every consulted head must be within the retained region. -/
def finiteSideCycleCheck (p : PartialMachine) (entry period : Nat)
    (right : Bool) (boundary : Int) : Bool :=
  match finitePartialRun p entry finiteBlank with
  | none => false
  | some c =>
    match finitePartialRun p period c with
    | none => false
    | some d => finiteTailEq right boundary c d &&
      (List.range period).all (fun j =>
        match finitePartialRun p j c with
        | none => false
        | some e => decide (side right boundary e.head))

theorem finiteSideCycleCheck_sound (p : PartialMachine) (entry period : Nat)
    (right : Bool) (boundary : Int) (hn : 0 < period)
    (h : finiteSideCycleCheck p entry period right boundary = true) :
    ∀ m, compatible p m → NeverHalts m := by
  cases hc : finitePartialRun p entry finiteBlank with
  | none => simp [finiteSideCycleCheck,hc] at h
  | some c =>
    cases hd : finitePartialRun p period c with
    | none => simp [finiteSideCycleCheck,hc,hd] at h
    | some d =>
      simp only [finiteSideCycleCheck,hc,hd,Bool.and_eq_true] at h
      obtain ⟨hδ,hrel⟩ := finiteTailEq_sound right boundary c d h.1
      intro m hm
      have hstart := finitePartialRun_sound p m hm finiteBlank c entry hc
      rw [embedFinRay_blank] at hstart
      have hloop := finitePartialRun_sound p m hm c d period hd
      apply sideCycle_never m right boundary (d.head-c.head) (embedFinRay c)
        (embedFinRay d) entry period hn hδ hstart ?_ hloop hrel
      intro j hj e he
      have hflag := List.all_eq_true.mp h.2 j (List.mem_range.mpr hj)
      cases hf : finitePartialRun p j c with
      | none => simp [hf] at hflag
      | some f =>
        have hsource := finitePartialRun_sound p m hm c f j hf
        have heq : e = embedFinRay f := Option.some.inj (he.symm.trans hsource)
        subst e
        change side right boundary f.head
        simpa [hf] using hflag

#print axioms finiteSideCycleCheck_sound
end BB6Coverage.Agent50SideCycle
