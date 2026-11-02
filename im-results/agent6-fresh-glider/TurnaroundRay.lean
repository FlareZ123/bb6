import Symmetry
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

variable (m : Machine) (b c : Fin 6) (v : Bool)

/-- Two-step entry followed by an opposite-direction three-step ray macro. -/
def TurnaroundRay : Prop :=
  m (0,false) = some ⟨true,true,b⟩ ∧
  m (b,false) = some ⟨v,false,c⟩ ∧
  m (c,true) = some ⟨false,false,0⟩

private def LeftFresh (cstate : Fin 6) (q : Config) : Prop :=
  q.state = cstate ∧ q.tape q.head = true ∧
    ∀ x, x < q.head → q.tape x = false

private theorem turnaround_entry (h : TurnaroundRay m b c v) :
    ∃ q, run m 2 blank = some q ∧ LeftFresh c q := by
  obtain ⟨ha,hb,_⟩ := h
  let q0 := blank
  let q1 := applyMove q0 ⟨true,true,b⟩
  let q2 := applyMove q1 ⟨v,false,c⟩
  have hread0 : readSlot q0 = (0,false) := rfl
  have hread1 : readSlot q1 = (b,false) := by
    simp [readSlot,q1,q0,applyMove,blank]
  have h0 : rawStep m q0 = some q1 := by
    simp [rawStep,hread0,ha,q1]
  have h1 : rawStep m q1 = some q2 := by
    simp [rawStep,hread1,hb,q2]
  have hrun : run m 2 blank = some q2 := by
    simpa [run,q0] using congrArg (fun x => x.bind (rawStep m)) h0 |>.trans (by simp [h1])
  refine ⟨q2,hrun,?_⟩
  constructor
  · rfl
  constructor
  · simp [q2,q1,q0,applyMove,blank]
  · intro x hx
    have hhead : q2.head=0 := by simp [q2,q1,q0,applyMove,blank]
    have hneq0 : x≠0 := by rw [hhead] at hx; omega
    have hneq1 : x≠1 := by rw [hhead] at hx; omega
    simp [q2,q1,q0,applyMove,blank,hneq0,hneq1]

private theorem turnaround_cycle (q : Config) (h : TurnaroundRay m b c v)
    (hq : LeftFresh c q) :
    ∃ q', run m 3 q = some q' ∧ LeftFresh c q' ∧ q'.head=q.head-1 := by
  obtain ⟨ha,hb,hc⟩ := h
  obtain ⟨hs,hone,hleft⟩ := hq
  let q1 := applyMove q ⟨false,false,0⟩
  let q2 := applyMove q1 ⟨true,true,b⟩
  let q3 := applyMove q2 ⟨v,false,c⟩
  have hhead1 : q1.head=q.head-1 := rfl
  have hhead2 : q2.head=q.head := by dsimp [q2,q1,applyMove]; omega
  have hhead3 : q3.head=q.head-1 := by dsimp [q3,q2,q1,applyMove]; omega
  have h1 : q1.tape q1.head=false := by
    have hneq : q1.head≠q.head := by rw [hhead1]; omega
    change (if q1.head=q.head then false else q.tape q1.head)=false
    rw [if_neg hneq,hhead1]
    exact hleft (q.head-1) (by omega)
  have h2 : q2.tape q2.head=false := by
    change (if q2.head=q1.head then true else if q2.head=q.head then false else q.tape q2.head)=false
    rw [hhead2,hhead1]
    simp <;> omega
  have hr1 : rawStep m q=some q1 := by
    change (m (q.state,q.tape q.head)).map (applyMove q)=some q1
    rw [hs,hone,hc]
    rfl
  have hr2 : rawStep m q1=some q2 := by
    change (m (q1.state,q1.tape q1.head)).map (applyMove q1)=some q2
    rw [h1]
    change (m (0,false)).map (applyMove q1)=some q2
    rw [ha]
    rfl
  have hr3 : rawStep m q2=some q3 := by
    change (m (q2.state,q2.tape q2.head)).map (applyMove q2)=some q3
    rw [h2]
    change (m (b,false)).map (applyMove q2)=some q3
    rw [hb]
    rfl
  have hrun : run m 3 q=some q3 := by simp [run,hr1,hr2,hr3]
  refine ⟨q3,hrun,?_,hhead3⟩
  constructor
  · rfl
  constructor
  · change (if q3.head=q2.head then v else if q3.head=q1.head then true else
      if q3.head=q.head then false else q.tape q3.head)=true
    rw [hhead3,hhead2,hhead1]
    simp <;> omega
  · intro x hx
    have hbound : x<q.head := by rw [hhead3] at hx; omega
    have hn1 : x≠q.head-1 := by rw [hhead3] at hx; omega
    have hn2 : x≠q.head := by omega
    change (if x=q2.head then v else if x=q1.head then true else
      if x=q.head then false else q.tape x)=false
    rw [hhead2,hhead1]
    simp [hn1,hn2,hleft x hbound]

private theorem run_add_turnaround (m : Machine) (q : Config) (n k : Nat) :
    run m (n+k) q = (run m n q).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.add_succ,run,ih]
    cases h : run m n q with
    | none => simp
    | some d => rfl

private theorem prefix_turnaround (m : Machine) (q : Config) (N n : Nat)
    (hn : n≤N) (hN : (run m N q).isSome=true) :
    (run m n q).isSome=true := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k,hk⟩
  cases h : run m n q with
  | some d => simp
  | none =>
    have hm : run m N q=none := by
      rw [hk,run_add_turnaround,h]
      rfl
    simp [hm] at hN

private theorem turnaround_steps (h : TurnaroundRay m b c v) (n : Nat) :
    ∃ q, run m (2+3*n) blank=some q ∧ LeftFresh c q := by
  induction n with
  | zero => simpa using turnaround_entry m b c v h
  | succ n ih =>
    obtain ⟨q,hq,hfresh⟩ := ih
    obtain ⟨q',hthree,hfresh',_⟩ := turnaround_cycle m b c v q h hfresh
    refine ⟨q', ?_, hfresh'⟩
    have htime : 2+3*(n+1)=2+3*n+3 := by omega
    rw [htime,run_add_turnaround,hq]
    exact hthree

/-- Every blank-origin time is defined under this three-slot specification. -/
theorem turnaround_never (h : TurnaroundRay m b c v) : NeverHalts m := by
  intro n
  obtain ⟨q,hq,_⟩ := turnaround_steps m b c v h (n+1)
  apply prefix_turnaround m blank (2+3*(n+1)) n (by omega)
  simp [hq]

def PartialTurnaround (p : PartialMachine) : Prop :=
  p (0,false)=some (some ⟨true,true,b⟩) ∧
  p (b,false)=some (some ⟨v,false,c⟩) ∧
  p (c,true)=some (some ⟨false,false,0⟩)

theorem partial_turnaround_cover (p : PartialMachine) (B : Nat)
    (hp : PartialTurnaround b c v p) : Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply turnaround_never m b c v
  obtain ⟨h0,h1,h2⟩ := hp
  exact ⟨hm _ _ h0,hm _ _ h1,hm _ _ h2⟩

/-- Reflected turnaround family, starting left and then receding right. -/
def PartialLeftTurnaround (p : PartialMachine) : Prop :=
  p (0,false)=some (some ⟨true,false,b⟩) ∧
  p (b,false)=some (some ⟨v,true,c⟩) ∧
  p (c,true)=some (some ⟨false,true,0⟩)

private theorem reflected_turnaround_never (m : Machine)
    (h : NeverHalts (reflectTable m)) : NeverHalts m := by
  intro n
  have hr := mirror_run m blank n
  simp only [mirror_blank] at hr
  cases ht : run m n blank with
  | none =>
    simp only [ht,Option.map_none] at hr
    have hn := h n
    rw [hr] at hn
    simp at hn
  | some q => simp

theorem partial_left_turnaround_cover (p : PartialMachine) (B : Nat)
    (hp : PartialLeftTurnaround b c v p) : Cover (DecidedBelow B) p := by
  apply Cover.leaf
  intro m hm
  left
  apply reflected_turnaround_never m
  apply turnaround_never (reflectTable m) b c v
  obtain ⟨h0,h1,h2⟩ := hp
  have h0' := hm _ _ h0
  have h1' := hm _ _ h1
  have h2' := hm _ _ h2
  simp [TurnaroundRay,reflectTable,reflectMove,h0',h1',h2']

def turnaroundExample : PartialMachine := fun s =>
  if s=(0,false) then some (some ⟨true,true,1⟩)
  else if s=(1,false) then some (some ⟨true,false,2⟩)
  else if s=(2,true) then some (some ⟨false,false,0⟩)
  else none

theorem turnaround_example_cover (B : Nat) :
    Cover (DecidedBelow B) turnaroundExample := by
  exact partial_turnaround_cover (b:=1) (c:=2) (v:=true)
    turnaroundExample B (by simp [PartialTurnaround,turnaroundExample])

#print axioms turnaround_never
#print axioms partial_turnaround_cover
#print axioms partial_left_turnaround_cover
#print axioms turnaround_example_cover
end BB6Coverage
