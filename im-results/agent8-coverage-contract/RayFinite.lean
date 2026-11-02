import RayEntry
import RayChecker
namespace BB6Coverage

structure FinRayCfg where
  state : Fin 6
  head : Int
  ones : List Int

def finiteTape (c : FinRayCfg) (x : Int) : Bool := c.ones.contains x

def embedFinRay (c : FinRayCfg) : Config :=
  { state := c.state, head := c.head, tape := finiteTape c }

def writeOnes (c : FinRayCfg) (mv : Move) : List Int :=
  if mv.write then c.head :: c.ones else c.ones.filter (· != c.head)

def finiteMove (c : FinRayCfg) (mv : Move) : FinRayCfg :=
  { state := mv.next
    head := c.head + (if mv.right then 1 else -1)
    ones := writeOnes c mv }

/-- Finite-support tape updates exactly agree at every integer position. -/
theorem finiteTape_write (c : FinRayCfg) (mv : Move) (x : Int) :
    finiteTape (finiteMove c mv) x =
      (if x = c.head then mv.write else finiteTape c x) := by
  apply Bool.eq_iff_iff.mpr
  cases hw : mv.write with
  | false =>
    by_cases hx : x = c.head
    · subst x
      simp [finiteTape, finiteMove, writeOnes, hw, List.mem_filter]
    · simp [finiteTape, finiteMove, writeOnes, hw, hx, List.mem_filter]
  | true =>
    by_cases hx : x = c.head
    · subst x
      simp [finiteTape, finiteMove, writeOnes, hw]
    · simp [finiteTape, finiteMove, writeOnes, hw, hx]

theorem embedFinRay_move (c : FinRayCfg) (mv : Move) :
    embedFinRay (finiteMove c mv) = applyMove (embedFinRay c) mv := by
  cases c with
  | mk state head ones =>
    cases mv with
    | mk write right next =>
      simp only [embedFinRay, applyMove, finiteMove, finiteTape]
      apply congrArg (fun tape : Int → Bool =>
        ({state := next, head := head + (if right then 1 else -1), tape := tape} : Config))
      funext x
      exact finiteTape_write ⟨state,head,ones⟩ ⟨write,right,next⟩ x

def finiteStep (m : Machine) (c : FinRayCfg) : Option FinRayCfg :=
  (m (c.state, finiteTape c c.head)).map (finiteMove c)

theorem finiteStep_sound (m : Machine) (c : FinRayCfg) :
    (finiteStep m c).map embedFinRay = rawStep m (embedFinRay c) := by
  simp only [finiteStep, rawStep, embedFinRay, readSlot]
  cases hm : m (c.state, finiteTape c c.head) with
  | none => simp
  | some mv =>
    simp only [Option.map_some]
    exact congrArg some (embedFinRay_move c mv)

/-- A step is defined only when the sparse transition is assigned ordinary. -/
def finitePartialStep (p : PartialMachine) (c : FinRayCfg) : Option FinRayCfg :=
  ((p (c.state, finiteTape c c.head)).bind id).map (finiteMove c)

theorem finitePartialStep_sound (p : PartialMachine) (m : Machine)
    (hm : compatible p m) (c d : FinRayCfg)
    (hs : finitePartialStep p c = some d) :
    rawStep m (embedFinRay c) = some (embedFinRay d) := by
  unfold finitePartialStep at hs
  cases hp : p (c.state, finiteTape c c.head) with
  | none => simp [hp] at hs
  | some t =>
    cases t with
    | none => simp [hp] at hs
    | some mv =>
      have hmove : finiteMove c mv = d := by
        simpa [hp] using hs
      subst d
      have htm : m (c.state, finiteTape c c.head) = some mv :=
        hm (c.state, finiteTape c c.head) (some mv) hp
      change (m (c.state, finiteTape c c.head)).map (applyMove (embedFinRay c)) =
        some (embedFinRay (finiteMove c mv))
      rw [htm]
      exact congrArg some (embedFinRay_move c mv).symm

def finitePartialRun (p : PartialMachine) : Nat → FinRayCfg → Option FinRayCfg
  | 0, c => some c
  | n+1, c => (finitePartialRun p n c).bind (finitePartialStep p)

/-- Every accepted finite run is literally a run of every full completion. -/
theorem finitePartialRun_sound (p : PartialMachine) (m : Machine)
    (hm : compatible p m) (c d : FinRayCfg) (n : Nat)
    (hs : finitePartialRun p n c = some d) :
    run m n (embedFinRay c) = some (embedFinRay d) := by
  induction n generalizing d with
  | zero =>
    simp only [finitePartialRun] at hs
    cases hs
    rfl
  | succ n ih =>
    cases hp : finitePartialRun p n c with
    | none => simp [finitePartialRun, hp] at hs
    | some t =>
      have ht : run m n (embedFinRay c) = some (embedFinRay t) := ih t hp
      have hstep : finitePartialStep p t = some d := by
        simpa only [finitePartialRun, hp, Option.bind_some] using hs
      have hraw := finitePartialStep_sound p m hm t d hstep
      simpa only [run, ht, Option.bind_some] using hraw

def finiteBlank : FinRayCfg :=
  {state := ⟨0,by decide⟩, head := 0, ones := []}

@[simp] theorem embedFinRay_blank : embedFinRay finiteBlank = blank := rfl

def finiteFreshRight (c : FinRayCfg) : Bool :=
  c.ones.all (fun x => decide (x < c.head))

def finiteFreshLeft (c : FinRayCfg) : Bool :=
  c.ones.all (fun x => decide (c.head < x))

theorem finiteFreshRight_sound (c : FinRayCfg)
    (h : finiteFreshRight c = true) : freshRight (embedFinRay c) := by
  intro x hx
  change c.head ≤ x at hx
  have hall : ∀ y, y ∈ c.ones → y < c.head := by
    intro y hy
    have hbool : decide (y < c.head) = true :=
      (List.all_eq_true.mp h) y hy
    simpa using hbool
  have hnot : x ∉ c.ones := by
    intro hm
    have hl := hall x hm
    omega
  change c.ones.contains x = false
  cases hx' : c.ones.contains x with
  | false => rfl
  | true => exact False.elim (hnot (List.contains_iff_mem.mp hx'))

theorem finiteFreshLeft_sound (c : FinRayCfg)
    (h : finiteFreshLeft c = true) : freshLeft (embedFinRay c) := by
  intro x hx
  change x ≤ c.head at hx
  have hall : ∀ y, y ∈ c.ones → c.head < y := by
    intro y hy
    have hbool : decide (c.head < y) = true :=
      (List.all_eq_true.mp h) y hy
    simpa using hbool
  have hnot : x ∉ c.ones := by
    intro hm
    have hl := hall x hm
    omega
  change c.ones.contains x = false
  cases hx' : c.ones.contains x with
  | false => rfl
  | true => exact False.elim (hnot (List.contains_iff_mem.mp hx'))

/-- Unlike the immediate blank-entry checker, this one need not contain A.
    It certifies a closed subgraph entered after an exact finite prefix. -/
def rayTailCheck (p : PartialMachine) (direction : Bool)
    (mask : Fin 6 → Bool) : Bool :=
  (List.finRange 6).all (rayMaskGood p direction mask)

theorem rayTailCheck_closed (p : PartialMachine) (direction : Bool)
    (mask : Fin 6 → Bool) (h : rayTailCheck p direction mask = true) :
    ∀ s, mask s = true → ∃ mv : Move,
      p (s,false) = some (some mv) ∧ mv.right = direction ∧ mask mv.next = true := by
  intro s hs
  have hall : rayMaskGood p direction mask s = true :=
    (List.all_eq_true.mp h) s (List.mem_finRange s)
  simp only [rayMaskGood, hs, ite_true] at hall
  cases hslot : p (s,false) with
  | none => simp [hslot] at hall
  | some outcome =>
    cases outcome with
    | none => simp [hslot] at hall
    | some mv =>
      have hboth : mv.right = direction ∧ mask mv.next = true := by
        simpa [hslot, Bool.and_eq_true] using hall
      exact ⟨mv, rfl, hboth.1, hboth.2⟩

def finiteRayCheck (p : PartialMachine) (n : Nat)
    (direction : Bool) (mask : Fin 6 → Bool) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c =>
    (mask c.state &&
      (if direction then finiteFreshRight c else finiteFreshLeft c)) &&
      rayTailCheck p direction mask

/-- One Boolean check certifies a finite observed prefix + infinite
    pristine-ray tail, for every full completion of the sparse table. -/
theorem finiteRayCheck_sound (p : PartialMachine) (n : Nat)
    (direction : Bool) (mask : Fin 6 → Bool) (bound : Nat)
    (h : finiteRayCheck p n direction mask = true) :
    Cover (DecidedBelow bound) p := by
  cases hentry : finitePartialRun p n finiteBlank with
  | none => simp [finiteRayCheck, hentry] at h
  | some c =>
    have hstate : mask c.state = true := by
      have hboth : (mask c.state &&
        (if direction then finiteFreshRight c else finiteFreshLeft c)) = true ∧
        rayTailCheck p direction mask = true := by
        simpa only [finiteRayCheck, hentry, Bool.and_eq_true] using h
      exact (Bool.and_eq_true _ _).mp hboth.1 |>.1
    have hfree : (if direction then finiteFreshRight c else finiteFreshLeft c) = true := by
      have hpair : (mask c.state &&
        (if direction then finiteFreshRight c else finiteFreshLeft c)) = true :=
        ((Bool.and_eq_true _ _).mp (by simpa only [finiteRayCheck, hentry] using h)).1
      exact ((Bool.and_eq_true _ _).mp hpair).2
    have htail : rayTailCheck p direction mask = true := by
      have hpair : (mask c.state &&
        (if direction then finiteFreshRight c else finiteFreshLeft c)) = true ∧
        rayTailCheck p direction mask = true := by
        simpa only [finiteRayCheck, hentry, Bool.and_eq_true] using h
      exact hpair.2
    apply Cover.leaf
    intro m hm
    left
    have hstart : run m n blank = some (embedFinRay c) := by
      have hsource := finitePartialRun_sound p m hm finiteBlank c n hentry
      simpa only [embedFinRay_blank] using hsource
    have hclose : ∀ s, mask s = true → ∃ mv : Move,
        m (s,false) = some mv ∧ mv.right = direction ∧ mask mv.next = true := by
      intro s hs
      obtain ⟨mv, hp, hd, hn⟩ := rayTailCheck_closed p direction mask htail s hs
      exact ⟨mv, hm (s,false) (some mv) hp, hd, hn⟩
    cases direction with
    | false =>
      exact eventually_fresh_left_never m (fun s => mask s = true) n (embedFinRay c)
        hstart hstate (finiteFreshLeft_sound c hfree) hclose
    | true =>
      exact eventually_fresh_right_never m (fun s => mask s = true) n (embedFinRay c)
        hstart hstate (finiteFreshRight_sound c hfree) hclose

#print axioms finiteRayCheck_sound
#print axioms finiteFreshRight_sound
#print axioms finiteFreshLeft_sound
#print axioms finitePartialRun_sound
#print axioms finiteStep_sound
end BB6Coverage
