namespace F197
inductive Q where | A | B | C | D | E | F deriving DecidableEq, Repr
open Q
abbrev Tape := Nat → Bool
def cons (b : Bool) (t : Tape) : Tape
  | 0 => b
  | n+1 => t n
def tail (t : Tape) : Tape := fun n => t (n+1)
def pre (bits : List Bool) (t : Tape) : Tape := bits.foldr cons t
structure Config where
  q : Q
  l : Tape
  r : Tape
-- Physical convention: l excludes current cell, r includes it.
def moveR (q : Q) (b : Bool) (l r : Tape) : Config := ⟨q,cons b l,tail r⟩
def moveL (q : Q) (b : Bool) (l r : Tape) : Config := ⟨q,tail l,cons (l 0) (cons b (tail r))⟩
def step (c : Config) : Option Config :=
  let ⟨q,l,r⟩ := c
  match q,r 0 with
  | A,false => some (moveR B true l r)
  | A,true => some (moveR E false l r)
  | B,false => some (moveR C true l r)
  | B,true => some (moveL E false l r)
  | C,false => some (moveR D false l r)
  | C,true => none
  | D,false => some (moveR E false l r)
  | D,true => some (moveR A false l r)
  | E,false => some (moveL F true l r)
  | E,true => some (moveL B false l r)
  | F,false => some (moveL A true l r)
  | F,true => some (moveL F true l r)
def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)
def d (l r : Tape) : Config := ⟨D,l,r⟩
def other (q : Q) (l r : Tape) : Config := ⟨q,tail l,cons (l 0) r⟩
def blank : Tape := fun _ => false
-- The prefix words are listed in nearest-first order.
theorem start : run 3 ⟨A,blank,blank⟩ = some (d (pre [false,true,true] blank) blank) := rfl
theorem rule_D_0 (l r : Tape) : run 4 (d l (pre [false, true] r)) = some (d (pre [false, true] l) r) := rfl
theorem rule_D_1 (l r : Tape) : run 5 (d l (pre [true, true, true] r)) = some (d (pre [false, true, false] l) r) := rfl
theorem rule_D_2 (l r : Tape) : run 4 (d l (pre [true, false, false, false] r)) = some (d (pre [false, true, true, false] l) r) := rfl
theorem rule_D_3 (l r : Tape) : run 9 (d (pre [false] l) (pre [true, true, false] r)) = some (d (pre [false, true] l) (pre [false, true] r)) := rfl
theorem rule_D_4 (l r : Tape) : run 6 (d l (pre [true, false, true] r)) = some (d (pre [false, true] l) (pre [false] r)) := rfl
theorem rule_D_5 (l r : Tape) : run 6 (d (pre [false] l) (pre [false, false] r)) = some (other B l (pre [false, false, true] r)) := rfl
theorem rule_B_0 (l r : Tape) : run 2 (other B (pre [false] l) (pre [false] r)) = some (d (pre [false, true] l) r) := rfl
theorem rule_B_1 (l r : Tape) : run 2 (other B (pre [true, true] l) r) = some (other B l (pre [false, false] r)) := rfl
theorem rule_B_2 (l r : Tape) : run 2 (other B (pre [true, false] l) r) = some (other F l (pre [true, false] r)) := rfl
theorem rule_F_0 (l r : Tape) : run 1 (other F (pre [true] l) r) = some (other F l (pre [true] r)) := rfl
theorem rule_F_1 (l r : Tape) : run 1 (other F (pre [false] l) r) = some (other A l (pre [true] r)) := rfl
theorem rule_A_0 (l r : Tape) : run 3 (other A (pre [false] l) (pre [true] r)) = some (other B l (pre [false, false] r)) := rfl
theorem rule_A_1 (l r : Tape) : run 4 (other A (pre [true] l) (pre [true] r)) = some (d (pre [false, true] l) r) := rfl
theorem fatal (l r : Tape) : run 4 (d l (pre [true,false,false,true] r)) = none := rfl

/-- Every macro-boundary state has one of these four orientations. -/
inductive Phase where | D | B | F | A deriving DecidableEq, Repr
structure MacroConfig where
  phase : Phase
  l : Tape
  r : Tape
def physical (m : MacroConfig) : Config :=
  match m.phase with
  | .D => d m.l m.r
  | .B => other B m.l m.r
  | .F => other F m.l m.r
  | .A => other A m.l m.r
def valid (m : MacroConfig) : Prop :=
  match m.phase with
  | .D => m.l 0 = false
  | .B => m.r 0 = false
  | .F => True
  | .A => m.r 0 = true
def fatalPrefix (m : MacroConfig) : Prop :=
  m.phase = .D ∧ m.r 0 = true ∧ m.r 1 = false ∧ m.r 2 = false ∧ m.r 3 = true

def macroStep (m : MacroConfig) : Option (Nat × MacroConfig) :=
  let ⟨q,l,r⟩ := m
  match q with
  | .D =>
    if r 0 then
      if r 1 then
        if r 2 then some (5, ⟨.D,pre [false,true,false] l, tail (tail (tail r))⟩)
        else some (9, ⟨.D,pre [false,true] (tail l),pre [false,true] (tail (tail (tail r)))⟩)
      else if r 2 then some (6, ⟨.D,pre [false,true] l,cons false (tail (tail (tail r)))⟩)
      else if r 3 then none
      else some (4, ⟨.D,pre [false,true,true,false] l,tail (tail (tail (tail r)))⟩)
    else if r 1 then some (4, ⟨.D,pre [false,true] l,tail (tail r)⟩)
    else some (6, ⟨.B,tail l,pre [false,false,true] (tail (tail r))⟩)
  | .B =>
    if l 0 then
      if l 1 then some (2, ⟨.B,tail (tail l),pre [false,false] r⟩)
      else some (2, ⟨.F,tail (tail l),pre [true,false] r⟩)
    else some (2, ⟨.D,pre [false,true] (tail l),tail r⟩)
  | .F => if l 0 then some (1, ⟨.F,tail l,cons true r⟩)
          else some (1, ⟨.A,tail l,cons true r⟩)
  | .A => if l 0 then some (4, ⟨.D,pre [false,true] (tail l),tail r⟩)
          else some (3, ⟨.B,tail l,pre [false,false] (tail r)⟩)

theorem decompose (t : Tape) : cons (t 0) (tail t) = t := by
  funext n
  cases n <;> rfl

theorem decompose_bit (t : Tape) (b : Bool) (h : t 0 = b) : cons b (tail t) = t := by
  rw [← h, decompose]

theorem macro_valid {m m' : MacroConfig} {n : Nat} (h : macroStep m = some (n,m')) : valid m' ∧ n > 0 := by
  rcases m with ⟨q,l,r⟩
  cases q with
  | D =>
    cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;> cases h3 : r 3 <;>
      simp [macroStep,h0,h1,h2,h3] at h <;> rcases h with ⟨rfl,rfl⟩ <;> exact ⟨by first | rfl | trivial, by decide⟩
  | B =>
    cases h0 : l 0 <;> cases h1 : l 1 <;> simp [macroStep,h0,h1] at h <;> rcases h with ⟨rfl,rfl⟩ <;> exact ⟨by first | rfl | trivial, by decide⟩
  | F => cases h0 : l 0 <;> simp [macroStep,h0] at h <;> rcases h with ⟨rfl,rfl⟩ <;> exact ⟨by first | rfl | trivial, by decide⟩
  | A => cases h0 : l 0 <;> simp [macroStep,h0] at h <;> rcases h with ⟨rfl,rfl⟩ <;> exact ⟨by first | rfl | trivial, by decide⟩

theorem macro_fatal_iff (m : MacroConfig) : macroStep m = none ↔ fatalPrefix m := by
  rcases m with ⟨q,l,r⟩
  cases q with
  | D => cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;> cases h3 : r 3 <;> simp [macroStep,fatalPrefix,h0,h1,h2,h3]
  | B => cases h0 : l 0 <;> cases h1 : l 1 <;> simp [macroStep,fatalPrefix,h0,h1]
  | F => cases h0 : l 0 <;> simp [macroStep,fatalPrefix,h0]
  | A => cases h0 : l 0 <;> simp [macroStep,fatalPrefix,h0]

@[simp] theorem tail_cons (b : Bool) (t : Tape) : tail (cons b t) = t := rfl

theorem macro_sound {m m' : MacroConfig} {n : Nat} (hv : valid m)
    (h : macroStep m = some (n,m')) : run n (physical m) = some (physical m') := by
  rcases m with ⟨q,l,r⟩
  cases q with
  | D =>
    have hl : l 0 = false := hv
    cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;> cases h3 : r 3 <;>
      simp [macroStep,h0,h1,h2,h3] at h <;> rcases h with ⟨rfl,rfl⟩ <;>
      simp [run,step,moveR,moveL,physical,d,other,tail,cons,pre,h0,h1,h2,h3,hl] <;> try rfl
  | B =>
    have hr : r 0 = false := hv
    cases h0 : l 0 <;> cases h1 : l 1 <;> simp [macroStep,h0,h1] at h <;> rcases h with ⟨rfl,rfl⟩ <;>
      simp [run,step,moveR,moveL,physical,d,other,tail,cons,pre,h0,h1,hr] <;> try rfl
  | F => cases h0 : l 0 <;> simp [macroStep,h0] at h <;> rcases h with ⟨rfl,rfl⟩ <;>
      simp [run,step,moveR,moveL,physical,d,other,tail,cons,pre,h0] <;> try rfl
  | A =>
    have hr : r 0 = true := hv
    cases h0 : l 0 <;> simp [macroStep,h0] at h <;> rcases h with ⟨rfl,rfl⟩ <;>
      simp [run,step,moveR,moveL,physical,d,other,tail,cons,pre,h0,hr] <;> try rfl

theorem macro_fatal_sound {m : MacroConfig} (h : macroStep m = none) : run 4 (physical m) = none := by
  have ⟨hp,h0,h1,h2,h3⟩ := (macro_fatal_iff m).mp h
  rcases m with ⟨q,l,r⟩
  cases hp
  change r 0 = true at h0
  change r 1 = false at h1
  change r 2 = false at h2
  change r 3 = true at h3
  simp [physical,d,run,step,moveR,moveL,cons,tail,h0,h1,h2,h3]

def startMacro : MacroConfig := ⟨.D,pre [false,true,true] blank,blank⟩
def macroRun : Nat → MacroConfig → Option MacroConfig
  | 0,m => some m
  | n+1,m => (macroStep m).bind fun (_,m') => macroRun n m'

theorem run_add (a b : Nat) (c : Config) : run (a+b) c = (run a c).bind (run b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add,run,run]
    cases h : step c with
    | none => rfl
    | some d => exact ih d

theorem macroRun_sound (k : Nat) (m m' : MacroConfig) (hv : valid m)
    (h : macroRun k m = some m') : ∃ n ≥ k, run n (physical m) = some (physical m') := by
  induction k generalizing m m' with
  | zero =>
    have e : m = m' := Option.some.inj h
    exact ⟨0,Nat.le_refl _,by cases e; rfl⟩
  | succ k ih =>
    simp only [macroRun] at h
    cases hs : macroStep m with
    | none => simp [hs] at h
    | some p =>
      rcases p with ⟨n,v⟩
      have hv' := macro_valid hs
      have hh : macroRun k v = some m' := by simpa [hs] using h
      obtain ⟨j,hj,hj'⟩ := ih v m' hv'.1 hh
      refine ⟨n+j,by omega,?_⟩
      rw [run_add, macro_sound hv hs]
      exact hj'

theorem macroRun_halt (k : Nat) (m : MacroConfig) (hv : valid m)
    (h : macroRun k m = none) : ∃ n, run n (physical m) = none := by
  induction k generalizing m with
  | zero => simp [macroRun] at h
  | succ k ih =>
    simp only [macroRun] at h
    cases hs : macroStep m with
    | none => exact ⟨4,macro_fatal_sound hs⟩
    | some p =>
      rcases p with ⟨n,v⟩
      obtain ⟨j,hj⟩ := ih v (macro_valid hs).1 (by simpa [hs] using h)
      exact ⟨n+j,by rw [run_add,macro_sound hv hs]; exact hj⟩

/-- Exact reduction of blank-tape halting to termination of the four-phase system. -/
theorem halt_iff_macro_halt :
    (∃ n, run n ⟨A,blank,blank⟩ = none) ↔ (∃ k, macroRun k startMacro = none) := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    cases hs : macroRun n startMacro with
    | none => rfl
    | some m =>
      obtain ⟨j,hj,hj'⟩ := macroRun_sound n startMacro m (by rfl) hs
      have he : run (3+j) ⟨A,blank,blank⟩ = some (physical m) := by
        rw [run_add,start]; exact hj'
      have hle : n ≤ 3+j := by omega
      have hz : run (3+j) ⟨A,blank,blank⟩ = none := by
        have e : 3+j = n+(3+j-n) := by omega
        rw [e,run_add,hn]; rfl
      rw [he] at hz
      contradiction
  · rintro ⟨k,hk⟩
    obtain ⟨j,hj⟩ := macroRun_halt k startMacro (by rfl) hk
    exact ⟨3+j,by rw [run_add,start]; exact hj⟩
#print axioms halt_iff_macro_halt
end F197
