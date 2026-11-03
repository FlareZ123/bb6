import Lean.Elab.Tactic.Omega

namespace DTripleStandalone
set_option linter.unusedSimpArgs false

structure Cfg where
  l : List Bool
  h : Bool
  r : List Bool
  st : Nat
  deriving Repr

def goL (c : Cfg) (b : Bool) (s : Nat) : Cfg :=
  match c.l with
  | [] => ⟨[], false, b::c.r, s⟩
  | x::xs => ⟨xs, x, b::c.r, s⟩

def goR (c : Cfg) (b : Bool) (s : Nat) : Cfg :=
  match c.r with
  | [] => ⟨b::c.l, false, [], s⟩
  | x::xs => ⟨b::c.l, x, xs, s⟩

def step (c : Cfg) : Cfg :=
  match c.st, c.h with
  | 0, false => goR c true 1
  | 0, true => goR c false 4
  | 1, false => goL c true 2
  | 1, true => goR c false 0
  | 2, false => goL c true 0
  | 2, true => goL c true 3
  | 3, false => goL c true 2
  | 3, true => goL c true 5
  | 4, false => goL c false 2
  | 4, true => goL c false 1
  | 5, false => goL c true 4
  | _, _ => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n+1, c => run n (step c)

theorem run_add (a b : Nat) (c : Cfg) : run (a+b) c = run b (run a c) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add]
    change run (a+b) (step c) = run b (run a (step c))
    exact ih (step c)

def pairs : Nat → List Bool
  | 0 => []
  | n+1 => [true,false] ++ pairs n

def oppairs : Nat → List Bool
  | 0 => []
  | n+1 => [false,true] ++ oppairs n

def scanStart (n : Nat) (L ys : List Bool) : Cfg :=
  ⟨L, false, pairs n ++ ys, 0⟩

theorem scan_step (n : Nat) (L ys : List Bool) :
  run 2 (scanStart (n+1) L ys) = scanStart n ([false,true]++L) ys := by
  simp [scanStart,run,step,goL,goR,pairs]

theorem oppairs_comm_one (n : Nat) :
  oppairs n ++ [false,true] = [false,true] ++ oppairs n := by
  induction n with
  | zero => simp [oppairs]
  | succ n ih =>
    simp only [oppairs, List.append_assoc]
    rw [ih]

theorem scan_run (n : Nat) (L ys : List Bool) :
  run (2*n) (scanStart n L ys) = ⟨oppairs n ++ L,false,ys,0⟩ := by
  induction n generalizing L with
  | zero => simp [scanStart,run,oppairs,pairs]
  | succ n ih =>
    have ht : 2*(n+1) = 2+2*n := by omega
    rw [ht,run_add,scan_step,ih]
    have hstack : oppairs n ++ ([false,true]++L) =
        oppairs (n+1) ++ L := by
      calc
        _ = (oppairs n ++ [false,true])++L := by simp [List.append_assoc]
        _ = ([false,true]++oppairs n)++L := by rw [oppairs_comm_one]
        _ = _ := by simp [oppairs,List.append_assoc]
    exact congrArg (fun z : List Bool => Cfg.mk z false ys 0) hstack

def eTriplePairs (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs m ++ [true,true],false,
    pairs q ++ ([true,true,true] ++ ys),4⟩

theorem eTriplePairs_two (m q : Nat) (ys : List Bool) :
  run 2 (eTriplePairs m q ys) =
    scanStart (q+1) (pairs m ++ [true,true]) ([true,true,true]++ys) := by
  simp [eTriplePairs,scanStart,run,step,goL,goR,pairs]

def bPop (q : Nat) (L ys : List Bool) : Cfg :=
  ⟨oppairs q ++ L,false,ys,1⟩

theorem bPop_step (q : Nat) (L ys : List Bool) :
  run 4 (bPop (q+1) L ys) = bPop q L (false::true::ys) := by
  simp [bPop,oppairs,run,step,goL,goR]

theorem aTriple8 (L ys : List Bool) :
  run 8 (⟨L,false,[true,true,true]++ys,0⟩ : Cfg) =
    ⟨L,false,[false,true,false]++ys,1⟩ := by
  cases L with
  | nil => simp [run,step,goL,goR]
  | cons a L => cases a <;> simp [run,step,goL,goR]

def NoF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → (run t c).st ≠ 5

private theorem append_noF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hc t hsmall
  · have heq : t = a+(t-a) := by omega
    rw [heq, run_add, he]
    exact hd (t-a) (by omega)

private theorem scan_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    have ht : 2*(n+1) = 2+2*n := by omega
    rw [ht]
    apply append_noF (scanStart (n+1) L ys)
      (scanStart n ([false,true]++L) ys) 2 (2*n)
    · intro t hlt
      have hcases : t=0 ∨ t=1 := by omega
      rcases hcases with rfl | rfl
      all_goals simp [scanStart,run,step,goL,goR,pairs]
    · exact scan_step n L ys
    · exact ih ([false,true]++L) ys

private theorem start_noF (m q : Nat) (ys : List Bool) :
    NoF (eTriplePairs m q ys) 2 := by
  intro t ht
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with rfl | rfl
  all_goals simp [eTriplePairs,run,step,goL,goR,pairs]

private theorem aTriple8_noF (L ys : List Bool) :
    NoF (⟨L,false,[true,true,true]++ys,0⟩ : Cfg) 8 := by
  intro t ht
  have hcases :
    t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases L with
    | nil => simp [run,step,goL,goR]
    | cons v L => cases v <;> simp [run,step,goL,goR]

private theorem bPop_four_noF (q : Nat) (L ys : List Bool) :
    NoF (bPop (q+1) L ys) 4 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals simp [bPop,oppairs,run,step,goL,goR]

private theorem bPop_noF (q : Nat) (L ys : List Bool) :
    NoF (bPop q L ys) (4*q) := by
  induction q generalizing ys with
  | zero =>
    intro t ht
    omega
  | succ q ih =>
    have ht : 4*(q+1) = 4+4*q := by omega
    rw [ht]
    exact append_noF (bPop (q+1) L ys)
      (bPop q L (false::true::ys)) 4 (4*q)
      (bPop_four_noF q L ys) (bPop_step q L ys)
      (ih (false::true::ys))

/-- The entire source E(10)^q111 boundary traversal excludes state F,
    including during the scanner, eight-step turn and 4q pair-popping sweep. -/
theorem eTriplePairs_front_noF (m q : Nat) (ys : List Bool) :
    NoF (eTriplePairs m q ys) (6*q+16) := by
  let L := pairs m ++ [true,true]
  let scan : Cfg := scanStart (q+1) L ([true,true,true]++ys)
  let a8 : Cfg := ⟨oppairs (q+1) ++ L,false,[true,true,true]++ys,0⟩
  let pop : Cfg := bPop (q+1) L ([false,true,false]++ys)
  have h1 : run 2 (eTriplePairs m q ys) = scan := by
    simpa [scan,L] using eTriplePairs_two m q ys
  have h2 : run (2*(q+1)) scan = a8 := by
    dsimp [scan,a8]
    rw [scan_run]
  have h3 : run 8 a8 = pop := by
    change run 8 (⟨oppairs (q+1)++L,false,[true,true,true]++ys,0⟩ : Cfg) = _
    rw [aTriple8]
    rfl
  have hf : NoF (eTriplePairs m q ys)
      (2+(2*(q+1)+(8+4*(q+1)))) := by
    apply append_noF (eTriplePairs m q ys) scan
      2 (2*(q+1)+(8+4*(q+1))) (start_noF m q ys) h1
    apply append_noF scan a8 (2*(q+1)) (8+4*(q+1))
      (scan_noF (q+1) L ([true,true,true]++ys)) h2
    exact append_noF a8 pop 8 (4*(q+1))
      (aTriple8_noF (oppairs (q+1)++L) ys) h3
      (bPop_noF (q+1) L ([false,true,false]++ys))
  have hn : 2+(2*(q+1)+(8+4*(q+1)))=6*q+16 := by omega
  simpa only [hn] using hf


#print axioms eTriplePairs_front_noF
end DTripleStandalone
