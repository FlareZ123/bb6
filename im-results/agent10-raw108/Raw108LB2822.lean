import SweepPumping
namespace BB6.Agent10Raw108LB2822
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def enc : List Nat → List Bool
  | [] => []
  | a::as => List.replicate a true ++ false::enc as

def C (l r : List Nat) (L R : List Bool) : Z0 := ⟨1,false::(enc l++L),enc r++R⟩
def E (r : List Nat) (R : List Bool) : Z0 := ⟨1,[],enc r++R⟩

def Path (a b : Z0) : Prop := ∃ t, run0 table t a = some b

theorem Path.refl (a : Z0) : Path a a := ⟨0,rfl⟩
theorem Path.trans {a b c : Z0} (h : Path a b) (g : Path b c) : Path a c := by
  obtain ⟨n,h⟩ := h
  obtain ⟨k,g⟩ := g
  exact ⟨n+k,join0 h g⟩

def repN (P : List Nat) : Nat → List Nat
  | 0 => []
  | n+1 => P ++ repN P n

theorem repN_snoc (P : List Nat) (n : Nat) : repN P n ++ P = P ++ repN P n := by
  induction n with
  | zero => simp [repN]
  | succ n ih => simp only [repN,List.append_assoc,ih]

theorem repN_add (P : List Nat) (n k : Nat) : repN P (n+k) = repN P n ++ repN P k := by
  induction n with
  | zero => simp [repN]
  | succ n ih =>
    rw [show n+1+k=(n+k)+1 by omega]
    simp only [repN,ih,List.append_assoc]

theorem repN_rotate (A B : List Nat) (n : Nat) : repN (A++B) n ++ A = A ++ repN (B++A) n := by
  induction n with
  | zero => simp [repN]
  | succ n ih => simp only [repN,List.append_assoc,ih]

theorem repN_twos (n : Nat) : repN [2] n = List.replicate n 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repN,ih,List.replicate_succ]

theorem repN_pairs (n : Nat) : repN [2,2] n = List.replicate (2*n) 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega]
    simp only [repN,ih,List.replicate_succ,List.cons_append,List.nil_append]

/-- Repeat a finite certified transfer while retaining arbitrary untouched tails. -/
theorem sweepL' (lp rp I O : List Nat)
    (one : ∀ l r L R, Path (C (lp++I++l) (rp++r) L R) (C (lp++l) (rp++O++r) L R))
    (n : Nat) (l r : List Nat) (L R : List Bool) :
    Path (C (lp++repN I n++l) (rp++r) L R) (C (lp++l) (rp++repN O n++r) L R) := by
  induction n generalizing r with
  | zero => simpa [repN] using Path.refl (C (lp++l) (rp++r) L R)
  | succ n ih =>
    have h1 := one (repN I n++l) r L R
    have h2 := ih (O++r)
    simp only [List.append_assoc] at h1 h2
    have h := h1.trans h2
    simpa only [repN,List.append_assoc,← List.append_assoc (repN O n) O r,repN_snoc O n] using h

theorem sweepR' (lp rp I O : List Nat)
    (one : ∀ l r L R, Path (C (lp++l) (rp++I++r) L R) (C (lp++O++l) (rp++r) L R))
    (n : Nat) (l r : List Nat) (L R : List Bool) :
    Path (C (lp++l) (rp++repN I n++r) L R) (C (lp++repN O n++l) (rp++r) L R) := by
  induction n generalizing l with
  | zero => simpa [repN] using Path.refl (C (lp++l) (rp++r) L R)
  | succ n ih =>
    have h1 := one l (repN I n++r) L R
    have h2 := ih (O++l)
    simp only [List.append_assoc] at h1 h2
    have h := h1.trans h2
    simpa only [repN,List.append_assoc,← List.append_assoc (repN O n) O l,repN_snoc O n] using h

theorem ltwo_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 9 (C ([2]++l) ([0,0,0]++r) (L) (R)) = some (C (l) ([0,0,0,2]++r) (L) (R)) := by rfl
theorem ltwo (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([2]++l) ([0,0,0]++r) (L) (R)) (C (l) ([0,0,0,2]++r) (L) (R)) := ⟨9,ltwo_run l r L R⟩

theorem llast_run (r : List Nat) (R : List Bool) : run0 table 9 (C ([]) ([0,0,0]++r) ([true,true]) (R)) = some (E ([0,0,0,2]++r) (R)) := by rfl
theorem llast (r : List Nat) (R : List Bool) : Path (C ([]) ([0,0,0]++r) ([true,true]) (R)) (E ([0,0,0,2]++r) (R)) := ⟨9,llast_run r R⟩

theorem lfour_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 47 (C ([4,2,2,2,2]++l) ([0,0,0,2,2,2,2]++r) (L) (R)) = some (C (l) ([0,0,0,2,2,2,2,0,0,2,2,2,2,2]++r) (L) (R)) := by rfl
theorem lfour (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([4,2,2,2,2]++l) ([0,0,0,2,2,2,2]++r) (L) (R)) (C (l) ([0,0,0,2,2,2,2,0,0,2,2,2,2,2]++r) (L) (R)) := ⟨47,lfour_run l r L R⟩

theorem lseven_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 41 (C ([7,2,2,2]++l) ([0,0,0,2,2,2]++r) (L) (R)) = some (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,2,2,2]++r) (L) (R)) := by rfl
theorem lseven (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([7,2,2,2]++l) ([0,0,0,2,2,2]++r) (L) (R)) (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,2,2,2]++r) (L) (R)) := ⟨41,lseven_run l r L R⟩

theorem turn_run (r : List Nat) (R : List Bool) : run0 table 7 (E ([0,0,0,2]++r) (R)) = some (E ([0,2,2]++r) (R)) := by rfl
theorem turn (r : List Nat) (R : List Bool) : Path (E ([0,0,0,2]++r) (R)) (E ([0,2,2]++r) (R)) := ⟨7,turn_run r R⟩

theorem ainit_run (l : List Nat) (L : List Bool) : run0 table 175 (C ([3,1,0,2,2,0,2,2,2,2,2]++l) ([]) (L) ([])) = some (C (l) ([0,0,0,2,2,2,2,0,0,2,2,2,0,1,0]) (L) ([true])) := by rfl
theorem ainit (l : List Nat) (L : List Bool) : Path (C ([3,1,0,2,2,0,2,2,2,2,2]++l) ([]) (L) ([])) (C (l) ([0,0,0,2,2,2,2,0,0,2,2,2,0,1,0]) (L) ([true])) := ⟨175,ainit_run l L⟩

theorem binit_run (l : List Nat) (L : List Bool) : run0 table 80 (C ([3,4,2,2,7,2,2,2]++l) ([]) (L) ([])) = some (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,2,2,0,0,2,0]) (L) ([true,true])) := by rfl
theorem binit (l : List Nat) (L : List Bool) : Path (C ([3,4,2,2,7,2,2,2]++l) ([]) (L) ([])) (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,2,2,0,0,2,0]) (L) ([true,true])) := ⟨80,binit_run l L⟩

theorem cinit_run (l : List Nat) (L : List Bool) : run0 table 88 (C ([7,2,2,2,4,2,2,2,2]++l) ([]) (L) ([false,false,false,false])) = some (C (l) ([0,0,0,2,2,2,2,0,0,2,2,2,2,0,0,0,0,0]) (L) ([true,true,false,false])) := by rfl
theorem cinit (l : List Nat) (L : List Bool) : Path (C ([7,2,2,2,4,2,2,2,2]++l) ([]) (L) ([false,false,false,false])) (C (l) ([0,0,0,2,2,2,2,0,0,2,2,2,2,0,0,0,0,0]) (L) ([true,true,false,false])) := ⟨88,cinit_run l L⟩

theorem dinit_run (l : List Nat) (L : List Bool) : run0 table 51 (C ([3,7,2,2,2]++l) ([]) (L) ([])) = some (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,0]) (L) ([true,true])) := by rfl
theorem dinit (l : List Nat) (L : List Bool) : Path (C ([3,7,2,2,2]++l) ([]) (L) ([])) (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,0]) (L) ([true,true])) := ⟨51,dinit_run l L⟩

theorem fourstart_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 11 (C ([4]++l) ([0,0,0,2,2,2,2]++r) (L) (R)) = some (C (l) ([0,0,0,0,0,2,2,2,2,2]++r) (L) (R)) := by rfl
theorem fourstart (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([4]++l) ([0,0,0,2,2,2,2]++r) (L) (R)) (C (l) ([0,0,0,0,0,2,2,2,2,2]++r) (L) (R)) := ⟨11,fourstart_run l r L R⟩

theorem sevenstart_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 14 (C ([7]++l) ([0,0,0,2,2,2]++r) (L) (R)) = some (C (l) ([0,0,0,0,0,0,0,0,2,2,2,2]++r) (L) (R)) := by rfl
theorem sevenstart (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([7]++l) ([0,0,0,2,2,2]++r) (L) (R)) (C (l) ([0,0,0,0,0,0,0,0,2,2,2,2]++r) (L) (R)) := ⟨14,sevenstart_run l r L R⟩

theorem rpair_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 18 (C ([0]++l) ([0,2,2,2]++r) (L) (R)) = some (C ([0,2,2]++l) ([0,2]++r) (L) (R)) := by rfl
theorem rpair (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([0]++l) ([0,2,2,2]++r) (L) (R)) (C ([0,2,2]++l) ([0,2]++r) (L) (R)) := ⟨18,rpair_run l r L R⟩

theorem rstart_run (r : List Nat) (R : List Bool) : run0 table 18 (E ([0,2,2,2]++r) (R)) = some (C ([0,2]) ([0,2]++r) ([true,true]) (R)) := by rfl
theorem rstart (r : List Nat) (R : List Bool) : Path (E ([0,2,2,2]++r) (R)) (C ([0,2]) ([0,2]++r) ([true,true]) (R)) := ⟨18,rstart_run r R⟩

theorem revenend_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 11 (C ([0]++l) ([0,2,2,0,0]++r) (L) (R)) = some (C ([0,0,2,2]++l) ([0,0]++r) (L) (R)) := by rfl
theorem revenend (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([0]++l) ([0,2,2,0,0]++r) (L) (R)) (C ([0,0,2,2]++l) ([0,0]++r) (L) (R)) := ⟨11,revenend_run l r L R⟩

theorem roddend_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 10 (C ([0]++l) ([0,2,0,0]++r) (L) (R)) = some (C ([3,2]++l) (r) (L) (R)) := by rfl
theorem roddend (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([0]++l) ([0,2,0,0]++r) (L) (R)) (C ([3,2]++l) (r) (L) (R)) := ⟨10,roddend_run l r L R⟩

theorem qfirst_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 63 (C ([0,0]++l) ([0,0,2,2,2,2,2,0,0]++r) (L) (R)) = some (C ([3,2,2,2,2,4]++l) (r) (L) (R)) := by rfl
theorem qfirst (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([0,0]++l) ([0,0,2,2,2,2,2,0,0]++r) (L) (R)) (C ([3,2,2,2,2,4]++l) (r) (L) (R)) := ⟨63,qfirst_run l r L R⟩

theorem qloop_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 71 (C ([3,2,2,2,2]++l) ([2,2,2,2,2,0,0]++r) (L) (R)) = some (C ([3,2,2,2,2,7,2,2,2]++l) (r) (L) (R)) := by rfl
theorem qloop (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([3,2,2,2,2]++l) ([2,2,2,2,2,0,0]++r) (L) (R)) (C ([3,2,2,2,2,7,2,2,2]++l) (r) (L) (R)) := ⟨71,qloop_run l r L R⟩

theorem aturn_run (l : List Nat) (L : List Bool) : run0 table 75 (C ([3,2,2,2,2]++l) ([2,2,2,0,1,0]) (L) ([true])) = some (C ([7,2,2,2]++l) ([0,0,0,2,2,0,0,0]) (L) ([true])) := by rfl
theorem aturn (l : List Nat) (L : List Bool) : Path (C ([3,2,2,2,2]++l) ([2,2,2,0,1,0]) (L) ([true])) (C ([7,2,2,2]++l) ([0,0,0,2,2,0,0,0]) (L) ([true])) := ⟨75,aturn_run l L⟩

theorem aleft_run (l : List Nat) (L : List Bool) : run0 table 41 (C ([7,2,2,2]++l) ([0,0,0,2,2,0,0,0]) (L) ([true])) = some (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,2,2,0,0,0]) (L) ([true])) := by rfl
theorem aleft (l : List Nat) (L : List Bool) : Path (C ([7,2,2,2]++l) ([0,0,0,2,2,0,0,0]) (L) ([true])) (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,2,2,0,0,0]) (L) ([true])) := ⟨41,aleft_run l L⟩

theorem cend_run (l : List Nat) (L : List Bool) : run0 table 106 (C ([3,2,2,2,2]++l) ([2,2,2,2,0,0,0,0,0]) (L) ([true,true,false,false])) = some (C ([3,7,2,2,2,7,2,2,2]++l) ([]) (L) ([])) := by rfl
theorem cend (l : List Nat) (L : List Bool) : Path (C ([3,2,2,2,2]++l) ([2,2,2,2,0,0,0,0,0]) (L) ([true,true,false,false])) (C ([3,7,2,2,2,7,2,2,2]++l) ([]) (L) ([])) := ⟨106,cend_run l L⟩

theorem pfirst_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 71 (C ([3,2]++l) ([2,2,2,2,0,0,0,0,0]++r) (L) (R)) = some (C ([3,2,2,2,2,7]++l) (r) (L) (R)) := by rfl
theorem pfirst (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([3,2]++l) ([2,2,2,2,0,0,0,0,0]++r) (L) (R)) (C ([3,2,2,2,2,7]++l) (r) (L) (R)) := ⟨71,pfirst_run l r L R⟩

theorem ploop_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 71 (C ([3,2,2,2,2]++l) ([2,2,2,2,0,0,0,0,0]++r) (L) (R)) = some (C ([3,2,2,2,2,7,2,2,2]++l) (r) (L) (R)) := by rfl
theorem ploop (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([3,2,2,2,2]++l) ([2,2,2,2,0,0,0,0,0]++r) (L) (R)) (C ([3,2,2,2,2,7,2,2,2]++l) (r) (L) (R)) := ⟨71,ploop_run l r L R⟩

theorem aend_run (l : List Nat) (L : List Bool) : run0 table 58 (C ([3,2,2,2,2]++l) ([2,2,2,0,0,0]) (L) ([true])) = some (C ([3,4,2,2,7,2,2,2]++l) ([]) (L) ([])) := by rfl
theorem aend (l : List Nat) (L : List Bool) : Path (C ([3,2,2,2,2]++l) ([2,2,2,0,0,0]) (L) ([true])) (C ([3,4,2,2,7,2,2,2]++l) ([]) (L) ([])) := ⟨58,aend_run l L⟩

theorem dturn_run (l : List Nat) (L : List Bool) : run0 table 39 (C ([3,2,2,2,2]++l) ([2,0]) (L) ([true,true])) = some (C ([7,2,2,2]++l) ([0,0,0,0]) (L) ([true])) := by rfl
theorem dturn (l : List Nat) (L : List Bool) : Path (C ([3,2,2,2,2]++l) ([2,0]) (L) ([true,true])) (C ([7,2,2,2]++l) ([0,0,0,0]) (L) ([true])) := ⟨39,dturn_run l L⟩

theorem dleft_run (l : List Nat) (L : List Bool) : run0 table 41 (C ([7,2,2,2]++l) ([0,0,0,0]) (L) ([true])) = some (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,0]) (L) ([true])) := by rfl
theorem dleft (l : List Nat) (L : List Bool) : Path (C ([7,2,2,2]++l) ([0,0,0,0]) (L) ([true])) (C (l) ([0,0,0,2,2,2,0,0,0,0,0,2,0]) (L) ([true])) := ⟨41,dleft_run l L⟩

theorem bdturn_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 10 (C ([3]++l) ([0,0,0,2,2,2,2]++r) (L) (R)) = some (C (l) ([0,0,0,0,2,2,2,2,2]++r) (L) (R)) := by rfl
theorem bdturn (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([3]++l) ([0,0,0,2,2,2,2]++r) (L) (R)) (C (l) ([0,0,0,0,2,2,2,2,2]++r) (L) (R)) := ⟨10,bdturn_run l r L R⟩

theorem pev_run (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : run0 table 155 (C ([0,0,2]++l) ([0,2,2,2,2,2,0,0,0,0,0,2,2,2,2]++r) (L) (R)) = some (C ([0,0,2,2,2,2,2,4]++l) ([0,2,2,2,2,2]++r) (L) (R)) := by rfl
theorem pev (l : List Nat) (r : List Nat) (L : List Bool) (R : List Bool) : Path (C ([0,0,2]++l) ([0,2,2,2,2,2,0,0,0,0,0,2,2,2,2]++r) (L) (R)) (C ([0,0,2,2,2,2,2,4]++l) ([0,2,2,2,2,2]++r) (L) (R)) := ⟨155,pev_run l r L R⟩

theorem bend_run (l : List Nat) (L : List Bool) : run0 table 354 (C ([0,0,2]++l) ([0,2,2,2,2,2,0,0,0,0,0,2,2,2,0,0,2,0]) (L) ([true,true])) = some (C ([7,2,2,2,4,2,2,2,2,4]++l) ([]) (L) ([false,false,false,false])) := by rfl
theorem bend (l : List Nat) (L : List Bool) : Path (C ([0,0,2]++l) ([0,2,2,2,2,2,0,0,0,0,0,2,2,2,0,0,2,0]) (L) ([true,true])) (C ([7,2,2,2,4,2,2,2,2,4]++l) ([]) (L) ([false,false,false,false])) := ⟨354,bend_run l L⟩

theorem dend_run (l : List Nat) (L : List Bool) : run0 table 171 (C ([0,0,2]++l) ([0,2,2,2,2,2,0,0,0,0,0,2,0]) (L) ([true])) = some (C ([3,1,0,2,2,0,2,2,2,2,2,4]++l) ([]) (L) ([])) := by rfl
theorem dend (l : List Nat) (L : List Bool) : Path (C ([0,0,2]++l) ([0,2,2,2,2,2,0,0,0,0,0,2,0]) (L) ([true])) (C ([3,1,0,2,2,0,2,2,2,2,2,4]++l) ([]) (L) ([])) := ⟨171,dend_run l L⟩


abbrev tw (n : Nat) := List.replicate n (2 : Nat)
abbrev tail2 : List Bool := [true,true]

theorem tw_slide (n : Nat) (r : List Nat) : tw n ++ 2::r = 2::(tw n ++ r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,ih]

theorem drainTwos (n : Nat) (r : List Nat) (R : List Bool) :
    Path (C (tw n) ([0,0,0]++r) tail2 R) (E ([0]++tw (n+2)++r) R) := by
  have h1 := sweepL' [] [0,0,0] [2] [2] ltwo n [] r tail2 R
  have h2 := llast (tw n++r) R
  have h3 := turn (tw n++r) R
  simp only [repN_twos,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at h1 h2 h3
  have h := h1.trans (h2.trans h3)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h

theorem scanEven (k : Nat) (r : List Nat) (R : List Bool) :
    Path (E ([0]++tw (2*k+4)++[0,0]++r) R)
      (C ([0,0]++tw (2*k+3)) ([0,0]++r) tail2 R) := by
  have h1 := rstart (tw (2*k+1)++[0,0]++r) R
  have h2 := sweepR' [0] [0,2] [2,2] [2,2] rpair k [2] ([2,0,0]++r) tail2 R
  have h3 := revenend (tw (2*k+1)) r tail2 R
  simp only [repN_pairs,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,tw_slide,List.replicate_succ] at h1 h2 h3
  have h := h1.trans (h2.trans h3)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h

theorem scanOdd (k : Nat) (r : List Nat) (R : List Bool) :
    Path (E ([0]++tw (2*k+3)++[0,0]++r) R)
      (C ([3]++tw (2*k+2)) r tail2 R) := by
  have h1 := rstart (tw (2*k)++[0,0]++r) R
  have h2 := sweepR' [0] [0,2] [2,2] [2,2] rpair k [2] ([0,0]++r) tail2 R
  have h3 := roddend (tw (2*k+1)) r tail2 R
  simp only [repN_pairs,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,tw_slide,List.replicate_succ] at h1 h2 h3
  have h := h1.trans (h2.trans h3)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h


abbrev S : List Nat := [7,2,2,2]
abbrev V : List Nat := [4,2,2,2,2]
abbrev P : List Nat := [0,0,0,0,0,2,2,2,2]
abbrev Q : List Nat := [0,0,2,2,2,2,2]
abbrev U : List Nat := [0,0,2,2,2,2]
abbrev W : List Nat := [0,0,2,2,2]
abbrev X : List Nat := [0,0,0,0,0,2,2,2]
abbrev Y : List Nat := [0,0,0,0,0,2]
abbrev P' : List Nat := [2,2,2,2,0,0,0,0,0]
abbrev Q' : List Nat := [2,2,2,2,2,0,0]
abbrev V' : List Nat := [2,2,2,2,4]
abbrev F : List Nat := [0,0,0,2,2,2,2]
abbrev G : List Nat := [0,0,0,2,2,2]
abbrev I : List Nat := [3,2,2,2,2]
abbrev J : List Nat := [0,2,2,2,2,2]
abbrev Apre : List Nat := [3,1,0,2,2,0,2,2,2,2,2]
abbrev Bpre : List Nat := [3,4,2,2]

theorem qrot (n : Nat) (r : List Nat) :
    repN Q n ++ (0::0::r) = 0::0::(repN Q' n ++ r) := by
  have h := congrArg (fun s => s++r) (repN_rotate [0,0] [2,2,2,2,2] n)
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

theorem prot (n : Nat) (r : List Nat) :
    repN P n ++ (0::0::0::0::0::r) = 0::0::0::0::0::(repN P' n++r) := by
  have h := congrArg (fun s => s++r) (repN_rotate [0,0,0,0,0] [2,2,2,2] n)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

theorem vrot (n : Nat) (r : List Nat) :
    repN V' n ++ ([2,2,2,2]++r) = [2,2,2,2]++(repN V n++r) := by
  have h := congrArg (fun s => s++r) (repN_rotate [2,2,2,2] [4] n)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

theorem fourDrain (n k : Nat) (r : List Nat) (R : List Bool) :
    Path (C (repN V n++[4]++tw k) (F++r) tail2 R)
      (E ([0]++tw (k+2)++Q++repN Q n++r) R) := by
  have h1 := sweepL' [] F V Q lfour n ([4]++tw k) r tail2 R
  have h2 := fourstart (tw k) (repN Q n++r) tail2 R
  have h3 := drainTwos k (Q++repN Q n++r) R
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at h1 h2 h3
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h1.trans (h2.trans h3)

theorem sevenDrain (n k : Nat) (r : List Nat) (R : List Bool) :
    Path (C (repN S n++[7]++tw k) (G++r) tail2 R)
      (E ([0]++tw (k+2)++P++repN P n++r) R) := by
  have h1 := sweepL' [] G S P lseven n ([7]++tw k) r tail2 R
  have h2 := sevenstart (tw k) (repN P n++r) tail2 R
  have h3 := drainTwos k (P++repN P n++r) R
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at h1 h2 h3
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h1.trans (h2.trans h3)

theorem fourstart3_run (l r : List Nat) (L R : List Bool) :
    run0 table 11 (C ([4]++l) (G++r) L R) = some (C l ([0,0,0]++U++r) L R) := by rfl

theorem mixedDrain (n k : Nat) (r : List Nat) (R : List Bool) :
    Path (C (repN S n++[4]++tw k) (G++r) tail2 R)
      (E ([0]++tw (k+2)++U++repN P n++r) R) := by
  have h1 := sweepL' [] G S P lseven n ([4]++tw k) r tail2 R
  have h2 : Path (C ([4]++tw k) (G++repN P n++r) tail2 R)
      (C (tw k) ([0,0,0]++U++repN P n++r) tail2 R) := ⟨11,by simpa only [List.append_assoc] using fourstart3_run (tw k) (repN P n++r) tail2 R⟩
  have h3 := drainTwos k (U++repN P n++r) R
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at h1 h2 h3
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h1.trans (h2.trans h3)

theorem qscan (n k : Nat) (r : List Nat) (R : List Bool) :
    Path (C ([0,0]++tw k) (Q++repN Q n++[0,0]++r) tail2 R)
      (C (I++repN S n++[4]++tw k) r tail2 R) := by
  have h1 := qfirst (tw k) (repN Q' n++r) tail2 R
  have h2 := sweepR' I [] Q' S qloop n ([4]++tw k) r tail2 R
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at h1 h2
  have h := h1.trans h2
  simpa only [List.append_assoc,qrot,List.cons_append,List.nil_append,List.append_nil] using h

theorem pscan (n k : Nat) (r : List Nat) (R : List Bool) :
    Path (C ([3,2]++tw k) ([2,2,2,2]++repN P n++[0,0,0,0,0]++r) tail2 R)
      (C (I++repN S n++[7]++tw k) r tail2 R) := by
  have h1 := pfirst (tw k) (repN P' n++r) tail2 R
  have h2 := sweepR' I [] P' S ploop n ([7]++tw k) r tail2 R
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append] at h1 h2
  have h := h1.trans h2
  simpa only [List.append_assoc,prot,List.cons_append,List.nil_append,List.append_nil] using h

theorem bdDrain (k : Nat) (r : List Nat) (R : List Bool) :
    Path (C ([3]++tw k) ([0,0,0,2,2,2,2]++r) tail2 R)
      (E ([0]++tw (k+2)++J++r) R) := by
  have h1 := bdturn (tw k) r tail2 R
  have h2 := drainTwos k (J++r) R
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h1 h2
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h1.trans h2

theorem pevscan (n : Nat) (l r : List Nat) (R : List Bool) :
    Path (C ([0,0,2]++l) (J++repN P n++r) tail2 R)
      (C ([0,0,2]++repN V' n++l) (J++r) tail2 R) := by
  exact sweepR' [0,0,2] J P V' pev n l r tail2 R


theorem revenAny_run (l r : List Nat) (L R : List Bool) :
    run0 table 11 (C ([0]++l) ([0,2,2]++r) L R) = some (C ([0,0,2,2]++l) r L R) := by rfl

theorem scanEvenAny (k : Nat) (r : List Nat) (R : List Bool) :
    Path (E ([0]++tw (2*k+4)++r) R) (C ([0,0]++tw (2*k+3)) r tail2 R) := by
  have h1 := rstart (tw (2*k+1)++r) R
  have h2 := sweepR' [0] [0,2] [2,2] [2,2] rpair k [2] ([2]++r) tail2 R
  have h3 : Path (C ([0]++tw (2*k+1)) ([0,2,2]++r) tail2 R)
      (C ([0,0,2,2]++tw (2*k+1)) r tail2 R) := ⟨11,revenAny_run _ _ _ _⟩
  simp only [repN_pairs,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,tw_slide,List.replicate_succ] at h1 h2 h3
  have h := h1.trans (h2.trans h3)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h

theorem vrot4 (n : Nat) (r : List Nat) :
    repN V n ++ 4::r = 4::(repN V' n++r) := by
  have h := congrArg (fun s => s++r) (repN_rotate [4] [2,2,2,2] n)
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

def aFamily (n : Nat) : Z0 := C (Apre++repN V n++[4]++tw (4*n+4)) [] tail2 []
def bFamily (n : Nat) : Z0 := C (Bpre++repN S (n+1)++[7]++tw (4*n+5)) [] tail2 []
def cFamily (n : Nat) : Z0 := C (S++repN V (n+1)++[4]++tw (4*n+6)) [] tail2 [false,false,false,false]
def dFamily (n : Nat) : Z0 := C ([3]++repN S (n+2)++[4]++tw (4*n+7)) [] tail2 []

abbrev tail1 : List Bool := [true]
abbrev tail2pad : List Bool := [true,true,false,false]

theorem phaseA (n : Nat) : ∃ t, 0 < t ∧ run0 table t (aFamily n) = some (bFamily n) := by
  have h1 := ainit_run (repN V n++[4]++tw (4*n+4)) tail2
  have h2 := fourDrain n (4*n+4) (W++[0,1,0]) tail1
  have h3 := scanEvenAny (2*n+1) (Q++repN Q n++W++[0,1,0]) tail1
  have h4 := qscan n (4*n+5) [2,2,2,0,1,0] tail1
  have h5 := aturn (repN S n++[4]++tw (4*n+5)) tail2
  have h6 := aleft (repN S n++[4]++tw (4*n+5)) tail2
  have h7 := mixedDrain n (4*n+5) (X++[0,0,0]) tail1
  have h8 := scanOdd (2*n+2) ([2,2,2,2]++repN P n++X++[0,0,0]) tail1
  have h9 := pscan n (4*n+5) [2,2,2,0,0,0] tail1
  have h10 := aend (repN S n++[7]++tw (4*n+5)) tail2
  simp only [show 2*(2*n+1)+4=4*n+6 by omega,show 2*(2*n+1)+3=4*n+5 by omega,
    show 2*(2*n+2)+3=4*n+7 by omega,show 2*(2*n+2)+2=4*n+6 by omega,
    show 4*n+4+2=4*n+6 by omega,show 4*n+5+2=4*n+7 by omega,
    List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨t,ht⟩ := h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans h10)))))))
  exact ⟨175+t,by omega,by simpa only [aFamily,bFamily,repN,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ] using join0 h1 ht⟩

theorem phaseB (n : Nat) : Path (bFamily n) (cFamily n) := by
  have h1 := binit (repN S n++[7]++tw (4*n+5)) tail2
  have h2 := sevenDrain n (4*n+5) (X++[0,0,2,0]) tail2
  have h3 := scanOdd (2*n+2) ([0,0,0,2,2,2,2]++repN P n++X++[0,0,2,0]) tail2
  have h4 := bdDrain (4*n+6) (repN P n++X++[0,0,2,0]) tail2
  have h5 := scanEvenAny (2*n+2) (J++repN P n++X++[0,0,2,0]) tail2
  have h6 := pevscan n (tw (4*n+6)) (X++[0,0,2,0]) tail2
  have h7 := bend (repN V' n++tw (4*n+6)) tail2
  simp only [show 2*(2*n+2)+3=4*n+7 by omega,show 2*(2*n+2)+2=4*n+6 by omega,
    show 2*(2*n+2)+4=4*n+8 by omega,show 4*n+5+2=4*n+7 by omega,show 4*n+6+2=4*n+8 by omega,
    List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ] at h1 h2 h3 h4 h5 h6 h7
  have h := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))
  simpa only [bFamily,cFamily,repN,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ,vrot4] using h

theorem phaseC (n : Nat) : Path (cFamily n) (dFamily n) := by
  have h1 := cinit (repN V n++[4]++tw (4*n+6)) tail2
  have h2 := fourDrain n (4*n+6) (U++[0,0,0,0,0]) tail2pad
  have h3 := scanEvenAny (2*n+2) (Q++repN Q n++U++[0,0,0,0,0]) tail2pad
  have h4 := qscan n (4*n+7) [2,2,2,2,0,0,0,0,0] tail2pad
  have h5 := cend (repN S n++[4]++tw (4*n+7)) tail2
  simp only [show 2*(2*n+2)+4=4*n+8 by omega,show 2*(2*n+2)+3=4*n+7 by omega,
    show 4*n+6+2=4*n+8 by omega,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ] at h1 h2 h3 h4 h5
  have h := h1.trans (h2.trans (h3.trans (h4.trans h5)))
  simpa only [cFamily,dFamily,repN,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ] using h

theorem phaseD (n : Nat) : Path (dFamily n) (aFamily (n+1)) := by
  have h1 := dinit (repN S (n+1)++[4]++tw (4*n+7)) tail2
  have h2 := mixedDrain (n+1) (4*n+7) (Y++[0]) tail2
  have h3 := scanOdd (2*n+3) ([2,2,2,2]++repN P (n+1)++Y++[0]) tail2
  have h4 := pscan (n+1) (4*n+7) [2,0] tail2
  have h5 := dturn (repN S (n+1)++[7]++tw (4*n+7)) tail2
  have h6 := dleft (repN S (n+1)++[7]++tw (4*n+7)) tail2
  have h7 := sevenDrain (n+1) (4*n+7) (Y++[0]) tail1
  have h8 := scanOdd (2*n+3) ([0,0,0,2,2,2,2]++repN P (n+1)++Y++[0]) tail1
  have h9 := bdDrain (4*n+8) (repN P (n+1)++Y++[0]) tail1
  have h10 := scanEvenAny (2*n+3) (J++repN P (n+1)++Y++[0]) tail1
  have h11 := pevscan (n+1) (tw (4*n+8)) (Y++[0]) tail1
  have h12 := dend (repN V' (n+1)++tw (4*n+8)) tail2
  simp only [show 2*(2*n+3)+3=4*n+9 by omega,show 2*(2*n+3)+2=4*n+8 by omega,
    show 2*(2*n+3)+4=4*n+10 by omega,show 4*n+7+2=4*n+9 by omega,
    show 4*n+8+2=4*n+10 by omega,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have h := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans h12))))))))))
  simpa only [dFamily,aFamily,show 4*(n+1)+4=4*n+8 by omega,repN,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,List.replicate_succ,vrot4] using h


theorem cyclePositive (n : Nat) : ∃ t, 0 < t ∧ run0 table t (aFamily n) = some (aFamily (n+1)) := by
  obtain ⟨t,ht,hr⟩ := phaseA n
  obtain ⟨k,hk⟩ := (phaseB n).trans ((phaseC n).trans (phaseD n))
  exact ⟨t+k,by omega,join0 hr hk⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (cyclePositive n)
theorem positive (n : Nat) : 0 < cost n := (Classical.choose_spec (cyclePositive n)).1
theorem growth (n : Nat) : run0 table (cost n) (aFamily n) = some (aFamily (n+1)) :=
  (Classical.choose_spec (cyclePositive n)).2
theorem entry : run0 table 1828 ⟨0,[],[]⟩ = some (aFamily 0) := by rfl
#print axioms cyclePositive
#print axioms growth
#print axioms entry
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table aFamily 1828 cost entry positive growth m hm
#print axioms never
end BB6.Agent10Raw108LB2822
