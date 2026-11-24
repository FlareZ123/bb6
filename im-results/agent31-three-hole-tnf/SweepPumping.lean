import SparseZipper
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent31Pump
open BB6Coverage Agent50Zipper

/-- Absolute head coordinate is irrelevant to blank-tape nonhalting. -/
structure Z0 where
  q : Fin 6
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def move0 (mv : Move) (z : Z0) : Z0 :=
  if mv.right then
    ⟨mv.next,z.r.headD false::mv.write::z.l.tail,z.r.tail⟩
  else ⟨mv.next,z.l.tail,mv.write::z.r⟩

def step0 (p : PartialMachine) (z : Z0) : Option Z0 :=
  ((p (z.q,z.l.headD false)).bind id).map (fun mv => move0 mv z)

def run0 (p : PartialMachine) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => (step0 p z).bind (run0 p n)

def project (z : Z) : Z0 := ⟨z.q,z.l,z.r⟩

theorem project_move (mv : Move) (z : Z) :
    project (Agent50Zipper.move mv z) = move0 mv (project z) := by
  cases h : mv.right <;> simp [Agent50Zipper.move,move0,project,h]

theorem step_project (p : PartialMachine) (z : Z) :
    (Agent50Zipper.step p z).map project = step0 p (project z) := by
  unfold Agent50Zipper.step step0
  change (((p (z.q,z.l.headD false)).bind id).map (fun mv => Agent50Zipper.move mv z)).map project =
    ((p (z.q,z.l.headD false)).bind id).map (fun mv => move0 mv (project z))
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [project_move]

theorem run_project (p : PartialMachine) (n : Nat) (z : Z) :
    (zrun p n z).map project = run0 p n (project z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [zrun,run0,← step_project]
    cases h : Agent50Zipper.step p z with
    | none => rfl
    | some t => exact ih t

theorem run0_add (p : PartialMachine) (n k : Nat) (z : Z0) :
    run0 p (n+k) z = (run0 p n z).bind (run0 p k) := by
  induction n generalizing z with
  | zero => simp [run0]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run0]
    cases step0 p z with
    | none => rfl
    | some t => exact ih t

theorem join0 {p : PartialMachine} {n k : Nat} {a b c : Z0}
    (h : run0 p n a = some b) (g : run0 p k b = some c) :
    run0 p (n+k) a = some c := by
  rw [run0_add,h]; exact g

def rep (P : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => P ++ rep P n

theorem rep_snoc (P : List Bool) (n : Nat) : rep P n ++ P = P ++ rep P n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

/-- Pump a leftward block transfer with fixed frame words on both sides.
    The hypothesis is a literal finite computation for arbitrary untouched
    tails, not a test at finitely many repetition counts. -/
theorem sweepL (p : PartialMachine) (q : Fin 6) (lp rp I O : List Bool) (k : Nat)
    (one : ∀ L R, run0 p k ⟨q,lp++I++L,rp++R⟩ = some ⟨q,lp++L,rp++O++R⟩)
    (n : Nat) (L R : List Bool) :
    run0 p (k*n) ⟨q,lp++rep I n++L,rp++R⟩ = some ⟨q,lp++L,rp++rep O n++R⟩ := by
  induction n generalizing R with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h1 := one (rep I n++L) R
    have h2 := ih (O++R)
    have h1' : run0 p k ⟨q,lp++rep I (n+1)++L,rp++R⟩ =
        some ⟨q,lp++rep I n++L,rp++(O++R)⟩ := by
      simpa only [rep,List.append_assoc] using h1
    have H := join0 h1' h2
    rw [Nat.mul_succ, Nat.add_comm (k*n) k]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep O n) O R,rep_snoc O n] using H

theorem sweepR (p : PartialMachine) (q : Fin 6) (lp rp I O : List Bool) (k : Nat)
    (one : ∀ L R, run0 p k ⟨q,lp++L,rp++I++R⟩ = some ⟨q,lp++O++L,rp++R⟩)
    (n : Nat) (L R : List Bool) :
    run0 p (k*n) ⟨q,lp++L,rp++rep I n++R⟩ = some ⟨q,lp++rep O n++L,rp++R⟩ := by
  induction n generalizing L with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h1 := one L (rep I n++R)
    have h2 := ih (O++L)
    have h1' : run0 p k ⟨q,lp++L,rp++rep I (n+1)++R⟩ =
        some ⟨q,lp++(O++L),rp++rep I n++R⟩ := by
      simpa only [rep,List.append_assoc] using h1
    have H := join0 h1' h2
    rw [Nat.mul_succ, Nat.add_comm (k*n) k]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep O n) O L,rep_snoc O n] using H

theorem rotate (b : Bool) (P : List Bool) (n : Nat) :
    [b] ++ rep (P++[b]) n = rep ([b]++P) n ++ [b] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    rw [← List.append_assoc [b] P ( [b] ++ rep (P ++ [b]) n)]
    rw [ih]
    simp only [List.append_assoc]

theorem moveCut (pre suf P : List Bool) (b : Bool) (n : Nat) :
    (pre++[b]) ++ rep (P++[b]) n ++ suf = pre ++ rep ([b]++P) n ++ ([b]++suf) := by
  calc
    _ = pre ++ (([b] ++ rep (P++[b]) n) ++ suf) := by simp only [List.append_assoc]
    _ = _ := by rw [rotate]; simp only [List.append_assoc]

def start : Z := ⟨0,0,[],[]⟩
theorem start_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

/-- Any positive-cost inductive family gives unbounded live prefixes in
    the original raw machine semantics, for every compatible completion. -/
theorem never_of_growth (p : PartialMachine) (family : Nat → Z0)
    (entry : Nat) (cost : Nat → Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (family 0))
    (positive : ∀ k, 0 < cost k)
    (growth : ∀ k, run0 p (cost k) (family k) = some (family (k+1)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (family k) := by
    intro k
    induction k with
    | zero => exact ⟨entry,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,ht,hr⟩ := ih
      have hp := positive k
      exact ⟨t+cost k,by omega,join0 hr (growth k)⟩
  intro n
  obtain ⟨t,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (family n) :=
    (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms sweepL
#print axioms sweepR
#print axioms never_of_growth
end BB6Coverage.Agent31Pump
