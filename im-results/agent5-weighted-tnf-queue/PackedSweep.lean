import FastPhaseTree
import Agent46AutoPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent5PackedSweep
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper

def encode0 (z : Z0) : P := ⟨z.q,pack z.l,pack z.r⟩

theorem encode0_read (z : Z0) : readP (encode0 z) = (z.q,z.l.headD false) := by
  unfold readP encode0
  rw [pack_head]
  cases z.l.headD false <;> rfl

theorem encode0_move (mv : Move) (z : Z0) : encode0 (move0 mv z) = moveP mv (encode0 z) := by
  cases h : mv.right <;> simp [encode0,move0,moveP,h,pack,pack_head,pack_tail]

theorem encode0_step (p : PartialMachine) (z : Z0) : (step0 p z).map encode0 = stepP p (encode0 z) := by
  unfold step0 stepP
  rw [encode0_read]
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [encode0_move]

theorem encode0_run (p : PartialMachine) (n : Nat) (z : Z0) :
    (run0 p n z).map encode0 = runP p n (encode0 z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [run0,runP,← encode0_step]
    cases h : step0 p z with
    | none => rfl
    | some t => exact ih t

def cat (xs : List Bool) (v : Nat) : Nat := pack xs + 2^xs.length*v

theorem pack_append (xs ys : List Bool) : pack (xs++ys) = cat xs (pack ys) := by
  induction xs with
  | nil => simp [cat,pack]
  | cons x xs ih =>
    simp only [List.cons_append,pack,ih,cat,List.length_cons,Nat.pow_succ,Nat.mul_add,Nat.add_assoc]
    rw [Nat.mul_comm 2 (2^xs.length),Nat.mul_assoc]
    simp [Nat.mul_assoc]

def repCat (xs : List Bool) : Nat → Nat → Nat
  | 0,v => v
  | n+1,v => cat xs (repCat xs n v)

theorem pack_rep (xs : List Bool) (n : Nat) (ys : List Bool) :
    pack (rep xs n++ys) = repCat xs n (pack ys) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,repCat,List.append_assoc,pack_append,ih]

theorem pack_surj_aux (f n : Nat) (h : n < 2^f) : ∃ xs, pack xs=n := by
  induction f generalizing n with
  | zero =>
    have : n=0 := by simpa using h
    exact ⟨[],by simp [pack,this]⟩
  | succ f ih =>
    have hh : n/2 < 2^f := by rw [Nat.pow_succ] at h; omega
    obtain ⟨xs,hxs⟩ := ih (n/2) hh
    refine ⟨(n%2 == 1)::xs,?_⟩
    simp only [pack,hxs]
    by_cases hn : n%2=1
    · simp [hn]; omega
    · simp [hn]; omega

theorem pack_surj (n : Nat) : ∃ xs, pack xs=n := by
  apply pack_surj_aux (n+1)
  have hp (k : Nat) : k < 2^(k+1) := by
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  exact hp n

theorem sweepRP (p : PartialMachine) (q : Fin 6) (lp rp I O : List Bool) (k n L R : Nat)
    (h : Auto.knownRun p k ⟨q,lp,rp++I⟩ = some ⟨q,lp++O,rp⟩) :
    runP p (k*n) ⟨q,cat lp L,cat rp (repCat I n R)⟩ =
      some ⟨q,cat lp (repCat O n L),cat rp R⟩ := by
  obtain ⟨l,rfl⟩ := pack_surj L
  obtain ⟨r,rfl⟩ := pack_surj R
  have one (a b : List Bool) : run0 p k ⟨q,lp++a,rp++I++b⟩ =
      some ⟨q,lp++O++a,rp++b⟩ := by
    simpa [Auto.extend] using Auto.knownRun_sound p k h a b
  have hh := sweepR p q lp rp I O k one n l r
  have he := (encode0_run p (k*n) ⟨q,lp++l,rp++rep I n++r⟩).symm
  rw [hh] at he
  simpa only [Option.map_some,encode0,List.append_assoc,pack_append,pack_rep] using he

theorem sweepLP (p : PartialMachine) (q : Fin 6) (lp rp I O : List Bool) (k n L R : Nat)
    (h : Auto.knownRun p k ⟨q,lp++I,rp⟩ = some ⟨q,lp,rp++O⟩) :
    runP p (k*n) ⟨q,cat lp (repCat I n L),cat rp R⟩ =
      some ⟨q,cat lp L,cat rp (repCat O n R)⟩ := by
  obtain ⟨l,rfl⟩ := pack_surj L
  obtain ⟨r,rfl⟩ := pack_surj R
  have one (a b : List Bool) : run0 p k ⟨q,lp++I++a,rp++b⟩ =
      some ⟨q,lp++a,rp++O++b⟩ := by
    simpa [Auto.extend] using Auto.knownRun_sound p k h a b
  have hh := sweepL p q lp rp I O k one n l r
  have he := (encode0_run p (k*n) ⟨q,lp++rep I n++l,rp++r⟩).symm
  rw [hh] at he
  simpa only [Option.map_some,encode0,List.append_assoc,pack_append,pack_rep] using he

inductive Action where
  | steps (k : Nat)
  | right (lp rp I O : List Bool) (k n : Nat)
  | left (lp rp I O : List Bool) (k n : Nat)
  deriving DecidableEq, Repr

def action (p : PartialMachine) (z : P) : Action → Option (Nat × P)
  | .steps k => (runP p k z).map fun y => (k,y)
  | .right lp rp I O k n =>
    let L := z.l / 2^lp.length
    let R := z.r / 2^(rp.length+I.length*n)
    if z = ⟨z.q,cat lp L,cat rp (repCat I n R)⟩ ∧
      Auto.knownRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      some (k*n,⟨z.q,cat lp (repCat O n L),cat rp R⟩)
    else none
  | .left lp rp I O k n =>
    let L := z.l / 2^(lp.length+I.length*n)
    let R := z.r / 2^rp.length
    if z = ⟨z.q,cat lp (repCat I n L),cat rp R⟩ ∧
      Auto.knownRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      some (k*n,⟨z.q,cat lp L,cat rp (repCat O n R)⟩)
    else none

theorem action_sound (p : PartialMachine) (z : P) (op : Action) {out : Nat × P}
    (h : action p z op = some out) : runP p out.1 z = some out.2 := by
  cases op with
  | steps k =>
    simp only [action] at h
    cases hs : runP p k z with
    | none => simp [hs] at h
    | some y => simp [hs] at h; obtain ⟨rfl,rfl⟩ := h; exact hs
  | right lp rp I O k n =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      exact (congrArg (runP p (k*n)) hc.1).trans (sweepRP p z.q lp rp I O k n _ _ hc.2)
    next => simp at h
  | left lp rp I O k n =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      exact (congrArg (runP p (k*n)) hc.1).trans (sweepLP p z.q lp rp I O k n _ _ hc.2)
    next => simp at h

def traceRun (p : PartialMachine) (z : P) : List Action → Option (Nat × P)
  | [] => some (0,z)
  | op::ops => do
    let (k,y) ← action p z op
    let (n,t) ← traceRun p y ops
    return (k+n,t)

theorem traceRun_sound (p : PartialMachine) (ops : List Action) (z : P) {out : Nat × P}
    (h : traceRun p z ops = some out) : runP p out.1 z = some out.2 := by
  induction ops generalizing z out with
  | nil => simp [traceRun] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | cons op ops ih =>
    simp only [traceRun] at h
    cases ha : action p z op with
    | none => simp [ha] at h
    | some a =>
      rcases a with ⟨k,y⟩
      simp only [ha,Option.bind_some] at h
      cases hb : traceRun p y ops with
      | none => simp [hb] at h
      | some b =>
        rcases b with ⟨n,t⟩
        simp only [hb,Option.bind_some,Option.some.injEq] at h
        subst out
        exact joinP (action_sound p z op ha) (ih y hb)

#print axioms traceRun_sound
end BB6.Agent5PackedSweep
