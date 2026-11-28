import SweepPumping
import WeightedTNFCertificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.SymbolicSweep
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay

/-- Symbolic words allow an arbitrary number of repeated blocks with a
    shared parameter, plus two independent opaque tails. -/
inductive Atom where
  | bit (b : Bool)
  | repeated (block : List Bool)
  | tailL
  | tailR
  deriving DecidableEq, Repr
abbrev Word := List Atom

def evalWord (k : Nat) (L R : List Bool) : Word → List Bool
  | [] => []
  | .bit b :: w => b :: evalWord k L R w
  | .repeated B :: w => rep B k ++ evalWord k L R w
  | .tailL :: w => L ++ evalWord k L R w
  | .tailR :: w => R ++ evalWord k L R w

def bits (w : List Bool) : Word := w.map Atom.bit

theorem eval_append (k : Nat) (L R : List Bool) (u v : Word) :
    evalWord k L R (u ++ v) = evalWord k L R u ++ evalWord k L R v := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [evalWord,ih,List.append_assoc]

theorem eval_bits (k : Nat) (L R w : List Bool) : evalWord k L R (bits w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => change b :: evalWord k L R (bits w) = b :: w; rw [ih]

structure SCfg where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def eval (k : Nat) (L R : List Bool) (z : SCfg) : Z0 :=
  ⟨z.q,evalWord k L R z.l,evalWord k L R z.r⟩

/-- Reading a symbolic atom fails, rather than assuming a nonempty tail or
    a positive repetition count. Empty literal words use implicit blank. -/
def pop : Word → Option (Bool × Word)
  | [] => some (false,[])
  | .bit b :: w => some (b,w)
  | _ => none

theorem pop_sound (k : Nat) (L R : List Bool) (w w' : Word) (b : Bool)
    (h : pop w = some (b,w')) :
    (evalWord k L R w).headD false = b ∧
      (evalWord k L R w).tail = evalWord k L R w' := by
  cases w with
  | nil => simp [pop] at h; obtain ⟨hb,hw⟩ := h; subst b; subst w'; exact ⟨rfl,rfl⟩
  | cons a w =>
    cases a <;> simp [pop] at h
    rename_i v
    obtain ⟨hb,hw⟩ := h
    subst b; subst w'; exact ⟨rfl,rfl⟩

def symStep (p : PartialMachine) (z : SCfg) : Option SCfg := do
  let (b,l) ← pop z.l
  let mv ← (p (z.q,b)).bind id
  if mv.right then
    let (br,r) ← pop z.r
    pure ⟨mv.next,.bit br :: .bit mv.write :: l,r⟩
  else pure ⟨mv.next,l,.bit mv.write :: z.r⟩

theorem symStep_sound (p : PartialMachine) (k : Nat) (L R : List Bool) (z z' : SCfg)
    (h : symStep p z = some z') : step0 p (eval k L R z) = some (eval k L R z') := by
  cases z with
  | mk q l r =>
    cases hl : pop l with
    | none => simp [symStep,hl] at h
    | some v =>
      obtain ⟨b,l'⟩ := v
      have hL := pop_sound k L R l l' b hl
      cases hp : p (q,b) with
      | none => simp [symStep,hl,hp] at h
      | some tr =>
        cases tr with
        | none => simp [symStep,hl,hp] at h
        | some mv =>
          cases hd : mv.right with
          | false =>
            have hz : z' = ⟨mv.next,l',.bit mv.write :: r⟩ := by
              simpa [symStep,hl,hp,hd] using h.symm
            subst z'
            simp only [step0,eval,hL.1,hp,Option.bind_some,id,Option.map_some,move0,hd,Bool.false_eq_true,ite_false,hL.2,evalWord]
          | true =>
            cases hr : pop r with
            | none => simp [symStep,hl,hp,hd,hr] at h
            | some v =>
              obtain ⟨br,r'⟩ := v
              have hR := pop_sound k L R r r' br hr
              have hz : z' = ⟨mv.next,.bit br :: .bit mv.write :: l',r'⟩ := by
                simpa [symStep,hl,hp,hd,hr] using h.symm
              subst z'
              simp only [step0,eval,hL.1,hp,Option.bind_some,id,Option.map_some,move0,hd,ite_true,hL.2,hR.1,hR.2,evalWord]

def symRun (p : PartialMachine) : Nat → SCfg → Option SCfg
  | 0,z => some z
  | n+1,z => (symStep p z).bind (symRun p n)

theorem symRun_sound (p : PartialMachine) (k : Nat) (L R : List Bool)
    (n : Nat) (z z' : SCfg) (h : symRun p n z = some z') :
    run0 p n (eval k L R z) = some (eval k L R z') := by
  induction n generalizing z with
  | zero => simp [symRun] at h; subst z'; rfl
  | succ n ih =>
    cases hs : symStep p z with
    | none => simp [symRun,hs] at h
    | some t =>
      have hr : symRun p n t = some z' := by simpa [symRun,hs] using h
      simp only [run0,symStep_sound p k L R z t hs,Option.bind_some]
      exact ih t hr

/-- One-block transfer certificate. The input/output tails may themselves
    contain other repeated segments, all sharing the same parameter. -/
structure Sweep where
  right : Bool
  q : Fin 6
  lp : List Bool
  rp : List Bool
  I : List Bool
  O : List Bool
  ls : Word
  rs : Word
  n : Nat
  deriving DecidableEq, Repr

def Sweep.oneSrc (d : Sweep) : SCfg :=
  if d.right then ⟨d.q,bits d.lp ++ [.tailL],bits (d.rp ++ d.I) ++ [.tailR]⟩
  else ⟨d.q,bits (d.lp ++ d.I) ++ [.tailL],bits d.rp ++ [.tailR]⟩

def Sweep.oneDst (d : Sweep) : SCfg :=
  if d.right then ⟨d.q,bits (d.lp ++ d.O) ++ [.tailL],bits d.rp ++ [.tailR]⟩
  else ⟨d.q,bits d.lp ++ [.tailL],bits (d.rp ++ d.O) ++ [.tailR]⟩

def Sweep.src (d : Sweep) : SCfg :=
  if d.right then ⟨d.q,bits d.lp ++ d.ls,bits d.rp ++ [.repeated d.I] ++ d.rs⟩
  else ⟨d.q,bits d.lp ++ [.repeated d.I] ++ d.ls,bits d.rp ++ d.rs⟩

def Sweep.dst (d : Sweep) : SCfg :=
  if d.right then ⟨d.q,bits d.lp ++ [.repeated d.O] ++ d.ls,bits d.rp ++ d.rs⟩
  else ⟨d.q,bits d.lp ++ d.ls,bits d.rp ++ [.repeated d.O] ++ d.rs⟩

theorem Sweep.sound (p : PartialMachine) (d : Sweep)
    (h : symRun p d.n d.oneSrc = some d.oneDst) (k : Nat) (L R : List Bool) :
    run0 p (d.n*k) (eval k L R d.src) = some (eval k L R d.dst) := by
  cases hd : d.right with
  | false =>
    have one (u v : List Bool) : run0 p d.n ⟨d.q,d.lp++d.I++u,d.rp++v⟩ = some ⟨d.q,d.lp++u,d.rp++d.O++v⟩ := by
      simpa [Sweep.oneSrc,Sweep.oneDst,hd,eval,eval_append,eval_bits,evalWord,List.append_assoc] using symRun_sound p 0 u v d.n d.oneSrc d.oneDst h
    simpa [Sweep.src,Sweep.dst,hd,eval,eval_append,eval_bits,evalWord,List.append_assoc] using
      sweepL p d.q d.lp d.rp d.I d.O d.n one k (evalWord k L R d.ls) (evalWord k L R d.rs)
  | true =>
    have one (u v : List Bool) : run0 p d.n ⟨d.q,d.lp++u,d.rp++d.I++v⟩ = some ⟨d.q,d.lp++d.O++u,d.rp++v⟩ := by
      simpa [Sweep.oneSrc,Sweep.oneDst,hd,eval,eval_append,eval_bits,evalWord,List.append_assoc] using symRun_sound p 0 u v d.n d.oneSrc d.oneDst h
    simpa [Sweep.src,Sweep.dst,hd,eval,eval_append,eval_bits,evalWord,List.append_assoc] using
      sweepR p d.q d.lp d.rp d.I d.O d.n one k (evalWord k L R d.ls) (evalWord k L R d.rs)

/-- Shift the cut through a periodic run by a single cell, using the proven
    rotation identity. Prefix/suffix and the other word can be symbolic. -/
structure Cut where
  onRight : Bool
  reverse : Bool
  q : Fin 6
  pre : Word
  suf : Word
  P : List Bool
  b : Bool
  other : Word
  deriving DecidableEq, Repr

def Cut.w0 (d : Cut) : Word := d.pre ++ [.bit d.b,.repeated (d.P++[d.b])] ++ d.suf
def Cut.w1 (d : Cut) : Word := d.pre ++ [.repeated (d.b::d.P),.bit d.b] ++ d.suf

def Cut.z (d : Cut) (w : Word) : SCfg :=
  if d.onRight then ⟨d.q,d.other,w⟩ else ⟨d.q,w,d.other⟩

def Cut.src (d : Cut) : SCfg := d.z (if d.reverse then d.w1 else d.w0)
def Cut.dst (d : Cut) : SCfg := d.z (if d.reverse then d.w0 else d.w1)

theorem Cut.sound (d : Cut) (k : Nat) (L R : List Bool) : eval k L R d.src = eval k L R d.dst := by
  have hw : evalWord k L R d.w0 = evalWord k L R d.w1 := by
    simpa [Cut.w0,Cut.w1,eval_append,evalWord,List.append_assoc] using
      moveCut (evalWord k L R d.pre) (evalWord k L R d.suf) d.P d.b k
  cases hr : d.reverse <;> cases hs : d.onRight <;> simp [Cut.src,Cut.dst,Cut.z,hr,hs,eval,hw]

inductive Phase where
  | bridge (n : Nat)
  | sweep (d : Sweep)
  | cut (d : Cut)
  deriving DecidableEq, Repr

def Phase.run (p : PartialMachine) (z : SCfg) : Phase → Option SCfg
  | .bridge n => symRun p n z
  | .sweep d => if z = d.src ∧ symRun p d.n d.oneSrc = some d.oneDst then some d.dst else none
  | .cut d => if z = d.src then some d.dst else none

def Phase.cost (k : Nat) : Phase → Nat
  | .bridge n => n
  | .sweep d => d.n*k
  | .cut _ => 0

theorem Phase.sound (p : PartialMachine) (k : Nat) (L R : List Bool) (z z' : SCfg) (f : Phase)
    (h : f.run p z = some z') : run0 p (f.cost k) (eval k L R z) = some (eval k L R z') := by
  cases f with
  | bridge n => exact symRun_sound p k L R n z z' h
  | sweep d =>
    by_cases H : z = d.src ∧ symRun p d.n d.oneSrc = some d.oneDst
    · have hz : d.dst = z' := by simpa [Phase.run,H] using h
      rw [H.1,← hz]
      exact d.sound p H.2 k L R
    · simp [Phase.run,H] at h
  | cut d =>
    by_cases H : z = d.src
    · have hz : d.dst = z' := by simpa [Phase.run,H] using h
      rw [H,← hz]
      simp only [Phase.cost,run0,d.sound]
    · simp [Phase.run,H] at h

def phasesRun (p : PartialMachine) (z : SCfg) : List Phase → Option SCfg
  | [] => some z
  | f::fs => (f.run p z).bind (fun t => phasesRun p t fs)

def phasesCost (k : Nat) : List Phase → Nat
  | [] => 0
  | f::fs => f.cost k + phasesCost k fs

theorem phasesSound (p : PartialMachine) (k : Nat) (L R : List Bool) (fs : List Phase) (z z' : SCfg)
    (h : phasesRun p z fs = some z') : run0 p (phasesCost k fs) (eval k L R z) = some (eval k L R z') := by
  induction fs generalizing z with
  | nil => simp [phasesRun] at h; subst z'; rfl
  | cons f fs ih =>
    cases hf : f.run p z with
    | none => simp [phasesRun,hf] at h
    | some t =>
      have ht : phasesRun p t fs = some z' := by simpa [phasesRun,hf] using h
      exact join0 (f.sound p k L R z t hf) (ih t ht)

theorem phasesCost_mono (fs : List Phase) (k : Nat) : phasesCost 0 fs ≤ phasesCost k fs := by
  induction fs with
  | nil => exact Nat.le_refl 0
  | cons f fs ih =>
    have H : f.cost 0 ≤ f.cost k := by cases f <;> simp [Phase.cost]
    exact Nat.add_le_add H ih

def nextWord : Word → Word
  | [] => []
  | .repeated B :: w => bits B ++ [.repeated B] ++ nextWord w
  | a::w => a::nextWord w

def next (z : SCfg) : SCfg := ⟨z.q,nextWord z.l,nextWord z.r⟩

theorem evalNextWord (k : Nat) (L R : List Bool) (w : Word) :
    evalWord k L R (nextWord w) = evalWord (k+1) L R w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [nextWord,evalWord,eval_append,eval_bits,rep,ih,List.append_assoc]

theorem evalNext (k : Nat) (L R : List Bool) (z : SCfg) : eval k L R (next z) = eval (k+1) L R z := by
  simp [eval,next,evalNextWord]

structure Certificate where
  entry : Nat
  initial : SCfg
  phases : List Phase
  deriving DecidableEq, Repr

def Certificate.check (p : PartialMachine) (c : Certificate) : Bool :=
  decide (run0 p c.entry ⟨0,[],[]⟩ = some (eval 0 [] [] c.initial) ∧
    phasesRun p c.initial c.phases = some (next c.initial) ∧ 0 < phasesCost 0 c.phases)

theorem Certificate.never (p : PartialMachine) (c : Certificate) (h : c.check p = true) :
    ∀ m, compatible p m → NeverHalts m := by
  have H := of_decide_eq_true h
  obtain ⟨he,hr,hpos⟩ := H
  apply never_of_growth p (fun k => eval k [] [] c.initial) c.entry (fun k => phasesCost k c.phases) he
  · intro k; exact Nat.lt_of_lt_of_le hpos (phasesCost_mono c.phases k)
  · intro k
    simpa only [evalNext] using phasesSound p k [] [] c.phases c.initial (next c.initial) hr

theorem Certificate.cover (p : PartialMachine) (c : Certificate) (h : c.check p = true) (B : Nat) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  exact weighted_never B m (c.never p h m hm)

#print axioms symRun_sound
#print axioms Sweep.sound
#print axioms Certificate.never
#print axioms Certificate.cover
end BB6Coverage.SymbolicSweep
