import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50CheckedSweepTrace
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

structure RightRule (p : PartialMachine) where
  q : Fin 6
  lp : List Bool
  rp : List Bool
  input : List Bool
  output : List Bool
  k : Nat
  one : ∀ L R, run0 p k ⟨q,lp++L,rp++input++R⟩ = some ⟨q,lp++output++L,rp++R⟩

structure LeftRule (p : PartialMachine) where
  q : Fin 6
  lp : List Bool
  rp : List Bool
  input : List Bool
  output : List Bool
  k : Nat
  one : ∀ L R, run0 p k ⟨q,lp++input++L,rp++R⟩ = some ⟨q,lp++L,rp++output++R⟩

def RightRule.exec {p : PartialMachine} (r : RightRule p) (n : Nat) (z : Z0) : Option Z0 :=
  let a := r.lp
  let b := r.rp ++ rep r.input n
  if z.q = r.q ∧ z.l.take a.length = a ∧ z.r.take b.length = b then
    some ⟨r.q,r.lp ++ rep r.output n ++ z.l.drop a.length,r.rp ++ z.r.drop b.length⟩
  else none

def LeftRule.exec {p : PartialMachine} (r : LeftRule p) (n : Nat) (z : Z0) : Option Z0 :=
  let a := r.lp ++ rep r.input n
  let b := r.rp
  if z.q = r.q ∧ z.l.take a.length = a ∧ z.r.take b.length = b then
    some ⟨r.q,r.lp ++ z.l.drop a.length,r.rp ++ rep r.output n ++ z.r.drop b.length⟩
  else none

theorem prefix_decomp (xs ys : List Bool) (h : xs.take ys.length = ys) : xs = ys ++ xs.drop ys.length := by
  calc
    xs = xs.take ys.length ++ xs.drop ys.length := (List.take_append_drop _ _).symm
    _ = ys ++ xs.drop ys.length := congrArg (· ++ xs.drop ys.length) h

theorem RightRule.sound {p : PartialMachine} (r : RightRule p) (n : Nat) (z z' : Z0) (h : r.exec n z = some z') : run0 p (r.k*n) z = some z' := by
  unfold RightRule.exec at h
  dsimp only at h
  split at h
  next hh =>
    have hl := prefix_decomp z.l r.lp hh.2.1
    have hr := prefix_decomp z.r (r.rp ++ rep r.input n) hh.2.2
    have hz : z = ⟨r.q,r.lp ++ z.l.drop r.lp.length,r.rp ++ rep r.input n ++ z.r.drop (r.rp ++ rep r.input n).length⟩ := by
      cases z; congr 1
      · exact hh.1
    have H := sweepR p r.q r.lp r.rp r.input r.output r.k r.one n (z.l.drop r.lp.length) (z.r.drop (r.rp ++ rep r.input n).length)
    exact (congrArg (run0 p (r.k*n)) hz).trans (H.trans h)
  next hh => contradiction

theorem LeftRule.sound {p : PartialMachine} (r : LeftRule p) (n : Nat) (z z' : Z0) (h : r.exec n z = some z') : run0 p (r.k*n) z = some z' := by
  unfold LeftRule.exec at h
  dsimp only at h
  split at h
  next hh =>
    have hl := prefix_decomp z.l (r.lp ++ rep r.input n) hh.2.1
    have hr := prefix_decomp z.r r.rp hh.2.2
    have hz : z = ⟨r.q,r.lp ++ rep r.input n ++ z.l.drop (r.lp ++ rep r.input n).length,r.rp ++ z.r.drop r.rp.length⟩ := by
      cases z; congr 1
      · exact hh.1
    have H := sweepL p r.q r.lp r.rp r.input r.output r.k r.one n (z.l.drop (r.lp ++ rep r.input n).length) (z.r.drop r.rp.length)
    exact (congrArg (run0 p (r.k*n)) hz).trans (H.trans h)
  next hh => contradiction

inductive Cmd (p : PartialMachine) where
  | raw (n : Nat)
  | left (r : LeftRule p) (n : Nat)
  | right (r : RightRule p) (n : Nat)

def Cmd.cost {p : PartialMachine} : Cmd p → Nat
  | .raw n => n
  | .left r n => r.k*n
  | .right r n => r.k*n

def Cmd.exec {p : PartialMachine} (z : Z0) : Cmd p → Option Z0
  | .raw n => run0 p n z
  | .left r n => r.exec n z
  | .right r n => r.exec n z

theorem Cmd.sound {p : PartialMachine} (c : Cmd p) (z z' : Z0) (h : c.exec z = some z') : run0 p c.cost z = some z' := by
  cases c with
  | raw n => exact h
  | left r n => exact r.sound n z z' h
  | right r n => exact r.sound n z z' h

def trace {p : PartialMachine} : List (Cmd p) → Z0 → Option Z0
  | [],z => some z
  | c::cs,z => (c.exec z).bind (trace cs)

def cost {p : PartialMachine} : List (Cmd p) → Nat
  | [] => 0
  | c::cs => c.cost + cost cs

theorem trace_sound {p : PartialMachine} (cs : List (Cmd p)) (z z' : Z0) (h : trace cs z = some z') : run0 p (cost cs) z = some z' := by
  induction cs generalizing z with
  | nil => exact h
  | cons c cs ih =>
    cases he : c.exec z with
    | none => simp [trace,he] at h
    | some u =>
      have ht : trace cs u = some z' := by simpa [trace,he] using h
      exact join0 (c.sound z u he) (ih u ht)

#print axioms trace_sound
end BB6.Agent50CheckedSweepTrace
