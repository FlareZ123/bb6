import Agent46Auto2

namespace BB6Coverage.Agent31Pump.Auto2.Counter
open BB6Coverage Agent31Pump Auto2

/-- Each original exponent is replaced by an affine expression in one
    selected exponent. This includes setting it to a constant. -/
structure Param where
  v : Bool
  scale : Nat
  shift : Nat
  deriving DecidableEq, Repr

def Param.eval (a : Param) (n : Bool → Nat) : Nat := a.scale * n a.v + a.shift

def Word.change (w : Auto2.Word) (f : Bool → Param) : Auto2.Word :=
  match w with
  | .lit xs => .lit xs
  | .periodic pre block v post =>
    let a := f v
    let s := Word.change post f
    if a.scale = 0 then s.push (pre ++ rep block a.shift)
    else .periodic (pre ++ rep block a.shift) (rep block a.scale) a.v s

theorem Word.change_sound (w : Auto2.Word) (f : Bool → Param) (n : Bool → Nat) :
    (Word.change w f).eval n = w.eval (fun v => (f v).eval n) := by
  induction w with
  | lit => rfl
  | periodic pre block v post ih =>
    simp only [Word.change]
    split
    next h => simp [Auto2.Word.push_sound,ih,Auto2.Word.eval,Param.eval,h,List.append_assoc]
    next h =>
      simp only [Auto2.Word.eval,ih,Param.eval,rep_mul,List.append_assoc]
      rw [← List.append_assoc (rep block (f v).shift) (rep block ((f v).scale * n (f v).v)),Auto.rep_add]
      rw [Nat.add_comm (f v).shift]

def PZ.change (z : Auto2.PZ) (f : Bool → Param) : Auto2.PZ :=
  ⟨z.q,Word.change z.l f,Word.change z.r f⟩

theorem PZ.change_sound (z : Auto2.PZ) (f : Bool → Param) (n : Bool → Nat) :
    (PZ.change z f).eval n = z.eval (fun v => (f v).eval n) := by
  simp [PZ.change,Auto2.PZ.eval,Word.change_sound]

def N (k m : Nat) : Bool → Nat := fun | false => k | true => m
private def loopIn : Bool → Param := fun | false => ⟨false,1,0⟩ | true => ⟨true,1,1⟩
private def loopOut : Bool → Param := fun | false => ⟨false,1,1⟩ | true => ⟨true,1,0⟩
private def resetIn : Bool → Param := fun | false => ⟨false,1,0⟩ | true => ⟨true,0,0⟩
private def resetOut (d : Nat) : Bool → Param := fun | false => ⟨false,0,0⟩ | true => ⟨false,2,d⟩

/-- A decreasing counter is converted into an increasing counter by an
    arbitrary-exponent trace; on exhaustion a second trace resets the first
    counter and produces twice its value plus a fixed offset. -/
structure Cert where
  family : Auto2.PZ
  entry : Nat
  start : Nat
  offset : Nat
  loopOps : List Action
  loopA : Nat
  loopC : Nat
  resetOps : List Action
  resetA : Nat
  resetC : Nat
  deriving DecidableEq, Repr

def Cert.F (c : Cert) (k m : Nat) : Z0 := c.family.eval (N k m)
def Cert.loop (c : Cert) : Macro :=
  ⟨PZ.change c.family loopIn,PZ.change c.family loopOut,c.loopOps,c.loopA,0,c.loopC⟩
def Cert.reset (c : Cert) : Macro :=
  ⟨PZ.change c.family resetIn,PZ.change c.family (resetOut c.offset),c.resetOps,c.resetA,0,c.resetC⟩
def Cert.check (p : PartialMachine) (c : Cert) : Bool :=
  (decide (0<c.resetC ∧ run0 p c.entry ⟨0,[],[]⟩ = some (c.F 0 c.start)) &&
    c.loop.check p) && c.reset.check p

theorem Cert.loop_sound (p : PartialMachine) (c : Cert) (h : c.loop.check p = true) (k m : Nat) :
    run0 p (c.loopA*k+c.loopC) (c.F k (m+1)) = some (c.F (k+1) m) := by
  have H := Macro.sound p c.loop h (N k m)
  have hin : (fun v => (loopIn v).eval (N k m)) = N k (m+1) := by
    funext v; cases v <;> simp [loopIn,Param.eval,N]
  have hout : (fun v => (loopOut v).eval (N k m)) = N (k+1) m := by
    funext v; cases v <;> simp [loopOut,Param.eval,N]
  simpa [Cert.loop,Cert.F,PZ.change_sound,hin,hout,N] using H

theorem Cert.reset_sound (p : PartialMachine) (c : Cert) (h : c.reset.check p = true) (k : Nat) :
    run0 p (c.resetA*k+c.resetC) (c.F k 0) = some (c.F 0 (2*k+c.offset)) := by
  have H := Macro.sound p c.reset h (N k 0)
  have hin : (fun v => (resetIn v).eval (N k 0)) = N k 0 := by
    funext v; cases v <;> simp [resetIn,Param.eval,N]
  have hout : (fun v => (resetOut c.offset v).eval (N k 0)) = N 0 (2*k+c.offset) := by
    funext v; cases v <;> simp [resetOut,Param.eval,N]
  simpa [Cert.reset,Cert.F,PZ.change_sound,hin,hout,N] using H

def Cert.cost (c : Cert) (n : Nat) : Nat := drainCost c.loopA c.loopC 1 n 0 + (c.resetA*n+c.resetC)

theorem Cert.growth (p : PartialMachine) (c : Cert) (h : c.check p = true) (n : Nat) :
    run0 p (c.cost n) (c.F 0 n) = some (c.F 0 (2*n+c.offset)) := by
  simp only [Cert.check,Bool.and_eq_true,decide_eq_true_eq] at h
  have hd := drain p (fun m k => c.F k m) c.loopA c.loopC 1 (fun m k => c.loop_sound p h.1.2 k m) n 0
  have hd' : run0 p (drainCost c.loopA c.loopC 1 n 0) (c.F 0 n) = some (c.F n 0) := by simpa using hd
  exact join0 hd' (c.reset_sound p h.2 n)

theorem Cert.never (p : PartialMachine) (c : Cert) (h : c.check p = true) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have hg := c.growth p h
  simp only [Cert.check,Bool.and_eq_true,decide_eq_true_eq] at h
  apply never_of_map p (c.F 0) (fun n => 2*n+c.offset) c.cost c.entry c.start h.1.1.2 _ hg m hm
  intro n; unfold Cert.cost; have := h.1.1.1; omega

#print axioms Cert.growth
#print axioms Cert.never
end BB6Coverage.Agent31Pump.Auto2.Counter
