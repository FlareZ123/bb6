import SymWord
import RuleCompose
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6SymTrace
open BB6Coverage BB6.Agent6NatTape BB6.Agent6WordNat BB6.Agent6SymWord BB6.Agent6RuleCompose
structure State where
  l : Sym
  r : Sym
  deriving DecidableEq, Repr

def State.eval (s : State) (x y : Nat) : N1 := ⟨4,BB6.Agent6SymWord.eval s.l (env x y),BB6.Agent6SymWord.eval s.r (env x y)⟩
def State.same (d : Widths) (a b : State) : Bool := BB6.Agent6SymWord.same d a.l b.l && BB6.Agent6SymWord.same d a.r b.r

theorem State.same_sound (d : Widths) (a b : State) (h : State.same d a b = true) (x y : Nat) : a.eval x y = b.eval x y := by
  simp only [State.same,Bool.and_eq_true] at h
  unfold State.eval
  rw [BB6.Agent6SymWord.same_sound d a.l b.l h.1 x y, BB6.Agent6SymWord.same_sound d a.r b.r h.2 x y]

structure Cost where
  c : Nat
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def Cost.eval (c : Cost) (x y : Nat) := c.c+c.x*x+c.y*y
def Cost.add (a b : Cost) : Cost := ⟨a.c+b.c,a.x+b.x,a.y+b.y⟩
theorem Cost.eval_add (a b : Cost) (x y : Nat) : (a.add b).eval x y = a.eval x y+b.eval x y := by
  simp only [Cost.add,Cost.eval,Nat.add_mul]; ac_rfl

inductive Action (p : PartialMachine) where
  | fixed (rs : List (CR p)) (L R : Sym)
  | symbolic (s : CS p) (v : Var) (k : Nat) (L R : Sym)

structure Transition where
  src : State
  dst : State
  cost : Cost

def block (a w : Word) (v : Var) (k : Nat) (t : Sym) : Sym := .lit a :: .lit (w.rep k) :: .rep w v :: t

def describe {p : PartialMachine} : Action p → Option Transition
  | .fixed rs L R => (combine rs).map fun r => ⟨⟨.lit r.leftIn::L,.lit r.rightIn::R⟩,⟨.lit r.leftOut::L,.lit r.rightOut::R⟩,⟨r.cost,0,0⟩⟩
  | .symbolic s v k L R =>
    let r := s.data
    let cost := ⟨r.cost*k,if v then 0 else r.cost,if v then r.cost else 0⟩
    if r.leftwards then some ⟨⟨block r.A r.W v k L,.lit r.C::R⟩,⟨.lit r.A::L,block r.C r.V v k R⟩,cost⟩
    else some ⟨⟨.lit r.C::L,block r.A r.W v k R⟩,⟨block r.C r.V v k L,.lit r.A::R⟩,cost⟩

theorem rep_apply (w : Word) (a b t : Nat) : (w.rep a).apply ((w.rep b).apply t) = (w.rep (a+b)).apply t := by rw [Word.rep_add,Word.cat_apply]

theorem describe_sound {p : PartialMachine} {a : Action p} {t : Transition} (h : describe a = some t) (x y : Nat) :
    runN p (t.cost.eval x y) (t.src.eval x y) = some (t.dst.eval x y) := by
  cases a with
  | fixed rs L R =>
    unfold describe at h
    cases hc : combine rs with
    | none => simp [hc] at h
    | some r =>
      simp only [hc,Option.map_some,Option.some.injEq] at h
      subst t
      simpa [Cost.eval,State.eval,eval] using combine_sound rs hc (eval L (env x y)) (eval R (env x y))
  | symbolic s v k L R =>
    cases hd : s.data.leftwards <;> cases v <;>
      simp only [describe,hd,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq] at h <;> subst t
    all_goals
      simp only [Cost.eval,State.eval,eval,block,env,Bool.false_eq_true,ite_false,ite_true,Nat.zero_mul,Nat.add_zero,Nat.zero_add]
    · rw [rep_apply,rep_apply,←Nat.mul_add]
      exact s.data.right p s.sound hd (k+x) _ _
    · rw [rep_apply,rep_apply,←Nat.mul_add]
      exact s.data.right p s.sound hd (k+y) _ _
    · rw [rep_apply,rep_apply,←Nat.mul_add]
      exact s.data.left p s.sound hd (k+x) _ _
    · rw [rep_apply,rep_apply,←Nat.mul_add]
      exact s.data.left p s.sound hd (k+y) _ _

def trace {p : PartialMachine} (d : Widths) (s : State) : List (Action p) → Option (State × Cost)
  | [] => some (s,⟨0,0,0⟩)
  | a::as => (describe a).bind fun t =>
    if s.same d t.src then (trace d t.dst as).map (fun v => (v.1,t.cost.add v.2)) else none

theorem trace_sound {p : PartialMachine} (d : Widths) (as : List (Action p)) {s out : State} {c : Cost}
    (h : trace d s as = some (out,c)) (x y : Nat) : runN p (c.eval x y) (s.eval x y) = some (out.eval x y) := by
  induction as generalizing s out c with
  | nil =>
    simp only [trace,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨hs,hc⟩; subst out; subst c; simp only [Cost.eval,Nat.zero_mul,Nat.add_zero]; rfl
  | cons a as ih =>
    rw [trace] at h
    cases ha : describe a with
    | none => simp [ha] at h
    | some t =>
      simp only [ha,Option.bind_some] at h
      split at h
      · rename_i he
        cases ht : trace d t.dst as with
        | none => simp [ht] at h
        | some v =>
          rcases v with ⟨z,k⟩
          simp only [ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨hz,hc⟩; subst out; subst c
          rw [Cost.eval_add,State.same_sound d s t.src he x y]
          exact runN_join (describe_sound ha x y) (ih ht)
      · contradiction

def check {p : PartialMachine} (d : Widths) (s : State) (as : List (Action p)) (out : State) (c : Cost) : Bool :=
  match trace d s as with
  | none => false
  | some (z,k) => z.same d out && decide (k=c)

theorem check_sound {p : PartialMachine} (d : Widths) (s : State) (as : List (Action p)) (out : State) (c : Cost)
    (h : check d s as out c = true) (x y : Nat) : runN p (c.eval x y) (s.eval x y) = some (out.eval x y) := by
  unfold check at h
  cases ht : trace d s as with
  | none => simp [ht] at h
  | some v =>
    rcases v with ⟨z,k⟩
    simp only [ht,Bool.and_eq_true,decide_eq_true_eq] at h
    rw [←h.2]
    rw [←State.same_sound d z out h.1 x y]
    exact trace_sound d as ht x y
#print axioms check_sound
end BB6.Agent6SymTrace
