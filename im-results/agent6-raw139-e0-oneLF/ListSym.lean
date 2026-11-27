import SymWord
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6ListSym
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6NatTape BB6.Agent6WordNat BB6.Agent6SymWord

inductive Atom where
  | lit (w : List Bool)
  | rep (w : List Bool) (v : Var)
  deriving DecidableEq
abbrev LS := List Atom
def word (w : List Bool) : Word := ⟨w.length,value w⟩
def code : LS → Sym
  | [] => []
  | .lit w::s => .lit (word w)::code s
  | .rep w v::s => .rep (word w) v::code s
def ev : LS → Env → List Bool
  | [],_ => []
  | .lit w::s,e => w++ev s e
  | .rep w v::s,e => rep w (e v)++ev s e
theorem repVal (w : List Bool) (n : Nat) (t : List Bool) :
    value (rep w n++t)=((word w).rep n).apply (value t) := by
  induction n with
  | zero => simp only [rep,List.nil_append,Word.rep,Word.empty_apply]
  | succ n ih =>
    rw [rep,List.append_assoc,value_append,ih,Word.rep,Word.cat_apply]
    rfl
theorem val_ev (s : LS) (e : Env) : value (ev s e)=BB6.Agent6SymWord.eval (code s) e := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    cases a with
    | lit w =>
      simp only [ev,code,BB6.Agent6SymWord.eval,value_append,ih,word,Word.apply]
    | rep w v =>
      simp only [ev,code,BB6.Agent6SymWord.eval,repVal,ih]
theorem len_rep (w : List Bool) (n : Nat) : (rep w n).length=w.length*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.length_append,ih,Nat.mul_succ]; omega
def lenCoeff : LS → Nat × Nat × Nat
  | [] => (0,0,0)
  | .lit w::s => let (a,b,c):=lenCoeff s; (w.length+a,b,c)
  | .rep w false::s => let (a,b,c):=lenCoeff s; (a,w.length+b,c)
  | .rep w true::s => let (a,b,c):=lenCoeff s; (a,b,w.length+c)
def lengthAt (a : Nat × Nat × Nat) (x y : Nat) := a.1+a.2.1*x+a.2.2*y
theorem len_ev (s : LS) (x y : Nat) : (ev s (env x y)).length=lengthAt (lenCoeff s) x y := by
  induction s with
  | nil => simp [ev,lenCoeff,lengthAt]
  | cons a s ih =>
    cases h : lenCoeff s with
    | mk b c =>
      rcases c with ⟨c,d⟩
      cases a with
      | lit w =>
        simp only [ev,List.length_append,ih,lenCoeff,h,lengthAt]
        omega
      | rep w v =>
        cases v <;> simp only [ev,List.length_append,len_rep,ih,lenCoeff,h,lengthAt,env,Bool.false_eq_true,ite_false,ite_true,Nat.add_mul] <;> omega
theorem value_inj {a b : List Bool} (hl : a.length=b.length) (hv : value a=value b) : a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at hl
    | cons y b =>
      have hh := congrArg head hv
      simp only [value_head,List.headD_cons] at hh
      have ht := congrArg (fun n : Nat => n/2) hv
      simp only [value_tail,List.tail_cons] at ht
      have hlen : a.length=b.length := by simpa using hl
      rw [hh,ih hlen ht]
def same (d : Widths) (a b : LS) : Bool :=
  BB6.Agent6SymWord.same d (code a) (code b) && decide (lenCoeff a=lenCoeff b)
theorem same_sound (d : Widths) (a b : LS) (h : same d a b=true) (x y : Nat) :
    ev a (env x y)=ev b (env x y) := by
  simp only [same,Bool.and_eq_true,decide_eq_true_eq] at h
  apply value_inj
  · rw [len_ev,len_ev,h.2]
  · rw [val_ev,val_ev]
    exact BB6.Agent6SymWord.same_sound d _ _ h.1 x y
structure State where
  q : Fin 6
  l : LS
  r : LS
def State.eval (s : State) (x y : Nat) : Z0 := ⟨s.q,ev s.l (env x y),ev s.r (env x y)⟩
def State.same (d : Widths) (a b : State) : Bool := decide (a.q=b.q) && BB6.Agent6ListSym.same d a.l b.l && BB6.Agent6ListSym.same d a.r b.r
theorem State.same_sound (d : Widths) (a b : State) (h : a.same d b=true) (x y : Nat) : a.eval x y=b.eval x y := by
  simp only [State.same,Bool.and_eq_true,decide_eq_true_eq] at h
  unfold State.eval
  rw [h.1.1,BB6.Agent6ListSym.same_sound d _ _ h.1.2 x y,BB6.Agent6ListSym.same_sound d _ _ h.2 x y]
#print axioms same_sound
#print axioms State.same_sound
end BB6.Agent6ListSym
