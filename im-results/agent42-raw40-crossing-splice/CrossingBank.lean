import CrossingCore
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42Crossing
open BB6Coverage Agent50Zipper

instance validDec (p : PartialMachine) (out mark b : Bool) (m : Mode) (es : List Ev) :
    Decidable (valid p out mark b m es) :=
  match es, m with
  | [], .active q => by simp only [valid]; infer_instance
  | [], .idle d => by simp only [valid]; infer_instance
  | e::es, .active q => by
    simp only [valid]
    letI := validDec p out mark e.write (.idle e.right) es
    infer_instance
  | e::es, .idle d => by
    simp only [valid]
    letI := validDec p out mark b (.active e.q) es
    infer_instance
termination_by structural es

instance localDec (p : PartialMachine) (c : Cell) (m : Mode) : Decidable (localOK p c m) :=
  validDec p c.out c.mark c.bit m c.events

instance chainDec (p : PartialMachine) (d : Bool) (a : List (Bool × Fin 6))
    (xs : List Cell) (b : List (Bool × Fin 6)) : Decidable (chain p d a xs b) :=
  match xs with
  | [] => by simp only [chain]; infer_instance
  | c::cs => by
    simp only [chain]
    letI := chainDec p d (edge c d) cs b
    infer_instance
termination_by structural xs

structure Segment where
  cells : List Cell
  pump : Bool
  exit : List (Bool × Fin 6)
  deriving Repr

def expand (n : Nat) : List Segment → List Cell
  | [] => []
  | s::ss => (if s.pump then copies s.cells (n+1) else s.cells) ++ expand n ss

def segOK (p : PartialMachine) (a : List (Bool × Fin 6)) : List Segment → Prop
  | [] => a = []
  | s::ss => chain p true a s.cells s.exit ∧ (s.pump = true → a = s.exit) ∧ segOK p s.exit ss

instance segDec (p : PartialMachine) (a : List (Bool × Fin 6)) (ss : List Segment) :
    Decidable (segOK p a ss) :=
  match ss with
  | [] => by simp only [segOK]; infer_instance
  | s::ss => by
    simp only [segOK]
    letI := segDec p s.exit ss
    infer_instance
termination_by structural ss

theorem expanded_chain (p : PartialMachine) (a : List (Bool × Fin 6)) (ss : List Segment)
    (hs : segOK p a ss) (n : Nat) : chain p true a (expand n ss) [] := by
  induction ss generalizing a with
  | nil => exact hs
  | cons s ss ih =>
    simp only [segOK] at hs
    simp only [expand]
    apply chain_append p true a s.exit [] _ _ _ (ih _ hs.2.2)
    split
    · rename_i he
      have heq := hs.2.1 he
      rw [← heq] at hs ⊢
      exact chain_copies p true a s.cells hs.1 (n+1)
    · exact hs.1

structure Certificate where
  left : List Cell
  head : Cell
  right : List Segment
  deriving Repr

def certOK (p : PartialMachine) (c : Certificate) : Prop :=
  localOK p c.head (.active 0) ∧ chain p false (edge c.head false) c.left [] ∧
    segOK p (edge c.head true) c.right

instance certDec (p : PartialMachine) (c : Certificate) : Decidable (certOK p c) := by
  unfold certOK; infer_instance

def script (c : Certificate) (h : Int) (n : Nat) : ScriptZ := ⟨0,h,c.left,c.head,expand n c.right⟩

theorem script_ok (p : PartialMachine) (c : Certificate) (hc : certOK p c) (h : Int) (n : Nat) :
    ok p (script c h n) := ⟨hc.1,hc.2.1,expanded_chain p _ _ hc.2.2 n⟩

-- Exact power-word normalization, independently of the machine.
structure WordExpr where
  terms : List (List Bool × List Bool)
  tail : List Bool
  deriving DecidableEq, Repr

def wordEval (n : Nat) (w : WordExpr) : List Bool :=
  (w.terms.flatMap fun (pre,b) => pre ++ copies b n) ++ w.tail

def slide (preRev block tail : List Bool) : List Bool × List Bool × List Bool :=
  match preRev with
  | [] => ([],block,tail)
  | x::xs =>
    match block.reverse with
    | [] => ((x::xs).reverse,block,tail)
    | y::ys => if x = y then slide xs (x::ys.reverse) (x::tail)
        else ((x::xs).reverse,block,tail)

theorem rotate_copies (x : Bool) (v : List Bool) (n : Nat) :
    [x] ++ copies (v++[x]) n = copies (x::v) n ++ [x] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copies,List.append_assoc]
    have h : [x] ++ v ++ ([x] ++ copies (v++[x]) n) =
        [x] ++ v ++ (copies (x::v) n ++ [x]) := by rw [ih]
    simpa [List.append_assoc] using h

theorem slide_sound (preRev block tail : List Bool) (n : Nat) :
    let (a,b,c) := slide preRev block tail
    preRev.reverse ++ copies block n ++ tail = a ++ copies b n ++ c := by
  induction preRev generalizing block tail with
  | nil => rfl
  | cons x xs ih =>
    cases hb : block.reverse with
    | nil => simp [slide,hb]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        have hb' : block = ys.reverse ++ [x] := by
          simpa using congrArg List.reverse hb
        have H := ih (x::ys.reverse) (x::tail)
        have eq : (x::xs).reverse ++ copies block n ++ tail =
            xs.reverse ++ copies (x::ys.reverse) n ++ (x::tail) := by
          rw [hb',List.reverse_cons]
          rw [List.append_assoc xs.reverse [x],rotate_copies]
          simp [List.append_assoc]
        rw [eq]
        simpa [slide,hb,List.append_assoc] using H
      · simp [slide,hb,hxy]

def normalize (f : Cell → Bool) (extra : Nat) (acc : List Bool) : List Segment → WordExpr
  | [] => ⟨[],acc⟩
  | s::ss =>
    let b := s.cells.map f
    if s.pump then
      let (pre,block,tail) := slide (acc ++ copies b (extra+1)).reverse b []
      let rest := normalize f extra tail ss
      ⟨(pre,block)::rest.terms,rest.tail⟩
    else normalize f extra (acc++b) ss

theorem copies_add {α : Type} (b : List α) (n k : Nat) : copies b (n+k) = copies b n ++ copies b k := by
  induction n with
  | zero => simp [copies]
  | succ n ih => rw [show n+1+k=n+k+1 by omega,copies,ih]; simp [copies,List.append_assoc]

theorem map_copies {α β : Type} (f : α → β) (b : List α) (n : Nat) :
    (copies b n).map f = copies (b.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copies,ih]

theorem normalize_sound (f : Cell → Bool) (extra n : Nat) (acc : List Bool) (ss : List Segment) :
    wordEval n (normalize f extra acc ss) = acc ++ (expand (extra+n) ss).map f := by
  induction ss generalizing acc with
  | nil => simp [normalize,wordEval,expand]
  | cons s ss ih =>
    cases hp : s.pump with
    | false =>
      simp [normalize,expand,hp,ih,List.append_assoc]
    | true =>
      let b := s.cells.map f
      cases hs : slide (acc ++ copies b (extra+1)).reverse b [] with
      | mk pre pair =>
        rcases pair with ⟨block,tail⟩
        have H := slide_sound (acc ++ copies b (extra+1)).reverse b [] n
        rw [hs] at H
        simp only [List.reverse_reverse,List.append_nil] at H
        have hrest := ih tail
        simp only [normalize,hp,if_true,show s.cells.map f=b from rfl,hs,wordEval,List.flatMap_cons]
        have H' : pre ++ copies block n ++ (wordEval n (normalize f extra tail ss)) =
            acc ++ copies b (extra+n+1) ++ (expand (extra+n) ss).map f := by
          rw [hrest,← List.append_assoc,← H]
          rw [show extra+n+1=extra+1+n by omega,copies_add b (extra+1) n]
          simp [List.append_assoc]
        simpa only [wordEval,expand,hp,if_true,List.map_append,map_copies,List.append_assoc] using H'

#print axioms normalize_sound

-- Equality of finite words padded with zero forever.
def padEq : List Bool → List Bool → Bool
  | [], ys => ys.all (!·)
  | x::xs, [] => !x && padEq xs []
  | x::xs, y::ys => (x == y) && padEq xs ys

theorem zeros_getD (ys : List Bool) (h : ys.all (!·) = true) (i : Nat) : ys.getD i false = false := by
  induction ys generalizing i with
  | nil => simp
  | cons y ys ih =>
    simp only [List.all_cons,Bool.and_eq_true,Bool.not_eq_true'] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa only [List.getD_cons_succ] using ih h.2 i

theorem padEq_sound (xs ys : List Bool) (h : padEq xs ys = true) (i : Nat) :
    xs.getD i false = ys.getD i false := by
  induction xs generalizing ys i with
  | nil => simpa only [List.getD_nil] using (zeros_getD ys h i).symm
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [padEq, Bool.and_eq_true, Bool.not_eq_true'] at h
      cases i with
      | zero => simpa using h.1
      | succ i => exact ih [] h.2 i
    | cons y ys =>
      simp only [padEq,Bool.and_eq_true,beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i => exact ih ys h.2 i

theorem append_getD (pre a b : List Bool) (h : ∀ i, a.getD i false = b.getD i false) (i : Nat) :
    (pre++a).getD i false = (pre++b).getD i false := by
  induction pre generalizing i with
  | nil => exact h i
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

def exprEq (a b : WordExpr) : Prop := a.terms = b.terms ∧ padEq a.tail b.tail = true

instance exprDec (a b : WordExpr) : Decidable (exprEq a b) := by
  unfold exprEq; infer_instance

theorem exprEq_sound (a b : WordExpr) (he : exprEq a b) (n i : Nat) :
    (wordEval n a).getD i false = (wordEval n b).getD i false := by
  unfold wordEval
  rw [he.1]
  exact append_getD _ _ _ (padEq_sound _ _ he.2) i

def fixedGoal (c : Certificate) : Option Z :=
  finished (-(c.left.length : Int)) [] (c.left.reverse.map marked ++ [marked c.head])

theorem finished_append (base : Int) (acc : List Bool) (xs ys : List (Bool × Bool)) (f : Z)
    (h : finished base acc xs = some f) :
    finished base acc (xs++ys) = some {f with r := f.r ++ ys.map Prod.fst} := by
  induction xs generalizing acc f with
  | nil => simp [finished] at h
  | cons x xs ih =>
    rcases x with ⟨b,m⟩
    cases m with
    | false =>
      simp only [finished,Bool.false_eq_true,ite_false] at h
      simp only [List.cons_append,finished,Bool.false_eq_true,ite_false]
      exact ih _ _ h
    | true =>
      simp only [finished,ite_true,Option.some.injEq] at h
      subst f
      simp [finished]

theorem finished_shift (base h : Int) (acc : List Bool) (xs : List (Bool × Bool)) :
    finished (base+h) acc xs = (finished base acc xs).map (fun f => {f with h := f.h+h}) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b,m⟩
    cases m with
    | false => exact ih (b::acc)
    | true => simp [finished]; omega

theorem goal_script (c : Certificate) (f : Z) (hf : fixedGoal c = some f) (h : Int) (n : Nat) :
    goal (script c h n) = some {f with h := f.h+h, r := f.r ++ (expand n c.right).map Cell.out} := by
  have h1 := finished_append (-(c.left.length : Int)) [] _ ((expand n c.right).map marked) f hf
  have h2 := finished_shift (-(c.left.length : Int)) h []
    ((c.left.reverse.map marked ++ [marked c.head]) ++ (expand n c.right).map marked)
  rw [h1] at h2
  have hmap : ((expand n c.right).map marked).map Prod.fst = (expand n c.right).map Cell.out := by
    simp [List.map_map,marked,Function.comp_def]
  simpa [goal,script,origin,finalWord,List.append_assoc,hmap,show h-(c.left.length : Int)=-(c.left.length : Int)+h by omega] using h2

#print axioms exprEq_sound
#print axioms goal_script
end BB6Coverage.Agent42Crossing
