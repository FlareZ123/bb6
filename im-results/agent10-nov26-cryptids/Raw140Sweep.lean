import Raw140ExtraCore
namespace Raw140Sweep
open BB6BlockFAR Raw140Orbit Raw140Extra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev Stack := List (Sym × Nat)
def expand : Stack → List Sym
  | [] => []
  | (a,n)::xs => List.replicate n a ++ expand xs

def pushN (a : Sym) (n : Nat) (xs : Stack) : Stack :=
  if n == 0 then xs else
  match xs with
  | [] => if a == Sym.zero then [] else [(a,n)]
  | (b,m)::ys => if a == b then (a,n+m)::ys else (a,n)::xs

theorem left_zeros (n : Nat) : leftRay (List.replicate n Sym.zero) = blankRay := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,leftRay,ih]; simp [Sym.zero]
theorem right_zeros (n : Nat) : rightRay (List.replicate n Sym.zero) = blankRay := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,rightRay,ih]; simp [Sym.zero]
theorem boundary_zerosL (q : Q) (d : Bool) (n : Nat) (R : List Sym) :
    boundary q d (List.replicate n Sym.zero) R = boundary q d [] R := by
  cases n with
  | zero => rfl
  | succ n => cases d <;> simp only [boundary,Bool.false_eq_true,ite_false,ite_true,List.replicate_succ,List.headD_cons,List.tail_cons,render,leftRay,left_zeros] <;> simp [Sym.zero,leftRay,rightRay]
theorem boundary_zerosR (q : Q) (d : Bool) (n : Nat) (L : List Sym) :
    boundary q d L (List.replicate n Sym.zero) = boundary q d L [] := by
  cases n with
  | zero => rfl
  | succ n => cases d <;> simp only [boundary,Bool.false_eq_true,ite_false,ite_true,List.replicate_succ,List.headD_cons,List.tail_cons,render,rightRay,right_zeros] <;> simp [Sym.zero,leftRay,rightRay]

theorem expand_pushN (a : Sym) (n : Nat) (xs : Stack) (h : xs ≠ [] ∨ a ≠ Sym.zero) :
    expand (pushN a n xs) = List.replicate n a ++ expand xs := by
  cases n with
  | zero => simp [pushN]
  | succ n =>
    cases xs with
    | nil => have ha : a ≠ Sym.zero := by simpa using h
             simp [pushN,ha,expand]
    | cons p xs =>
      rcases p with ⟨b,m⟩
      by_cases hab : a = b
      · subst b; simp [pushN,expand,← List.replicate_append_replicate,List.append_assoc]
      · simp [pushN,expand,hab]

theorem pushNL (q : Q) (d : Bool) (a : Sym) (n : Nat) (L : Stack) (R : List Sym) :
    boundary q d (expand (pushN a n L)) R = boundary q d (List.replicate n a ++ expand L) R := by
  by_cases h : L ≠ [] ∨ a ≠ Sym.zero
  · rw [expand_pushN a n L h]
  · have hL : L = [] := by exact Classical.byContradiction (fun hn => h (Or.inl hn))
    have ha : a = Sym.zero := by exact Classical.byContradiction (fun hn => h (Or.inr hn))
    subst L; subst a
    cases n <;> simp [pushN,expand,boundary_zerosL]
theorem pushNR (q : Q) (d : Bool) (a : Sym) (n : Nat) (L : List Sym) (R : Stack) :
    boundary q d L (expand (pushN a n R)) = boundary q d L (List.replicate n a ++ expand R) := by
  by_cases h : R ≠ [] ∨ a ≠ Sym.zero
  · rw [expand_pushN a n R h]
  · have hR : R = [] := by exact Classical.byContradiction (fun hn => h (Or.inl hn))
    have ha : a = Sym.zero := by exact Classical.byContradiction (fun hn => h (Or.inr hn))
    subst R; subst a
    cases n <;> simp [pushN,expand,boundary_zerosR]

structure RState where
  q : Q
  d : Bool
  l : Stack
  r : Stack
  deriving DecidableEq, Repr

def RState.prim (s : RState) : Prim := boundary s.q s.d (expand s.l) (expand s.r)

def keep (a : Sym) (n : Nat) (xs : Stack) : Stack := if n == 0 then xs else (a,n)::xs
@[simp] theorem expand_keep (a : Sym) (n : Nat) (xs : Stack) :
    expand (keep a n xs) = List.replicate n a ++ expand xs := by
  cases n <;> simp [keep,expand]

def advR (M : Table) (q : Q) (L : Stack) (a : Sym) (n : Nat) (R : Stack) : Option (Nat × RState) := do
  let e ← blockExit M q true a
  if e.q = q ∧ e.dir = true then
    return ((n+1)*e.steps,⟨q,true,pushN e.w (n+1) L,R⟩)
  else
    let rest := keep a n R
    return (e.steps,if e.dir then ⟨e.q,true,pushN e.w 1 L,rest⟩ else ⟨e.q,false,L,pushN e.w 1 rest⟩)

def advL (M : Table) (q : Q) (L : Stack) (a : Sym) (n : Nat) (R : Stack) : Option (Nat × RState) := do
  let e ← blockExit M q false a
  if e.q = q ∧ e.dir = false then
    return ((n+1)*e.steps,⟨q,false,L,pushN e.w (n+1) R⟩)
  else
    let rest := keep a n L
    return (e.steps,if e.dir then ⟨e.q,true,pushN e.w 1 rest,R⟩ else ⟨e.q,false,rest,pushN e.w 1 R⟩)

theorem advR_sound (M : Table) (q : Q) (L : Stack) (a : Sym) (n : Nat) (R : Stack)
    (c : Nat) (t : RState) (h : advR M q L a n R = some (c,t)) :
    run M c (boundary q true (expand L) (List.replicate (n+1) a ++ expand R)) = some t.prim := by
  cases he : blockExit M q true a with
  | none => simp [advR,he] at h
  | some e =>
    rcases e with ⟨k,q',d',w⟩
    by_cases hs : q' = q ∧ d' = true
    · obtain ⟨rfl,rfl⟩ := hs
      simp [advR,he] at h
      obtain ⟨rfl,rfl⟩ := h
      simpa only [RState.prim,pushNL] using sweepR M q' a w k (n+1) (expand L) (expand R) he
    · cases d' <;> simp [advR,he,hs] at h
      · obtain ⟨rfl,rfl⟩ := h
        simpa only [RState.prim,pushNR,expand_keep,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,List.replicate_one,List.singleton_append,Bool.false_eq_true,ite_false] using
          stepR M q q' false a w k (expand L) (List.replicate n a ++ expand R) he
      · have hn : q' ≠ q := fun hq => hs ⟨hq,rfl⟩
        simp [hn] at h
        obtain ⟨rfl,rfl⟩ := h
        simpa only [RState.prim,pushNL,expand_keep,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,List.replicate_one,List.singleton_append,ite_true] using
          stepR M q q' true a w k (expand L) (List.replicate n a ++ expand R) he

theorem advL_sound (M : Table) (q : Q) (L : Stack) (a : Sym) (n : Nat) (R : Stack)
    (c : Nat) (t : RState) (h : advL M q L a n R = some (c,t)) :
    run M c (boundary q false (List.replicate (n+1) a ++ expand L) (expand R)) = some t.prim := by
  cases he : blockExit M q false a with
  | none => simp [advL,he] at h
  | some e =>
    rcases e with ⟨k,q',d',w⟩
    by_cases hs : q' = q ∧ d' = false
    · obtain ⟨rfl,rfl⟩ := hs
      simp [advL,he] at h
      obtain ⟨rfl,rfl⟩ := h
      simpa only [RState.prim,pushNR] using sweepL M q' a w k (n+1) (expand L) (expand R) he
    · cases d' <;> simp [advL,he,hs] at h
      · have hn : q' ≠ q := fun hq => hs ⟨hq,rfl⟩
        simp [hn] at h
        obtain ⟨rfl,rfl⟩ := h
        simpa only [RState.prim,pushNR,expand_keep,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,List.replicate_one,List.singleton_append,Bool.false_eq_true,ite_false] using
          stepL M q q' false a w k (List.replicate n a ++ expand L) (expand R) he
      · obtain ⟨rfl,rfl⟩ := h
        simpa only [RState.prim,pushNL,expand_keep,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,List.replicate_one,List.singleton_append,ite_true] using
          stepL M q q' true a w k (List.replicate n a ++ expand L) (expand R) he

def advance (M : Table) (s : RState) : Option (Nat × RState) :=
  if s.d then
    match s.r with
    | [] => advR M s.q s.l Sym.zero 0 []
    | (_,0)::_ => none
    | (a,n+1)::R => advR M s.q s.l a n R
  else
    match s.l with
    | [] => advL M s.q [] Sym.zero 0 s.r
    | (_,0)::_ => none
    | (a,n+1)::L => advL M s.q L a n s.r

theorem advance_sound (M : Table) (s t : RState) (n : Nat) (h : advance M s = some (n,t)) :
    run M n s.prim = some t.prim := by
  rcases s with ⟨q,d,L,R⟩
  cases d
  · cases L with
    | nil => simpa [advance,RState.prim,expand,left_zero] using advL_sound M q [] Sym.zero 0 R n t h
    | cons p L => rcases p with ⟨a,k⟩; cases k with
      | zero => simp [advance] at h
      | succ k => exact advL_sound M q L a k R n t h
  · cases R with
    | nil => simpa [advance,RState.prim,expand,right_zero] using advR_sound M q L Sym.zero 0 [] n t h
    | cons p R => rcases p with ⟨a,k⟩; cases k with
      | zero => simp [advance] at h
      | succ k => exact advR_sound M q L a k R n t h

def execute (M : Table) : Nat → RState → Option (Nat × RState)
  | 0,s => some (0,s)
  | k+1,s => do
    let (a,u) ← advance M s
    let (b,t) ← execute M k u
    return (a+b,t)

theorem execute_sound (M : Table) (k n : Nat) (s t : RState) (h : execute M k s = some (n,t)) :
    run M n s.prim = some t.prim := by
  induction k generalizing s n with
  | zero => simp [execute] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | succ k ih =>
    simp only [execute] at h
    cases he : advance M s with
    | none => rw [he] at h; contradiction
    | some p =>
      rcases p with ⟨a,u⟩
      cases hg : execute M k u with
      | none => simp [he,hg] at h
      | some p =>
        rcases p with ⟨b,w⟩
        simp [he,hg] at h
        obtain ⟨rfl,rfl⟩ := h
        exact join (advance_sound M s u a he) (ih b u hg)

#print axioms execute_sound
end Raw140Sweep
