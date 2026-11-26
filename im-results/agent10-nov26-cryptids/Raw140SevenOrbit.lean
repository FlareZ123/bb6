import Raw140OrbitPhases
namespace Raw140Orbit
open BB6BlockFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def variant (v : Fin 7) : Table := fun q b =>
  match base q b with
  | some m => some m
  | none =>
    if q == 0 && b then some ⟨v.val >= 3,true,5⟩
    else if q == 5 && !b then
      ([⟨false,false,1⟩,⟨false,false,2⟩,⟨false,true,0⟩,
         ⟨false,false,4⟩,⟨true,false,1⟩,⟨true,true,0⟩,⟨true,true,3⟩] : List Move)[v.val]?
    else none

theorem variant_extends (v : Fin 7) (q : Q) (b : Bool) (m : Move) (h : base q b = some m) : variant v q b = some m := by
  simp [variant,h]

theorem step_extend (v : Fin 7) (c c' : Prim) (h : primStep base c = some c') : primStep (variant v) c = some c' := by
  cases hm : base c.q (c.r 0) with
  | none => simp [primStep,hm] at h
  | some m => simpa [primStep,hm,variant_extends v _ _ _ hm] using h

theorem run_extend (v : Fin 7) (n : Nat) (c c' : Prim) (h : run base n c = some c') : run (variant v) n c = some c' := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    rw [run] at h ⊢
    cases hm : primStep base c with
    | none => simp [hm] at h
    | some d => simp only [hm,Option.bind_some] at h; rw [step_extend v c d hm]; exact ih d h

theorem growth (v : Fin 7) (n : Nat) : run (variant v) (36*n+198) (familyA n) = some (familyA (n+6)) := by
  have h := join (phaseA n) (phaseB (n+3))
  rw [show (18*n+62)+(18*(n+3)+82)=36*n+198 by omega, show n+3+3=n+6 by omega] at h
  exact run_extend v _ _ _ h

def push (a : Sym) (xs : List Sym) : List Sym := if xs.isEmpty && a == Sym.zero then [] else a::xs

theorem pushL (q : Q) (d : Bool) (a : Sym) (L R : List Sym) : boundary q d (push a L) R = boundary q d (a::L) R := by
  cases L with
  | nil => by_cases h : a = Sym.zero
           · subst a; simpa [push] using (left_zero q d R).symm
           · simp [push,h]
  | cons b L => rfl

theorem pushR (q : Q) (d : Bool) (a : Sym) (L R : List Sym) : boundary q d L (push a R) = boundary q d L (a::R) := by
  cases R with
  | nil => by_cases h : a = Sym.zero
           · subst a; simpa [push] using (right_zero q d L).symm
           · simp [push,h]
  | cons b R => rfl

structure BState where
  q : Q
  d : Bool
  l : List Sym
  r : List Sym
  deriving DecidableEq, Repr

def BState.prim (s : BState) : Prim := boundary s.q s.d s.l s.r

def advance (M : Table) (s : BState) : Option (Nat × BState) := do
  let a := if s.d then s.r.headD Sym.zero else s.l.headD Sym.zero
  let l := if s.d then s.l else s.l.tail
  let r := if s.d then s.r.tail else s.r
  let e ← blockExit M s.q s.d a
  return (e.steps, if e.dir then ⟨e.q,true,push e.w l,r⟩ else ⟨e.q,false,l,push e.w r⟩)

theorem advance_sound (M : Table) (s t : BState) (n : Nat) (h : advance M s = some (n,t)) : run M n s.prim = some t.prim := by
  rcases s with ⟨q,d,L,R⟩
  cases d with
  | false =>
    simp only [advance, Bool.false_eq_true, ite_false] at h
    cases he : blockExit M q false (L.headD Sym.zero) with
    | none => rw [he] at h; contradiction
    | some e =>
      rcases e with ⟨k,q',d',w⟩
      rw [he] at h
      change some (_,_) = some (n,t) at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have H := stepL M q q' d' (L.headD Sym.zero) w k L.tail R he
      cases L <;> cases d' <;> simpa [BState.prim,left_zero,pushL,pushR] using H
  | true =>
    simp only [advance, ite_true] at h
    cases he : blockExit M q true (R.headD Sym.zero) with
    | none => rw [he] at h; contradiction
    | some e =>
      rcases e with ⟨k,q',d',w⟩
      rw [he] at h
      change some (_,_) = some (n,t) at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have H := stepR M q q' d' (R.headD Sym.zero) w k L R.tail he
      cases R <;> cases d' <;> simpa [BState.prim,right_zero,pushL,pushR] using H

def execute (M : Table) : Nat → BState → Option (Nat × BState)
  | 0,s => some (0,s)
  | k+1,s => do
    let (a,u) ← advance M s
    let (b,t) ← execute M k u
    return (a+b,t)

theorem execute_sound (M : Table) (k n : Nat) (s t : BState) (h : execute M k s = some (n,t)) : run M n s.prim = some t.prim := by
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

end Raw140Orbit
