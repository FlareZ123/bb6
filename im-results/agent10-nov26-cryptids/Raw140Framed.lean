import Raw140ExtraCore
namespace Raw140Framed
open BB6BlockFAR Raw140Orbit Raw140Extra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

/-- Prefixes are finite; an open side is followed by an arbitrary frame.
    Reading across an open frame boundary is rejected. -/
def prim (oL oR : Bool) (s : BState) (X Y : List Sym) : Prim :=
  boundary s.q s.d (s.l ++ if oL then X else []) (s.r ++ if oR then Y else [])

def fpush (o : Bool) (b : Sym) (l : List Sym) : List Sym :=
  if o then b::l else push b l

def advance (M : Table) (oL oR : Bool) (s : BState) : Option (Nat × BState) := do
  if (if s.d then oR && s.r.isEmpty else oL && s.l.isEmpty) then none else
    let a := if s.d then s.r.headD Sym.zero else s.l.headD Sym.zero
    let l := if s.d then s.l else s.l.tail
    let r := if s.d then s.r.tail else s.r
    let e ← blockExit M s.q s.d a
    return (e.steps, if e.dir then ⟨e.q,true,fpush oL e.w l,r⟩ else ⟨e.q,false,l,fpush oR e.w r⟩)

theorem fpushL (o : Bool) (q : Q) (d : Bool) (b : Sym) (L X R : List Sym) :
    boundary q d ((fpush o b L) ++ (if o then X else [])) R =
      boundary q d (b::(L ++ (if o then X else []))) R := by
  cases o <;> simp [fpush,pushL]

theorem fpushR (o : Bool) (q : Q) (d : Bool) (b : Sym) (R Y L : List Sym) :
    boundary q d L ((fpush o b R) ++ (if o then Y else [])) =
      boundary q d L (b::(R ++ (if o then Y else []))) := by
  cases o <;> simp [fpush,pushR]

theorem advance_sound (M : Table) (oL oR : Bool) (s t : BState) (n : Nat) (X Y : List Sym)
    (h : advance M oL oR s = some (n,t)) :
    run M n (prim oL oR s X Y) = some (prim oL oR t X Y) := by
  rcases s with ⟨q,d,L,R⟩
  cases d with
  | false =>
    simp only [advance,Bool.false_eq_true,ite_false] at h
    split at h
    · contradiction
    · rename_i hguard
      cases he : blockExit M q false (L.headD Sym.zero) with
      | none => rw [he] at h; contradiction
      | some e =>
        rcases e with ⟨k,q',d',b⟩
        rw [he] at h
        change some (_,_) = some (n,t) at h
        simp only [Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        have H := stepL M q q' d' (L.headD Sym.zero) b k
          (L.tail ++ if oL then X else []) (R ++ if oR then Y else []) he
        have hl : boundary q false (L.headD Sym.zero::(L.tail ++ if oL then X else [])) (R ++ if oR then Y else []) =
            boundary q false (L ++ if oL then X else []) (R ++ if oR then Y else []) := by
          cases L with
          | nil => cases oL <;> simp [left_zero] at hguard ⊢
          | cons a L => rfl
        rw [hl] at H
        cases d' <;> simpa only [prim,ite_true,ite_false,Bool.false_eq_true,fpushL,fpushR] using H
  | true =>
    simp only [advance,ite_true] at h
    split at h
    · contradiction
    · rename_i hguard
      cases he : blockExit M q true (R.headD Sym.zero) with
      | none => rw [he] at h; contradiction
      | some e =>
        rcases e with ⟨k,q',d',b⟩
        rw [he] at h
        change some (_,_) = some (n,t) at h
        simp only [Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        have H := stepR M q q' d' (R.headD Sym.zero) b k
          (L ++ if oL then X else []) (R.tail ++ if oR then Y else []) he
        have hr : boundary q true (L ++ if oL then X else []) (R.headD Sym.zero::(R.tail ++ if oR then Y else [])) =
            boundary q true (L ++ if oL then X else []) (R ++ if oR then Y else []) := by
          cases R with
          | nil => cases oR <;> simp [right_zero] at hguard ⊢
          | cons a R => rfl
        rw [hr] at H
        cases d' <;> simpa only [prim,ite_true,ite_false,Bool.false_eq_true,fpushL,fpushR] using H

def execute (M : Table) (oL oR : Bool) : Nat → BState → Option (Nat × BState)
  | 0,s => some (0,s)
  | k+1,s => do
    let (a,u) ← advance M oL oR s
    let (b,t) ← execute M oL oR k u
    return (a+b,t)

theorem execute_sound (M : Table) (oL oR : Bool) (k n : Nat) (s t : BState) (X Y : List Sym)
    (h : execute M oL oR k s = some (n,t)) :
    run M n (prim oL oR s X Y) = some (prim oL oR t X Y) := by
  induction k generalizing s n with
  | zero => simp [execute] at h; obtain ⟨rfl,rfl⟩ := h; simp [run]
  | succ k ih =>
    simp only [execute] at h
    cases he : advance M oL oR s with
    | none => rw [he] at h; contradiction
    | some p =>
      rcases p with ⟨a,u⟩
      cases hg : execute M oL oR k u with
      | none => simp [he,hg] at h
      | some p =>
        rcases p with ⟨b,w⟩
        simp [he,hg] at h
        obtain ⟨rfl,rfl⟩ := h
        exact join (advance_sound M oL oR s u a X Y he) (ih b u hg)

#print axioms execute_sound
end Raw140Framed
