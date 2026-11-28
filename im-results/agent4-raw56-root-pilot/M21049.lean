import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw56RootE11LB.M21049
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def O : List Bool := [true,true,true,true]
def D (b : Bool) : List Bool := [true,false,true,b]
def T : List Bool := [false,true,true,true]
def R (n : Nat) : List Bool := false :: (rep O n ++ T)
def G (b : Bool) (L : List Bool) (n : Nat) : Z0 := ⟨0,b::L,R n⟩
def Z (n : Nat) : Z0 := ⟨0,[],R n⟩
def F (L X : List Bool) : Z0 := ⟨5,[true,false] ++ L,X⟩

-- Every fixed local segment preserves arbitrary untouched suffixes.
theorem scan_pre (L X : List Bool) : run0 table 7 ⟨0,false::L,false::(O++X)⟩ = some (F (D true ++ L) X) := rfl
theorem scan_pre_nil (X : List Bool) : run0 table 7 ⟨0,[],false::(O++X)⟩ = some (F (D true) X) := rfl
theorem sweep (L X : List Bool) : run0 table 8 (F L (O++X)) = some (F (D false++L) X) := rfl
theorem finish (L : List Bool) : run0 table 7 (F L T) = some (G false L 0) := rfl

theorem scan_finish (L : List Bool) (n : Nat) :
    run0 table (8*n+7) (F L (rep O n++T)) = some (G false (rep (D false) n++L) 0) := by
  have h := sweepR table 5 [true,false] [] O (D false) 8 (by intro L R; exact sweep L R) n L T
  simp only [List.nil_append] at h
  exact join0 h (finish _)

theorem scan (L : List Bool) (n : Nat) :
    run0 table (7+(8*n+7)) (G false L (n+1)) =
      some (G false (rep (D false) n++D true++L) 0) := by
  have h := join0 (scan_pre L (rep O n++T)) (scan_finish (D true++L) n)
  simpa only [G,R,rep.eq_2,List.append_assoc] using h

theorem scan_nil (n : Nat) :
    run0 table (7+(8*n+7)) (Z (n+1)) =
      some (G false (rep (D false) n++D true) 0) := by
  have h := join0 (scan_pre_nil (rep O n++T)) (scan_finish (D true) n)
  simpa only [Z,R,rep.eq_2,List.append_assoc] using h

theorem flip (L : List Bool) : run0 table 6 (G false L 0) = some (G true L 0) := rfl

theorem pop (b : Bool) (L : List Bool) (n : Nat) :
    run0 table 14 (G true (D b++L) n) = some (G b L (n+1)) := by
  simp only [G,D,R,rep.eq_2,List.cons_append,List.nil_append]
  rfl

theorem pop_short (n : Nat) : run0 table 14 (G true [true,false,true] n) = some (Z (n+1)) := by
  simp only [G,Z,R,rep.eq_2]
  rfl

theorem reset_pre (X : List Bool) :
    run0 table 25 ⟨0,[true],false::(O++X)⟩ = some (F [true,false,true] (O++X)) := rfl

theorem reset (n : Nat) :
    run0 table (25+(8*(n+1)+7)) (G true [] (n+1)) =
      some (G false (rep (D false) (n+1)++[true,false,true]) 0) := by
  have h := join0 (reset_pre (rep O n++T)) (scan_finish [true,false,true] (n+1))
  simpa only [G,R,rep.eq_2,List.append_assoc] using h

inductive Good : List Bool → Prop
  | nil : Good []
  | short : Good [true,false,true]
  | digit (b : Bool) (L : List Bool) : Good L → Good (D b++L)

theorem pad (n : Nat) (L : List Bool) (h : Good L) : Good (rep (D false) n++L) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [rep.eq_2,List.append_assoc] using Good.digit false _ ih

theorem nonempty_pad (n : Nat) (b : Bool) (L : List Bool) : rep (D false) n ++ D b ++ L ≠ [] := by
  simp [D]

inductive Inv : Z0 → Prop
  | z (n : Nat) : Inv (Z (n+1))
  | g (b : Bool) (L : List Bool) (n : Nat) : Good L → (L ≠ [] ∨ 0 < n) → Inv (G b L n)

theorem closed (z : Z0) (h : Inv z) : ∃ k w, 0 < k ∧ run0 table k z = some w ∧ Inv w := by
  cases h with
  | z n => exact ⟨_,_,by omega,scan_nil n,Inv.g false _ 0 (pad n _ (Good.digit true [] Good.nil)) (Or.inl (by simpa using nonempty_pad n true []))⟩
  | g b L n hL hn =>
    cases b with
    | false =>
      cases n with
      | zero => exact ⟨_,_,by decide,flip L,Inv.g true L 0 hL hn⟩
      | succ n =>
        refine ⟨_,_,by omega,scan L n,Inv.g false _ 0 ?_ (Or.inl (nonempty_pad n true L))⟩
        simpa only [List.append_assoc] using pad n _ (Good.digit true L hL)
    | true =>
      cases hL with
      | nil =>
        cases n with
        | zero => simp at hn
        | succ n => exact ⟨_,_,by omega,reset n,Inv.g false _ 0 (pad (n+1) _ Good.short) (Or.inl (by simp))⟩
      | short => exact ⟨_,_,by decide,pop_short n,Inv.z n⟩
      | digit b L hL => exact ⟨_,_,by decide,pop b L n,Inv.g b L (n+1) hL (Or.inr (by omega))⟩

theorem entry : run0 table 74 ⟨0,[],[]⟩ = some (Z 1) := rfl

theorem live (k : Nat) : ∃ t z, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction k with
  | zero => exact ⟨_,_,by omega,entry,Inv.z 0⟩
  | succ k ih =>
    obtain ⟨t,z,ht,hr,hz⟩ := ih
    obtain ⟨u,w,hu,hs,hw⟩ := closed z hz
    exact ⟨t+u,w,by omega,join0 hr hs,hw⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro k
  obtain ⟨t,z,ht,hr,_⟩ := live k
  have hz : (zrun table t start).map project = some z := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some zz =>
    have H := zrun_sound table m hm t start zz h
    rw [start_embed] at H
    rw [show t=k+(t-k) by omega,run_append] at H
    cases he : run m k blank with
    | none => simp [he] at H
    | some c => rfl
theorem cover_never : Cover NeverHalts table := Cover.leaf table never
#print axioms cover_never
#print axioms never
end BB6.Agent4Raw56RootE11LB.M21049
