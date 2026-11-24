import RootShift
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent50Zipper
open BB6Coverage

/-- The left list includes the scanned cell; both lists are padded with zero. -/
structure Z where
  q : Fin 6
  h : Int
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def atCell (z : Z) (x : Int) : Bool :=
  if x ≤ z.h then z.l.getD (z.h-x).toNat false
  else z.r.getD (x-z.h-1).toNat false

def embed (z : Z) : Config := ⟨z.q,z.h,atCell z⟩

def move (mv : Move) (z : Z) : Z :=
  if mv.right then
    ⟨mv.next,z.h+1,z.r.headD false::mv.write::z.l.tail,z.r.tail⟩
  else
    ⟨mv.next,z.h-1,z.l.tail,mv.write::z.r⟩

def step (p : PartialMachine) (z : Z) : Option Z :=
  ((p (z.q,z.l.headD false)).bind id).map (fun mv => move mv z)

def zrun (p : PartialMachine) : Nat → Z → Option Z
  | 0,z => some z
  | n+1,z => (step p z).bind (zrun p n)

theorem getD_tail (l : List Bool) (n : Nat) :
    l.tail.getD n false = l.getD (n+1) false := by
  cases l <;> rfl

theorem headD_getD (l : List Bool) : l.headD false = l.getD 0 false := by
  cases l <;> rfl

theorem read_embed (z : Z) : readSlot (embed z) = (z.q,z.l.headD false) := by
  change (z.q, atCell z z.h) = _
  simp only [atCell, Int.le_refl, ite_true, Int.sub_self, Int.toNat_zero, headD_getD]

theorem atCell_move (mv : Move) (z : Z) (x : Int) :
    atCell (move mv z) x = if x = z.h then mv.write else atCell z x := by
  cases hr : mv.right with
  | false =>
    simp only [move,hr,Bool.false_eq_true,ite_false,atCell]
    by_cases hlt : x < z.h
    · have ha : x ≤ z.h-1 := by omega
      have hb : x ≤ z.h := by omega
      have hn : x ≠ z.h := by omega
      have hi : (z.h-1-x).toNat+1 = (z.h-x).toNat := by omega
      simp [ha,hb,hn,getD_tail,hi]
    · by_cases he : x = z.h
      · subst x; have hnot : ¬z.h ≤ z.h-1 := by omega
        simp [hnot,show (z.h-(z.h-1)-1).toNat=0 by omega]
      · have ha : ¬x ≤ z.h-1 := by omega
        have hb : ¬x ≤ z.h := by omega
        have hi : (x-(z.h-1)-1).toNat = (x-z.h-1).toNat+1 := by omega
        simp [ha,hb,he,hi]
  | true =>
    simp only [move,hr,ite_true,atCell]
    by_cases hlt : x < z.h
    · have ha : x ≤ z.h+1 := by omega
      have hb : x ≤ z.h := by omega
      have hn : x ≠ z.h := by omega
      have hi : (z.h+1-x).toNat = ((z.h-x).toNat-1)+2 := by omega
      have hj : (z.h-x).toNat-1+1 = (z.h-x).toNat := by omega
      rw [if_pos ha,if_neg hn,if_pos hb,hi,show ((z.h-x).toNat-1)+2=((z.h-x).toNat-1)+1+1 by omega]
      rw [List.getD_cons_succ,List.getD_cons_succ,getD_tail,hj]
    · by_cases he : x = z.h
      · subst x
        have hle : z.h ≤ z.h+1 := by omega
        simp [hle,show (z.h+1-z.h).toNat=1 by omega]
      · by_cases he' : x = z.h+1
        · subst x
          have hnot : ¬z.h+1 ≤ z.h := by omega
          have hne : z.h+1 ≠ z.h := by omega
          rw [if_pos (Int.le_refl _),if_neg hne,if_neg hnot]
          rw [show (z.h+1-(z.h+1)).toNat=0 by omega,show (z.h+1-z.h-1).toNat=0 by omega,List.getD_cons_zero,headD_getD]
        · have ha : ¬x ≤ z.h+1 := by omega
          have hb : ¬x ≤ z.h := by omega
          have hi : (x-(z.h+1)-1).toNat+1 = (x-z.h-1).toNat := by omega
          rw [if_neg ha,if_neg he,if_neg hb,getD_tail,hi]

theorem embed_move (mv : Move) (z : Z) :
    embed (move mv z) = applyMove (embed z) mv := by
  have hs : (move mv z).q = mv.next := by cases hr : mv.right <;> simp [move,hr]
  have hh : (move mv z).h = z.h + (if mv.right then 1 else -1) := by
    cases hr : mv.right <;> simp [move,hr] <;> omega
  unfold embed applyMove
  rw [hs,hh]
  congr 1
  exact funext (atCell_move mv z)

theorem step_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (z z' : Z) (hs : step p z = some z') : rawStep m (embed z) = some (embed z') := by
  unfold step at hs
  cases hp : p (z.q,z.l.headD false) with
  | none => simp only [hp,Option.bind_none,Option.map_none,Option.some.injEq] at hs <;> contradiction
  | some tr =>
    cases tr with
    | none => simp only [hp,Option.bind_some,id,Option.map_none,Option.some.injEq] at hs <;> contradiction
    | some mv =>
      have hz : move mv z = z' := by simpa only [hp,Option.bind_some,id,Option.map_some,Option.some.injEq] using hs
      subst z'
      rw [rawStep,read_embed,hm _ _ hp]
      simp [embed_move]

theorem zrun_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (n : Nat) (z z' : Z) (hs : zrun p n z = some z') :
    run m n (embed z) = some (embed z') := by
  induction n generalizing z with
  | zero =>
    have h : z = z' := Option.some.inj hs
    subst z'; rfl
  | succ n ih =>
    cases hz : step p z with
    | none => simp [zrun,hz] at hs
    | some t =>
      have ht : zrun p n t = some z' := by simpa [zrun,hz] using hs
      have hfirst := step_sound p m hm z t hz
      have htail := ih t ht
      rw [show n+1=1+n by omega,run_append]
      have hstep : run m 1 (embed z) = some (embed t) := by simpa [run] using hfirst
      rw [hstep]; exact htail

theorem zrun_add (p : PartialMachine) (n k : Nat) (z : Z) :
    zrun p (n+k) z = (zrun p n z).bind (zrun p k) := by
  induction n generalizing z with
  | zero => simp [zrun]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [zrun]
    cases step p z with
    | none => rfl
    | some t => exact ih t

theorem join {p : PartialMachine} {n k : Nat} {a b c : Z}
    (h : zrun p n a = some b) (g : zrun p k b = some c) :
    zrun p (n+k) a = some c := by
  rw [zrun_add,h]; exact g

def shift (x : Int) (z : Z) : Z := {z with h := z.h+x}

theorem move_shift (mv : Move) (x : Int) (z : Z) :
    move mv (shift x z) = shift x (move mv z) := by
  cases z
  cases mv
  rename_i w r q
  cases r <;> simp [move,shift] <;> omega

theorem step_shift (p : PartialMachine) (x : Int) (z : Z) :
    step p (shift x z) = (step p z).map (shift x) := by
  change ((p (z.q,z.l.headD false)).bind id).map (fun mv => move mv (shift x z)) =
    (((p (z.q,z.l.headD false)).bind id).map (fun mv => move mv z)).map (shift x)
  cases h : (p (z.q,z.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [move_shift]

theorem zrun_shift (p : PartialMachine) (x : Int) (n : Nat) (z : Z) :
    zrun p n (shift x z) = (zrun p n z).map (shift x) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [zrun,step_shift]
    cases step p z with
    | none => rfl
    | some t => exact ih t

#print axioms zrun_sound
end BB6Coverage.Agent50Zipper
