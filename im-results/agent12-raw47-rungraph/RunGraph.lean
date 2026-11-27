import Counter286Bridge
import MaskMap
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12RunGraph
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent32MaskBiDFA
open Counter286 (Ray cons tail pre nilRay)
open BB6.Agent12Counter286 (observe moveC observe_move observed_slot)

structure Graph where
  delta : Map Nat
  incoming : Map (List (Bool × Nat))

def push (g : Graph) (x : Nat) (b : Bool) : Nat := (g.delta.lookup (2*x+b.toNat)).getD 0
def preds (g : Graph) (x : Nat) : List (Bool × Nat) := (g.incoming.lookup x).getD []
def edge (g : Graph) (x : Nat) (b : Bool) (y : Nat) : Bool := decide ((b,y) ∈ preds g x)
def summary (g : Graph) : List Bool → Nat
  | [] => 0
  | b::w => push g (summary g w) b

def TapeOK (g : Graph) : List Bool → Prop
  | [] => (false,0) ∈ preds g 0
  | b::w => (b,summary g w) ∈ preds g (summary g (b::w)) ∧ TapeOK g w

theorem pop_edge {g w} (h : TapeOK g w) :
    (w.headD false,summary g w.tail) ∈ preds g (summary g w) := by
  cases w with
  | nil => exact h
  | cons b w => exact h.1

theorem pop_ok {g w} (h : TapeOK g w) : TapeOK g w.tail := by
  cases w with
  | nil => exact h
  | cons b w => exact h.2

theorem push_ok {g w b} (h : TapeOK g w)
    (he : edge g (push g (summary g w) b) b (summary g w) = true) : TapeOK g (b::w) :=
  ⟨of_decide_eq_true he,h⟩

structure Cert where
  left : Graph
  right : Graph
  rows : Array (Map Cell)

def row (c : Cert) (q : Fin 6) (a : Bool) : Map Cell := c.rows.getD (2*q.val+a.toNat) .empty
def cell (c : Cert) (q : Fin 6) (a : Bool) (l : Nat) : Cell := ((row c q a).lookup l).getD ⟨0,[]⟩
def stateOK (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool := (cell c q a l).mask.testBit r
def stepOK (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  match p (q,a) with
  | some (some m) =>
    if m.right then
      edge c.left (push c.left l m.write) m.write l &&
        (preds c.right r).all (fun e => stateOK c m.next e.1 (push c.left l m.write) e.2)
    else
      edge c.right (push c.right r m.write) m.write r &&
        (preds c.left l).all (fun e => stateOK c m.next e.1 e.2 (push c.right r m.write))
  | _ => false

def cellCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (l : Nat) (v : Cell) : Bool :=
  subset v.mask (listMask v.indices) && v.indices.all (fun r => stepOK p c q a l r)

def rowCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) : Bool :=
  (row c q a).all (cellCheck p c q a)

def check (p : PartialMachine) (c : Cert) : Bool :=
  edge c.left 0 false 0 && edge c.right 0 false 0 && stateOK c 0 false 0 0 &&
    (List.finRange 6).all (fun q => rowCheck p c q false && rowCheck p c q true)

theorem state_checked {p c q a l r} (h : check p c = true)
    (hs : stateOK c q a l r = true) : stepOK p c q a l r = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  have hq : q ∈ List.finRange 6 := by simp
  have hr := h.2 q hq
  have hh : rowCheck p c q a = true := by cases a; exact hr.1; exact hr.2
  cases hv : (row c q a).lookup l with
  | none => simp [stateOK,cell,hv] at hs
  | some v =>
    have hc := Map.all_sound hh hv
    simp only [cellCheck,Bool.and_eq_true,List.all_eq_true] at hc
    have he : v.mask.testBit r = true := by simpa [stateOK,cell,hv] using hs
    exact hc.2 r (listMask_mem (subset_sound hc.1 he))

-- Finite words with implicit zero tails faithfully represent the physical tape.
structure Z where
  q : Fin 6
  a : Bool
  l : List Bool
  r : List Bool

def ray (w : List Bool) : Ray := pre w nilRay

def repr (z : Z) : Counter286.C := ⟨z.q,ray z.l,cons z.a (ray z.r)⟩

def moveZ (m : Move) (z : Z) : Z :=
  if m.right then ⟨m.next,z.r.headD false,m.write::z.l,z.r.tail⟩
  else ⟨m.next,z.l.headD false,z.l.tail,m.write::z.r⟩

theorem ray_cons (b : Bool) (w : List Bool) : ray (b::w) = cons b (ray w) := rfl
theorem ray_eta (w : List Bool) : ray w = cons (w.headD false) (ray w.tail) := by
  cases w with
  | nil => exact Counter286.cons_zero_blank.symm
  | cons b w => rfl

theorem move_repr (m : Move) (z : Z) : repr (moveZ m z) = moveC m (repr z) := by
  rcases z with ⟨q,a,l,r⟩
  cases hd : m.right with
  | false =>
    simp only [moveZ,repr,moveC,hd,Bool.false_eq_true,ite_false,ray_cons,Counter286.tail_cons]
    rw [ray_eta l]; rfl
  | true =>
    simp only [moveZ,repr,moveC,hd,ite_true,ray_cons,Counter286.tail_cons]
    exact congrArg (Counter286.C.mk m.next (cons m.write (ray l))) (ray_eta r).symm

def Inv (c : Cert) (z : Z) : Prop :=
  TapeOK c.left z.l ∧ TapeOK c.right z.r ∧ stateOK c z.q z.a (summary c.left z.l) (summary c.right z.r) = true

def zblank : Z := ⟨0,false,[],[]⟩

theorem inv_start {p c} (h : check p c = true) : Inv c zblank := by
  simp only [check,Bool.and_eq_true] at h
  change (false,0) ∈ preds c.left 0 ∧ (false,0) ∈ preds c.right 0 ∧ stateOK c 0 false 0 0 = true
  exact ⟨of_decide_eq_true h.1.1.1,of_decide_eq_true h.1.1.2,h.1.2⟩

theorem inv_step {p c z} (hc : check p c = true) (hi : Inv c z) :
    ∃ m : Move, p (z.q,z.a) = some (some m) ∧ Inv c (moveZ m z) := by
  obtain ⟨hl,hr,hs⟩ := hi
  have h := state_checked hc hs
  cases ht : p (z.q,z.a) with
  | none => simp [stepOK,ht] at h
  | some v => cases v with
    | none => simp [stepOK,ht] at h
    | some m =>
      refine ⟨m,rfl,?_⟩
      cases hd : m.right with
      | false =>
        simp only [stepOK,ht,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true] at h
        simpa only [Inv,moveZ,hd,Bool.false_eq_true,ite_false,summary] using And.intro (pop_ok hl) (And.intro (push_ok hr h.1) (h.2 _ (pop_edge hl)))
      | true =>
        simp only [stepOK,ht,hd,ite_true,Bool.and_eq_true,List.all_eq_true] at h
        simpa only [Inv,moveZ,hd,ite_true,summary] using And.intro (push_ok hl h.1) (And.intro (pop_ok hr) (h.2 _ (pop_edge hr)))

theorem live {p c} (hc : check p c = true) (m : Machine) (hm : compatible p m)
    (n : Nat) (x : Config) (z : Z) (hi : Inv c z) (he : observe x = repr z) :
    ∃ y, BB6Coverage.run m n x = some y := by
  induction n generalizing x z with
  | zero => exact ⟨x,rfl⟩
  | succ n ih =>
    obtain ⟨mv,hp,hj⟩ := inv_step hc hi
    have hq : readSlot x = (z.q,z.a) := by
      have h1 := congrArg Counter286.C.q he
      have h2 := congrArg (fun y : Counter286.C => y.r 0) he
      exact Prod.ext h1 (by simpa [repr,observe] using h2)
    have hx : rawStep m x = some (applyMove x mv) := by
      have hmv := hm (readSlot x) (some mv) (by rw [hq]; exact hp)
      simp [rawStep,hmv]
    have hy : observe (applyMove x mv) = repr (moveZ mv z) := by
      rw [observe_move,he,move_repr]
    obtain ⟨y,h⟩ := ih (applyMove x mv) (moveZ mv z) hj hy
    refine ⟨y,?_⟩
    rw [show n+1=1+n by omega,BB6Coverage.run_append]
    have h1 : BB6Coverage.run m 1 x = some (applyMove x mv) := by simpa [BB6Coverage.run] using hx
    rw [h1]; exact h

theorem never {p c} (hc : check p c = true) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have he : observe blank = repr zblank := by
    change Counter286.blankC = repr zblank
    unfold repr zblank ray Counter286.blankC
    rw [Counter286.pre,Counter286.cons_zero_blank]
  obtain ⟨y,hy⟩ := live hc m hm n blank zblank (inv_start hc) he
  change (BB6Coverage.run m n blank).isSome = true
  rw [hy]; rfl

theorem weighted {p c} (hc : check p c = true) (B : Nat) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  have h := never hc m hm (k+1)
  change (BB6Coverage.run m (k+1) blank).isSome = true at h
  rw [hk.2] at h
  contradiction

#print axioms never
#print axioms weighted
end BB6.Agent12RunGraph
