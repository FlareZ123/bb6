import BiDFA
import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32PackedMatrixBiDFA
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent16BiDFA

structure PackedDFA where
  width : Nat
  data : Nat

def field (data width i : Nat) : Nat := (data >>> (width*i)) &&& ((1 <<< width)-1)
def delta (d : PackedDFA) (i : Nat) (b : Bool) : Nat := field d.data d.width (2*i+b.toNat)
def summary (d : PackedDFA) : List Bool → Nat
  | [] => 0
  | b::t => delta d (summary d t) b

/-- Bit-packed transition tables, reverse tape edges, and state relation rows.
Each state row is a bitset of right summaries, indexed by state, bit and left summary. -/
structure MatrixCert where
  dl : PackedDFA
  dr : PackedDFA
  nl : Nat
  nr : Nat
  el : Nat
  er : Nat
  states : Nat

def edges (e n dst : Nat) (b : Bool) : Nat := field e n (2*dst+b.toNat)
def edgeOK (e n dst : Nat) (b : Bool) (src : Nat) : Bool :=
  (dst < n) && (src < n) && (edges e n dst b).testBit src
def row (c : MatrixCert) (q : Fin 6) (a : Bool) (l : Nat) : Nat :=
  field c.states c.nr ((2*q.val+a.toNat)*c.nl+l)
def stateOK (c : MatrixCert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  (l < c.nl) && (r < c.nr) && (row c q a l).testBit r
def bits : List Bool := [false,true]

def subset (x y : Nat) : Bool := (x &&& y) == x

theorem subset_sound {x y i : Nat} (h : subset x y = true) (hx : x.testBit i = true) :
    y.testBit i = true := by
  have e := congrArg (fun v : Nat => v.testBit i) (beq_iff_eq.mp h)
  rw [Nat.testBit_and,hx] at e
  simpa using e

def selected (n x : Nat) (f : Nat → Bool) : Bool :=
  (List.range n).all (fun i => !x.testBit i || f i)

theorem selected_sound {n x i : Nat} {f : Nat → Bool}
    (h : selected n x f = true) (hi : i < n) (hx : x.testBit i = true) : f i = true := by
  have he := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa [hx] using he

def imageOn (x : Nat) (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | i::is => if x.testBit i then f i ||| imageOn x f is else imageOn x f is

theorem imageOn_sound {x i j : Nat} {f : Nat → Nat} {is : List Nat}
    (hi : i ∈ is) (hx : x.testBit i = true) (hf : (f i).testBit j = true) :
    (imageOn x f is).testBit j = true := by
  induction is with
  | nil => simp at hi
  | cons k ks ih =>
    rcases List.mem_cons.mp hi with rfl|hm
    · simp [imageOn,hx,Nat.testBit_or,hf]
    · have hh := ih hm
      cases e : x.testBit k <;> simp [imageOn,e,Nat.testBit_or,hh]

def image (n x : Nat) (f : Nat → Nat) : Nat := imageOn x f (List.range n)

theorem image_sound {n x i j : Nat} {f : Nat → Nat}
    (hi : i < n) (hx : x.testBit i = true) (hf : (f i).testBit j = true) :
    (image n x f).testBit j = true := imageOn_sound (List.mem_range.mpr hi) hx hf

def pushImage (d : PackedDFA) (n x : Nat) (w : Bool) : Nat :=
  image n x (fun r => 1 <<< delta d r w)

theorem pushImage_sound {d n x r : _} {w : Bool} (hr : r < n)
    (hx : x.testBit r = true) : (pushImage d n x w).testBit (delta d r w) = true := by
  apply image_sound hr hx
  simp [Nat.shiftLeft_eq]

def rowStepOK (p : PartialMachine) (c : MatrixCert) (q : Fin 6) (a : Bool) (l : Nat) : Bool :=
  let x := row c q a l
  if x == 0 then true else
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      let l' := delta c.dl l mv.write
      edgeOK c.el c.nl l' mv.write l &&
        bits.all (fun b => subset (image c.nr x (fun r => edges c.er c.nr r b)) (row c mv.next b l'))
    else
      selected c.nr x (fun r => edgeOK c.er c.nr (delta c.dr r mv.write) mv.write r) &&
        bits.all (fun b => selected c.nl (edges c.el c.nl l b) (fun l' =>
          subset (pushImage c.dr c.nr x mv.write) (row c mv.next b l')))
  | _ => false

def check (p : PartialMachine) (c : MatrixCert) : Bool :=
  edgeOK c.el c.nl 0 false 0 && edgeOK c.er c.nr 0 false 0 && stateOK c 0 false 0 0 &&
  (List.finRange 6).all (fun q => bits.all (fun a => (List.range c.nl).all (rowStepOK p c q a)))

theorem state_checked {p c q a l r} (h : check p c = true)
    (hs : stateOK c q a l r = true) : rowStepOK p c q a l = true := by
  simp only [stateOK,Bool.and_eq_true,decide_eq_true_eq] at hs
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  exact h.2 q (by simp) a (by cases a <;> decide) l (List.mem_range.mpr hs.1.1)

def TapeOK (d : PackedDFA) (e n : Nat) : List Bool → Prop
  | [] => edgeOK e n 0 false 0 = true
  | b::t => edgeOK e n (delta d (summary d t) b) b (summary d t) = true ∧ TapeOK d e n t

theorem tape_top {d e n t} (h : TapeOK d e n t) :
    edgeOK e n (summary d t) (t.headD false) (summary d t.tail) = true := by
  cases t with
  | nil => exact h
  | cons b t => exact h.1

theorem tape_tail {d e n t} (h : TapeOK d e n t) : TapeOK d e n t.tail := by
  cases t with
  | nil => exact h
  | cons b t => exact h.2

theorem tape_push {d e n t} (b : Bool) (h : TapeOK d e n t)
    (he : edgeOK e n (delta d (summary d t) b) b (summary d t) = true) :
    TapeOK d e n (b::t) := ⟨he,h⟩

def Inv (c : MatrixCert) (z : Z0) : Prop :=
  TapeOK c.dl c.el c.nl z.l.tail ∧ TapeOK c.dr c.er c.nr z.r ∧
    stateOK c z.q (z.l.headD false) (summary c.dl z.l.tail) (summary c.dr z.r) = true

theorem inv_start {p c} (h : check p c = true) : Inv c ⟨0,[],[]⟩ := by
  simp only [check,Bool.and_eq_true] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2⟩

theorem inv_step {p c z} (hc : check p c = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨hl,hr,hs⟩ := hz
  change TapeOK c.dl c.el c.nl l.tail at hl
  change TapeOK c.dr c.er c.nr r at hr
  change stateOK c q (l.headD false) (summary c.dl l.tail) (summary c.dr r) = true at hs
  have h := state_checked hc hs
  simp only [stateOK,Bool.and_eq_true,decide_eq_true_eq] at hs
  have hn : row c q (l.headD false) (summary c.dl l.tail) ≠ 0 := by
    intro e
    rw [e] at hs
    simp at hs
  simp only [rowStepOK,beq_iff_eq,hn,ite_false] at h
  cases hm : p (q,l.headD false) with
  | none => simp only [hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some],?_⟩
      cases hd : mv.right with
      | false =>
        simp only [hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true] at h
        have he := selected_sound h.1 hs.1.2 hs.2
        have hp := tape_push mv.write hr he
        have ht := tape_tail hl
        have hpop := tape_top hl
        simp only [edgeOK,Bool.and_eq_true,decide_eq_true_eq] at hpop he
        have hsub := selected_sound (h.2 (l.tail.headD false) (by cases l.tail.headD false <;> decide)) hpop.1.2 hpop.2
        have hbit := subset_sound hsub (pushImage_sound hs.1.2 hs.2)
        have hstate : stateOK c mv.next (l.tail.headD false) (summary c.dl l.tail.tail)
            (delta c.dr (summary c.dr r) mv.write) = true := by
          simp only [stateOK,Bool.and_eq_true,decide_eq_true_eq]
          exact ⟨⟨hpop.1.2,he.1.1⟩,hbit⟩
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false,summary] using And.intro ht (And.intro hp hstate)
      | true =>
        simp only [hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true] at h
        have hp := tape_push mv.write hl h.1
        have ht := tape_tail hr
        have hpop := tape_top hr
        have he := h.1
        simp only [edgeOK,Bool.and_eq_true,decide_eq_true_eq] at hpop he
        have hsub := h.2 (r.headD false) (by cases r.headD false <;> decide)
        have hbit := subset_sound hsub (image_sound hs.1.2 hs.2 hpop.2)
        have hstate : stateOK c mv.next (r.headD false) (delta c.dl (summary c.dl l.tail) mv.write)
            (summary c.dr r.tail) = true := by
          simp only [stateOK,Bool.and_eq_true,decide_eq_true_eq]
          exact ⟨⟨he.1.1,hpop.1.2⟩,hbit⟩
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons,summary] using And.intro hp (And.intro ht hstate)

theorem live {p c z} (hc : check p c = true) (hz : Inv c z) (n : Nat) :
    ∃ t, run0 p n z = some t ∧ Inv c t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl,hz⟩
  | succ n ih =>
    obtain ⟨t,ht,hi⟩ := inv_step hc hz
    obtain ⟨u,hu,hj⟩ := ih hi
    exact ⟨u,by rw [run0,ht]; exact hu,hj⟩

theorem never (p : PartialMachine) (c : MatrixCert) (hc : check p c = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,_⟩ := live hc (inv_start hc) n
  have hz : (BB6Coverage.Agent50Zipper.zrun p n start).map project = some t :=
    (run_project p n start).trans ht
  cases h : BB6Coverage.Agent50Zipper.zrun p n start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound p m hm n start z h
    rw [start_embed] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms inv_step
#print axioms never
end BB6.Agent32PackedMatrixBiDFA
