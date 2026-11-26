import NGramCertificate
import MaskMap
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32MaskBiDFA
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram
structure Graph where
  delta : Map Nat
  incoming : Map (List (Bool × Nat))

def push (g : Graph) (i : Nat) (b : Bool) : Nat := (g.delta.lookup (2*i+b.toNat)).getD 0
def preds (g : Graph) (i : Nat) : List (Bool × Nat) := (g.incoming.lookup i).getD []
def edgeOK (g : Graph) (i : Nat) (b : Bool) (j : Nat) : Bool := decide ((b,j) ∈ preds g i)

def summary (g : Graph) : List Bool → Nat
  | [] => 0
  | b::t => push g (summary g t) b

def TapeOK (g : Graph) : List Bool → Prop
  | [] => (false,0) ∈ preds g 0
  | b::t => (b,summary g t) ∈ preds g (summary g (b::t)) ∧ TapeOK g t

theorem tape_top {g t} (h : TapeOK g t) : (t.headD false,summary g t.tail) ∈ preds g (summary g t) := by
  cases t with
  | nil => exact h
  | cons b t => exact h.1

theorem tape_tail {g t} (h : TapeOK g t) : TapeOK g t.tail := by
  cases t with
  | nil => exact h
  | cons b t => exact h.2

theorem tape_push {g t} (b : Bool) (h : TapeOK g t)
    (he : edgeOK g (push g (summary g t) b) b (summary g t) = true) : TapeOK g (b::t) :=
  ⟨of_decide_eq_true he,h⟩

def predMask (b : Bool) : List (Bool × Nat) → Nat
  | [] => 0
  | (a,j)::t => (if a = b then 2^j else 0) ||| predMask b t

theorem predMask_mem {b j es} (h : (b,j) ∈ es) : (predMask b es).testBit j = true := by
  induction es with
  | nil => contradiction
  | cons e es ih =>
    rcases List.mem_cons.mp h with he|ht
    · subst e
      simp [predMask,Nat.testBit_or]
    · obtain ⟨a,i⟩ := e
      simp [predMask,Nat.testBit_or,ih ht]

structure Cert where
  left : Graph
  right : Graph
  states : Array (Map Cell)

def rows (c : Cert) (q : Fin 6) (a : Bool) : Map Cell := c.states.getD (2*q.val+a.toNat) .empty
def cell (c : Cert) (q : Fin 6) (a : Bool) (l : Nat) : Cell := ((rows c q a).lookup l).getD ⟨0,[]⟩
def mask (c : Cert) (q : Fin 6) (a : Bool) (l : Nat) : Nat := (cell c q a l).mask
def stateOK (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool := (mask c q a l).testBit r

/-- A single row closure checks whole successor masks. The receiving-side push
    is constant for right moves, and left moves reuse its full image for each pop. -/
def cellCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (l : Nat) (v : Cell) : Bool :=
  let m := v.mask
  if m = 0 then true else
  subset m (listMask v.indices) &&
  (match p (q,a) with
  | some (some mv) =>
    if mv.right then
      let lp := push c.left l mv.write
      edgeOK c.left lp mv.write l && bits.all (fun b =>
        match image (fun r => some (predMask b (preds c.right r))) v.indices with
        | none => false
        | some out => subset out (mask c mv.next b lp))
    else
      match image (fun r =>
        let rp := push c.right r mv.write
        if edgeOK c.right rp mv.write r then some (2^rp) else none) v.indices with
      | none => false
      | some out => (preds c.left l).all (fun e => subset out (mask c mv.next e.1 e.2))
  | _ => false)

def rowCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) : Bool :=
  (rows c q a).all (cellCheck p c q a)

def check (p : PartialMachine) (c : Cert) : Bool :=
  edgeOK c.left 0 false 0 && edgeOK c.right 0 false 0 && stateOK c 0 false 0 0 &&
  (List.finRange 6).all (fun q => bits.all (fun a => rowCheck p c q a))

theorem check_of_rows {p c} (hl : edgeOK c.left 0 false 0 = true)
    (hr : edgeOK c.right 0 false 0 = true) (hs : stateOK c 0 false 0 0 = true)
    (hc : ∀ q a, rowCheck p c q a = true) : check p c = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨hl,hr⟩,hs⟩,fun q _ a _ => hc q a⟩

def stateStepOK (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      edgeOK c.left (push c.left l mv.write) mv.write l &&
        (preds c.right r).all (fun e => stateOK c mv.next e.1 (push c.left l mv.write) e.2)
    else
      edgeOK c.right (push c.right r mv.write) mv.write r &&
        (preds c.left l).all (fun e => stateOK c mv.next e.1 e.2 (push c.right r mv.write))
  | _ => false

theorem cell_sound {p c q a l r} (h : cellCheck p c q a l (cell c q a l) = true)
    (hs : stateOK c q a l r = true) : stateStepOK p c q a l r = true := by
  have hn : mask c q a l ≠ 0 := by intro he; simp [stateOK,he] at hs
  change (cell c q a l).mask ≠ 0 at hn
  simp only [cellCheck,hn,ite_false,Bool.and_eq_true] at h
  have hiMem := listMask_mem (subset_sound h.1 hs)
  have h := h.2
  cases hm : p (q,a) with
  | none => simp [hm] at h
  | some op =>
    cases op with
    | none => simp [hm] at h
    | some mv =>
      cases hd : mv.right with
      | true =>
        simp only [hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true] at h ⊢
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true]
        refine ⟨h.1,?_⟩
        intro e he
        have hh := h.2 e.1 (mem_bits e.1)
        cases hi : image (fun x => some (predMask e.1 (preds c.right x))) (cell c q a l).indices with
        | none => simp [hi] at hh
        | some out =>
          simp only [hi] at hh
          obtain ⟨x,hx,hsub⟩ := image_sound hi hiMem
          simp only [Option.some.injEq] at hx
          subst x
          exact subset_sound hh (hsub e.2 (predMask_mem (by simpa using he)))
      | false =>
        simp only [hm,hd,Bool.false_eq_true,ite_false] at h
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true]
        cases hi : image (fun x => if edgeOK c.right (push c.right x mv.write) mv.write x then some (2^push c.right x mv.write) else none) (cell c q a l).indices with
        | none => simp [hi] at h
        | some out =>
          simp only [hi,List.all_eq_true] at h
          obtain ⟨x,hx,hsub⟩ := image_sound hi hiMem
          cases he : edgeOK c.right (push c.right r mv.write) mv.write r with
          | false => simp [he] at hx
          | true =>
            simp only [he,ite_true,Option.some.injEq] at hx
            subst x
            refine ⟨rfl,?_⟩
            intro e he
            exact subset_sound (h e he) (hsub _ (by simp))

theorem state_checked {p c q a l r} (h : check p c = true)
    (hs : stateOK c q a l r = true) : stateStepOK p c q a l r = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  have hh := h.2 q (mem_states q) a (mem_bits a)
  cases hv : (rows c q a).lookup l with
  | none => simp [stateOK,mask,cell,hv] at hs
  | some v =>
    have he : cell c q a l = v := by simp [cell,hv]
    apply cell_sound _ hs
    rw [he]
    exact Map.all_sound hh hv

def Inv (c : Cert) (z : Z0) : Prop :=
  TapeOK c.left z.l.tail ∧ TapeOK c.right z.r ∧
    stateOK c z.q (z.l.headD false) (summary c.left z.l.tail) (summary c.right z.r) = true

theorem inv_start {p c} (h : check p c = true) : Inv c ⟨0,[],[]⟩ := by
  simp only [check,Bool.and_eq_true] at h
  change (false,0) ∈ preds c.left 0 ∧ (false,0) ∈ preds c.right 0 ∧ stateOK c 0 false 0 0 = true
  exact ⟨of_decide_eq_true h.1.1.1,of_decide_eq_true h.1.1.2,h.1.2⟩

theorem inv_step {p c z} (hc : check p c = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨hl,hr,hs⟩ := hz
  change TapeOK c.left l.tail at hl
  change TapeOK c.right r at hr
  change stateOK c q (l.headD false) (summary c.left l.tail) (summary c.right r) = true at hs
  have h := state_checked hc hs
  cases hm : p (q,l.headD false) with
  | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some],?_⟩
      cases hd : mv.right with
      | false =>
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true] at h
        have hp := tape_push mv.write hr h.1
        have ht := tape_tail hl
        have he := h.2 _ (tape_top hl)
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false,summary] using And.intro ht (And.intro hp he)
      | true =>
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true] at h
        have hp := tape_push mv.write hl h.1
        have ht := tape_tail hr
        have he := h.2 _ (tape_top hr)
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons,summary] using And.intro hp (And.intro ht he)

theorem live {p c z} (hc : check p c = true) (hz : Inv c z) (n : Nat) :
    ∃ t, run0 p n z = some t ∧ Inv c t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl,hz⟩
  | succ n ih =>
    obtain ⟨t,ht,hi⟩ := inv_step hc hz
    obtain ⟨u,hu,hj⟩ := ih hi
    exact ⟨u,by rw [run0,ht]; exact hu,hj⟩

theorem never (p : PartialMachine) (c : Cert) (hc : check p c = true)
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

#print axioms image_sound
#print axioms cell_sound
#print axioms never
end BB6.Agent32MaskBiDFA
