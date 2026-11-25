import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32FastBiDFA
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram

/-- Sparse graph of discovered stack edges, indexed by destination. -/
structure Graph where
  delta : Array Nat
  incoming : Array (List (Bool × Nat))

def push (g : Graph) (i : Nat) (b : Bool) : Nat := g.delta.getD (2*i+b.toNat) 0
def preds (g : Graph) (i : Nat) : List (Bool × Nat) := g.incoming.getD i []
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

/-- Each row is indexed by state/symbol and the left summary, and stores a trie
    of right summaries. No dense product scan or quadratic membership tests. -/
structure Cert where
  left : Graph
  right : Graph
  states : Array (Array Trie)

def rows (c : Cert) (q : Fin 6) (a : Bool) : Array Trie := c.states.getD (2*q.val+a.toNat) #[]
def row (c : Cert) (q : Fin 6) (a : Bool) (l : Nat) : Trie := (rows c q a).getD l .empty
def stateOK (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool := (row c q a l).has r

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

def rowCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) : Bool :=
  (List.range (rows c q a).size).all (fun l => (row c q a l).all (stateStepOK p c q a l))

def check (p : PartialMachine) (c : Cert) : Bool :=
  edgeOK c.left 0 false 0 && edgeOK c.right 0 false 0 && stateOK c 0 false 0 0 &&
    (List.finRange 6).all (fun q => bits.all (fun a => rowCheck p c q a))

theorem check_of_rows {p c} (hl : edgeOK c.left 0 false 0 = true)
    (hr : edgeOK c.right 0 false 0 = true) (hs : stateOK c 0 false 0 0 = true)
    (hc : ∀ q a, rowCheck p c q a = true) : check p c = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨hl,hr⟩,hs⟩,fun q _ a _ => hc q a⟩

theorem state_checked {p c q a l r} (h : check p c = true)
    (hs : stateOK c q a l r = true) : stateStepOK p c q a l r = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  have hh := h.2 q (mem_states q) a (mem_bits a)
  have hl : l < (rows c q a).size := by
    by_cases hn : l < (rows c q a).size
    · exact hn
    · simp [stateOK,row,Array.getD,hn,Trie.has] at hs
  have ha := List.all_eq_true.mp hh l (List.mem_range.mpr hl)
  exact Trie.all_sound ha hs

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

#print axioms never
#print axioms inv_step
#print axioms live
end BB6.Agent32FastBiDFA
