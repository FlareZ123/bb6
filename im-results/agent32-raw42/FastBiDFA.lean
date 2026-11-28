import BiDFA
import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32FastBiDFA
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent16BiDFA BB6.Agent1NGram

structure FastCert where
  dl : List Nat
  dr : List Nat
  el : Array Trie
  er : Array Trie
  nr : Nat
  states : Array Trie

def edges (e : Array Trie) (dst : Nat) : Trie := e.getD dst .empty
def edgeOK (e : Array Trie) (dst : Nat) (b : Bool) (src : Nat) : Bool :=
  (edges e dst).has (2*src+b.toNat)
def row (c : FastCert) (q : Fin 6) (a : Bool) : Trie := c.states.getD (2*q.val+a.toNat) .empty
def stateOK (c : FastCert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  (r < c.nr) && (row c q a).has (r+c.nr*l)
def bits : List Bool := [false,true]

def stateStepOK (p : PartialMachine) (c : FastCert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      edgeOK c.el (delta c.dl l mv.write) mv.write l &&
      (edges c.er r).all (fun i => stateOK c mv.next (i%2 == 1) (delta c.dl l mv.write) (i/2))
    else
      edgeOK c.er (delta c.dr r mv.write) mv.write r &&
      (edges c.el l).all (fun i => stateOK c mv.next (i%2 == 1) (i/2) (delta c.dr r mv.write))
  | _ => false

def check (p : PartialMachine) (c : FastCert) : Bool :=
  edgeOK c.el 0 false 0 && edgeOK c.er 0 false 0 && stateOK c 0 false 0 0 &&
  (List.finRange 6).all (fun q => bits.all (fun a =>
    (row c q a).all (fun i => stateStepOK p c q a (i/c.nr) (i%c.nr))))

theorem check_of_rows {p c} (hl : edgeOK c.el 0 false 0 = true)
    (hr : edgeOK c.er 0 false 0 = true) (hs : stateOK c 0 false 0 0 = true)
    (hc : ∀ q a, (row c q a).all
      (fun i => stateStepOK p c q a (i/c.nr) (i%c.nr)) = true) :
    check p c = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨hl,hr⟩,hs⟩,fun q _ a _ => hc q a⟩

theorem state_checked {p c q a l r} (h : check p c = true)
    (hs : stateOK c q a l r = true) : stateStepOK p c q a l r = true := by
  simp only [stateOK,Bool.and_eq_true,decide_eq_true_eq] at hs
  have hr := hs.1
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  have ha := h.2 q (by simp) a (by cases a <;> decide)
  have H := Trie.all_sound ha hs.2
  change stateStepOK p c q a ((r+c.nr*l)/c.nr) ((r+c.nr*l)%c.nr) = true at H
  rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hr,Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr] at H
  exact H

theorem edge_all_sound {e d b s} {f : Bool → Nat → Bool} (h : (edges e d).all (fun i => f (i%2 == 1) (i/2)) = true)
    (he : edgeOK e d b s = true) : f b s = true := by
  have H := Trie.all_sound h he
  have hb : ((2*s+b.toNat)%2 == 1) = b := by cases b <;> simp <;> omega
  have hn : (2*s+b.toNat)/2 = s := by cases b <;> simp <;> omega
  simpa only [hb,hn] using H

def TapeOK (d : List Nat) (e : Array Trie) : List Bool → Prop
  | [] => edgeOK e 0 false 0 = true
  | b::t => edgeOK e (delta d (summary d t) b) b (summary d t) = true ∧ TapeOK d e t

theorem tape_top {d e t} (h : TapeOK d e t) :
    edgeOK e (summary d t) (t.headD false) (summary d t.tail) = true := by
  cases t with
  | nil => exact h
  | cons b t => exact h.1

theorem tape_tail {d e t} (h : TapeOK d e t) : TapeOK d e t.tail := by
  cases t with
  | nil => exact h
  | cons b t => exact h.2

theorem tape_push {d e t} (b : Bool) (h : TapeOK d e t)
    (he : edgeOK e (delta d (summary d t) b) b (summary d t) = true) :
    TapeOK d e (b::t) := ⟨he,h⟩

def Inv (c : FastCert) (z : Z0) : Prop :=
  TapeOK c.dl c.el z.l.tail ∧ TapeOK c.dr c.er z.r ∧
    stateOK c z.q (z.l.headD false) (summary c.dl z.l.tail) (summary c.dr z.r) = true

theorem inv_start {p c} (h : check p c = true) : Inv c ⟨0,[],[]⟩ := by
  simp only [check,Bool.and_eq_true] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2⟩

theorem inv_step {p c z} (hc : check p c = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨hl,hr,hs⟩ := hz
  change TapeOK c.dl c.el l.tail at hl
  change TapeOK c.dr c.er r at hr
  change stateOK c q (l.headD false) (summary c.dl l.tail) (summary c.dr r) = true at hs
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
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h
        have hp := tape_push mv.write hr h.1
        have ht := tape_tail hl
        have he := edge_all_sound (f := fun b s => stateOK c mv.next b s (delta c.dr (summary c.dr r) mv.write)) h.2 (tape_top hl)
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false,summary] using And.intro ht (And.intro hp he)
      | true =>
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true] at h
        have hp := tape_push mv.write hl h.1
        have ht := tape_tail hr
        have he := edge_all_sound (f := fun b s => stateOK c mv.next b (delta c.dl (summary c.dl l.tail) mv.write) s) h.2 (tape_top hr)
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons,summary] using And.intro hp (And.intro ht he)

theorem live {p c z} (hc : check p c = true) (hz : Inv c z) (n : Nat) :
    ∃ t, run0 p n z = some t ∧ Inv c t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl,hz⟩
  | succ n ih =>
    obtain ⟨t,ht,hi⟩ := inv_step hc hz
    obtain ⟨u,hu,hj⟩ := ih hi
    exact ⟨u,by rw [run0,ht]; exact hu,hj⟩

theorem never (p : PartialMachine) (c : FastCert) (hc : check p c = true)
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
end BB6.Agent32FastBiDFA
