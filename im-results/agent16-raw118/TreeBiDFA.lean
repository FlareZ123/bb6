import BiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent16BiDFA.TreeCheck
open BB6Coverage BB6Coverage.Agent16BiDFA

inductive Tree where
  | empty
  | node (l : Tree) (s : AState) (r : Tree)

def key (s : AState) : Nat := ((s.q.val*2+s.a.toNat)*64+s.l)*64+s.r

def Tree.contains (t : Tree) (s : AState) : Bool :=
  match t with
  | .empty => false
  | .node l a r =>
    if key s < key a then l.contains s
    else if key a < key s then r.contains s
    else decide (s = a)

def Tree.flatten : Tree → List AState
  | .empty => []
  | .node l s r => l.flatten ++ s::r.flatten

def Tree.all (f : AState → Bool) : Tree → Bool
  | .empty => true
  | .node l s r => f s && l.all f && r.all f

theorem Tree.contains_sound {t : Tree} {s : AState} (h : t.contains s = true) : s ∈ t.flatten := by
  induction t with
  | empty => simp [Tree.contains] at h
  | node l a r il ir =>
    simp only [Tree.contains] at h
    split at h
    · exact List.mem_append_left _ (il h)
    · split at h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ir h))
      · have he := of_decide_eq_true h
        subst s
        exact List.mem_append_right _ (List.mem_cons_self)

theorem Tree.all_sound {f : AState → Bool} {t : Tree} (h : t.all f = true) : ∀ s ∈ t.flatten, f s = true := by
  induction t with
  | empty => simp [Tree.flatten]
  | node l a r il ir =>
    simp only [Tree.all,Bool.and_eq_true] at h
    intro s hs
    rcases List.mem_append.mp hs with hl|hr
    · exact il h.1.2 s hl
    · rcases List.mem_cons.mp hr with rfl|hr
      · exact h.1.1
      · exact ir h.2 s hr

structure TreeCert where
  dl : List Nat
  dr : List Nat
  el : List Edge
  er : List Edge
  states : Tree

def TreeCert.toCert (c : TreeCert) : Cert :=
  ⟨c.dl,c.dr,c.el,c.er,c.states.flatten⟩

def stepOK (p : PartialMachine) (c : TreeCert) (s : AState) : Bool :=
  match p (s.q,s.a) with
  | some (some mv) =>
    if mv.right then
      decide ((⟨delta c.dl s.l mv.write,mv.write,s.l⟩ : Edge) ∈ c.el) &&
      c.er.all (fun e => if e.dst = s.r then c.states.contains ⟨mv.next,e.sym,delta c.dl s.l mv.write,e.src⟩ else true)
    else
      decide ((⟨delta c.dr s.r mv.write,mv.write,s.r⟩ : Edge) ∈ c.er) &&
      c.el.all (fun e => if e.dst = s.l then c.states.contains ⟨mv.next,e.sym,e.src,delta c.dr s.r mv.write⟩ else true)
  | _ => false

theorem stepOK_sound {p c s} (h : stepOK p c s = true) :
    stateStepOK p c.toCert s = true := by
  cases hp : p (s.q,s.a) with
  | none => simp [stepOK,hp] at h
  | some op =>
    cases op with
    | none => simp [stepOK,hp] at h
    | some mv =>
      cases hd : mv.right with
      | false =>
        simp only [stepOK,hp,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true] at h
        simp only [stateStepOK,TreeCert.toCert,hp,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true]
        refine ⟨h.1,?_⟩
        intro e he
        by_cases heq : e.dst = s.l
        · simp only [heq,ite_true]
          exact decide_eq_true (Tree.contains_sound (by simpa only [heq,ite_true] using h.2 e he))
        · simp only [heq,ite_false]
      | true =>
        simp only [stepOK,hp,hd,ite_true,Bool.and_eq_true,List.all_eq_true] at h
        simp only [stateStepOK,TreeCert.toCert,hp,hd,ite_true,Bool.and_eq_true,List.all_eq_true]
        refine ⟨h.1,?_⟩
        intro e he
        by_cases heq : e.dst = s.r
        · simp only [heq,ite_true]
          exact decide_eq_true (Tree.contains_sound (by simpa only [heq,ite_true] using h.2 e he))
        · simp only [heq,ite_false]

theorem Tree.all_node {f l s r} (hs : f s = true) (hl : l.all f = true) (hr : r.all f = true) :
    (Tree.node l s r).all f = true := by simp [Tree.all,hs,hl,hr]

theorem check_sound {p : PartialMachine} {c : TreeCert}
    (hl : (⟨0,false,0⟩ : Edge) ∈ c.el)
    (hr : (⟨0,false,0⟩ : Edge) ∈ c.er)
    (hs : c.states.contains ⟨0,false,0,0⟩ = true)
    (hc : c.states.all (stepOK p c) = true) : check p c.toCert = true := by
  simp only [check,TreeCert.toCert,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨⟨decide_eq_true hl,decide_eq_true hr⟩,decide_eq_true (Tree.contains_sound hs)⟩,?_⟩
  intro s he
  exact stepOK_sound (Tree.all_sound hc s he)

theorem never (p : PartialMachine) (c : TreeCert)
    (hl : (⟨0,false,0⟩ : Edge) ∈ c.el)
    (hr : (⟨0,false,0⟩ : Edge) ∈ c.er)
    (hs : c.states.contains ⟨0,false,0,0⟩ = true)
    (hc : c.states.all (stepOK p c) = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  Agent16BiDFA.never p c.toCert (check_sound hl hr hs hc) m hm

#print axioms never
end BB6Coverage.Agent16BiDFA.TreeCheck
