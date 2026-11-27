import WeightedTNFCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent46FiniteStateTransfer
open BB6Coverage BB6.Agent13BlankDelay

/-- A bit matrix of 36 directed pairs of control states. Configurations
    related by a pair have the same complete tape and head coordinate. -/
def rel (R : Nat) (a b : Fin 6) : Bool :=
  R.testBit (6*a.val+b.val)

/-- Only the source's ordinary transitions have to be simulated: a source
    default completion certified to never halt cannot consult a hole. -/
def cell (p p' : PartialMachine) (R : Nat) (a b : Fin 6) (s : Bool) : Bool :=
  if rel R a b then
    match p (a,s) with
    | some (some mv) =>
      match p' (b,s) with
      | some (some mv') =>
        (mv.write == mv'.write) && ((mv.right == mv'.right) && rel R mv.next mv'.next)
      | _ => false
    | _ => true
  else true

def check (p p' : PartialMachine) (R : Nat) : Bool :=
  rel R 0 0 && (List.finRange 6).all (fun a =>
    (List.finRange 6).all (fun b => [false,true].all (cell p p' R a b)))

theorem step_transport {p p' : PartialMachine} {R : Nat}
    (h : check p p' R = true) {a b : Fin 6} {s : Bool} {mv : Move}
    (hr : rel R a b = true) (hp : p (a,s) = some (some mv)) :
    ∃ mv', p' (b,s) = some (some mv') ∧
      mv.write = mv'.write ∧ mv.right = mv'.right ∧ rel R mv.next mv'.next = true := by
  have hmem : s ∈ [false,true] := by cases s <;> simp
  have h0 := (Bool.and_eq_true.mp h).2
  have h1 := List.all_eq_true.mp h0 a (List.mem_finRange a)
  have h2 := List.all_eq_true.mp h1 b (List.mem_finRange b)
  have h3 := List.all_eq_true.mp h2 s hmem
  simp only [cell, hr, if_true, hp] at h3
  cases ht : p' (b,s) with
  | none => simp [ht] at h3
  | some tr =>
    cases tr with
    | none => simp [ht] at h3
    | some mv' =>
      simp only [ht,Bool.and_eq_true,beq_iff_eq] at h3
      exact ⟨mv',rfl,h3.1,h3.2.1,h3.2.2⟩

/-- Every sparse completion of the target is live if the source sparse
    cylinder is live and the finite directed simulation check succeeds. -/
theorem never {p p' : PartialMachine} {R : Nat} (h : check p p' R = true)
    (source : ∀ m, compatible p m → NeverHalts m)
    (m : Machine) (hm : compatible p' m) : NeverHalts m := by
  let m0 := weightedTNFDefaultCompletion p
  have h0 := source m0 (weightedTNFDefaultCompletion_compatible p)
  have hpair : ∀ n, ∃ x y : Config,
      run m0 n blank = some x ∧ run m n blank = some y ∧
      x.head = y.head ∧ x.tape = y.tape ∧ rel R x.state y.state = true := by
    intro n
    induction n with
    | zero =>
      exact ⟨blank,blank,rfl,rfl,rfl,rfl,(Bool.and_eq_true.mp h).1⟩
    | succ n ih =>
      obtain ⟨x,y,hx,hy,hh,ht,hr⟩ := ih
      have hlive := h0 (n+1)
      simp only [run,hx,Option.bind_some] at hlive
      cases hp : p (readSlot x) with
      | none => simp [rawStep,m0,weightedTNFDefaultCompletion,hp] at hlive
      | some tr =>
        cases tr with
        | none => simp [rawStep,m0,weightedTNFDefaultCompletion,hp] at hlive
        | some mv =>
          obtain ⟨mv',hp',hw,hd,hn⟩ := step_transport h hr hp
          have hyrow : p' (readSlot y) = some (some mv') := by
            simpa [readSlot,hh,ht] using hp'
          refine ⟨applyMove x mv,applyMove y mv',?_,?_,?_,?_,hn⟩
          · simp [run,hx,rawStep,m0,weightedTNFDefaultCompletion,hp]
          · simp [run,hy,rawStep,hm _ _ hyrow]
          · simp [applyMove,hh,hd]
          · simp [applyMove,hh,ht,hw]
  intro n
  obtain ⟨_,_,_,hy,_,_,_⟩ := hpair n
  simp [hy]

#print axioms step_transport
#print axioms never
end BB6.Agent46FiniteStateTransfer
