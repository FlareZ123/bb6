import FARBi
namespace BB6Coverage.FAR

def nodes (d : Nat) : List (Node (Fin d)) :=
  none :: (List.finRange d).flatMap fun l => (List.finRange 6).map fun q => some (l,q)

theorem mem_nodes {d : Nat} (s : Node (Fin d)) : s ∈ nodes d := by
  cases s with
  | none => simp [nodes]
  | some s =>
    rcases s with ⟨l,q⟩
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨l,List.mem_finRange l,List.mem_map.mpr ⟨q,List.mem_finRange q,rfl⟩⟩

def Data.mask {d : Nat} (C : Data d) (a : Bool) (s : Node (Fin d)) : Nat :=
  (if a then C.masks1 else C.masks0)[nodeCode s]?.getD 0

def subsetMask (x y : Nat) : Bool := (x &&& y) == x

theorem subsetMask_sound {x y i : Nat} (h : subsetMask x y = true)
    (hi : x.testBit i = true) : y.testBit i = true := by
  have he : x &&& y = x := by simpa [subsetMask] using h
  have hb := congrArg (fun n => n.testBit i) he
  simpa [Nat.testBit_and,hi] using hb

/-- One mask inclusion replaces the innermost target-state quantifier. -/
def Data.fastRule {d : Nat} (C : Data d) (p : PartialMachine) (l : Fin d) (q : Fin 6) (a : Bool) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then decide (C.edge a (some (l,q)) (some (C.push l mv.write,mv.next)))
    else (List.finRange d).all fun j => [false,true].all fun b =>
      if C.push j b = l then (nodes d).all fun v =>
        if C.edge b (some (j,mv.next)) v then
          subsetMask (C.mask mv.write v) (C.mask a (some (l,q)))
        else true
      else true
  | _ => decide (C.edge a (some (l,q)) none)

theorem Data.fastRule_sound {d : Nat} (C : Data d) (p : PartialMachine) (l : Fin d) (q : Fin 6) (a : Bool)
    (h : C.fastRule p l q a = true) : C.rule p l q a := by
  unfold Data.fastRule at h
  unfold Data.rule
  split at h <;> rename_i mv he
  · rw [he]
    split at h
    · rename_i hr
      simp [hr] at h ⊢
      exact h
    · rename_i hr
      simp only [hr]
      intro j b v t hj hv ht
      have ha := List.all_eq_true.mp h j (List.mem_finRange j)
      have hb := List.all_eq_true.mp ha b (by cases b <;> simp)
      simp only [hj,ite_eq_left] at hb
      have hc := List.all_eq_true.mp hb v (mem_nodes v)
      simp only [hv,ite_eq_left] at hc
      exact subsetMask_sound hc ht
  · split
    · rename_i mv hm
      exact False.elim (he mv hm)
    · exact of_decide_eq_true h

/-- Retain the original zero-suffix fixedpoint conditions, but check each
    transition with a bitset rather than a nested target enumeration. -/
def Data.fastValid {d : Nat} (C : Data d) (p : PartialMachine) : Bool :=
  decide (C.push C.start false = C.start ∧ C.zero none ∧
    (∀ s, C.zero s ↔ ∃ t, C.edge false s t ∧ C.zero t) ∧
    (∀ a, C.edge a none none) ∧ ¬ C.zero (some (C.start,0))) &&
  (List.finRange d).all (fun l => (List.finRange 6).all (fun q => [false,true].all (C.fastRule p l q)))

theorem Data.fastValid_sound {d : Nat} (C : Data d) (p : PartialMachine)
    (h : C.fastValid p = true) : C.valid p := by
  have h' := (Bool.and_eq_true _ _).mp h
  have hbase := of_decide_eq_true h'.1
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,hbase.2.2.2.1,hbase.2.2.2.2,?_⟩
  intro l q a
  exact C.fastRule_sound p l q a (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp h'.2 l (List.mem_finRange l)) q (List.mem_finRange q)) a
    (by cases a <;> simp))

def fastTryDfa {d : Nat} (p : PartialMachine) (start : Fin d) (dfa : List (Fin d)) : Option (Verified p) :=
  match synthesize p start dfa with
  | none => none
  | some C => if h : C.fastValid p = true then some ⟨d,⟨C,C.fastValid_sound p h⟩⟩ else none

def fastSearchD {d : Nat} (p : PartialMachine) (start : Fin d) : Option (Verified p) :=
  (dfaList start).findSome? (fastTryDfa p start)

def fastSearch (p : PartialMachine) (limit : Nat) : Option (Verified p) :=
  if !knownPrefix p 24 0 [] [] then none
  else (List.range limit).findSome? fun d => fastSearchD p (⟨0,by omega⟩ : Fin (d+1))

theorem fastSearch_sound (p : PartialMachine) (limit : Nat) (h : (fastSearch p limit).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  cases hc : fastSearch p limit with
  | none => simp [hc] at h
  | some C => exact C.2.1.sound p C.2.2 m hm

def fastOracle (p : PartialMachine) (limit : Nat) : Bool :=
  (fastSearch p limit).isSome || (fastSearch (reflectPartial p) limit).isSome

theorem fastOracle_sound (p : PartialMachine) (limit : Nat) (h : fastOracle p limit = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  rcases (Bool.or_eq_true _ _).mp h with hl | hr
  · exact fastSearch_sound p limit hl m hm
  · exact reflectNever m (fastSearch_sound (reflectPartial p) limit hr (reflectTable m) (reflectCompatible p m hm))

#print axioms Data.fastValid_sound
#print axioms fastOracle_sound
end BB6Coverage.FAR
