import E0LFResidual3862
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent3E0LFSweep
namespace BB6.Agent14ZeroLF3862

/-- The symbolic period is exactly 48 consecutive ones. -/
theorem family_shape (k : Nat) : family k = [false,false,true,false,false] ++ List.replicate (112+48*k) true := by
  have hp : pow (List.replicate 48 true) k = List.replicate (48*k) true := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow,ih,List.replicate_append_replicate]; congr 1; omega
  change r0.pre ++ pow r0.period k ++ r0.post = _
  rw [show r0.pre = [false,false,true,false,false] ++ List.replicate 112 true by decide +kernel,
      show r0.period = List.replicate 48 true by decide +kernel,
      show r0.post = [] by rfl, List.append_nil, hp, List.append_assoc, List.replicate_append_replicate]

/-- Every member of the growing family from the entry index onward occurs. -/
theorem family_reachable (m : Machine) (hm : compatible (table false) m) (j : Nat) :
    ∃ n h, run m n blank = some (embed (cfg .a h [] (family (132+j)))) := by
  induction j with
  | zero => exact seed m hm
  | succ j ih =>
    obtain ⟨n,h,hn⟩ := ih
    obtain ⟨u,h',_,hu⟩ := recurrence (132+j) m hm h
    refine ⟨n+u,h',?_⟩
    rw [run_append,hn]
    exact hu

/-- A reachable configuration has an interval of at least N consecutive ones. -/
theorem arbitrary_one_run (m : Machine) (hm : compatible (table false) m) (N : Nat) :
    ∃ n c x, run m n blank = some c ∧ ∀ i : Nat, i < N → c.tape (x + (i:Int)) = true := by
  obtain ⟨n,h,hn⟩ := family_reachable m hm N
  refine ⟨n,embed (cfg .a h [] (family (132+N))),h+5,hn,?_⟩
  intro i hi
  rw [family_shape]
  change atCell (cfg .a h [] ([false,false,true,false,false] ++ List.replicate (112+48*(132+N)) true)) (h+5+(i:Int)) = true
  unfold atCell cfg
  simp only [List.cons_append, List.tail_cons]
  split
  · omega
  · have hidx : (h+5+(i:Int)-h-1).toNat = i+4 := by omega
    rw [hidx]
    simp only [List.getD, List.nil_append]
    change (List.replicate (112+48*(132+N)) true)[i]?.getD false = true
    rw [List.getElem?_replicate_of_lt (by omega)]
    rfl

#print axioms arbitrary_one_run
end BB6.Agent14ZeroLF3862
