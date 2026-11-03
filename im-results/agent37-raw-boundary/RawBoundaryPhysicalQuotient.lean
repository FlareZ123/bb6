import RawBoundaryInit

namespace BB6.RawBoundaryBridge
open BB6.Portfolio

private theorem getD_append_false (xs : List Bool) (j : Nat) :
    (xs ++ [false]).getD j false = xs.getD j false := by
  induction xs generalizing j with
  | nil => cases j <;> rfl
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => simpa [List.getD] using ih j

/-- Appending an explicit trailing zero changes no bit of the full physical
    tape, including when the implicit tape is originally all zeros. -/
theorem pack_right_append_zero (l r : List Bool) (b : Bool)
    (st : Nat) (p : Int) :
    pack ⟨l,b,r++[false],st⟩ p = pack ⟨l,b,r,st⟩ p := by
  by_cases hs : st < 6
  · unfold pack
    simp only [hs, dite_true, Option.some.injEq]
    congr 1
    funext i
    unfold tapeZ
    by_cases hl : i < p
    · simp [hl]
    · by_cases heq : i = p
      · simp [hl,heq]
      · simp only [if_neg hl, if_neg heq]
        exact getD_append_false r _
  · simp [pack,hs]

/-- The representation-independent quotient principle: any two finite-list
    tapes with the same actual infinite physical tape have identical raw
    physical trajectories for all primitive step counts, including halting. -/
theorem physical_run_congruence (c d : CryptidBoundary.Cfg)
    (p q : Int) (h : pack c p = pack d q) (n : Nat) :
    pack (CryptidBoundary.run n c) (posAfter n c p) =
      pack (CryptidBoundary.run n d) (posAfter n d q) := by
  rw [←run_pack, ←run_pack, h]

/-- An original-source, unbounded family of *exact primitive-step* raw TM
    transitions, obtained by combining Agent31's full_B rule with the
    infinite physical tape transport and representation quotient. Head offset
    is existential because Agent31's zipper deliberately forgets coordinates. -/
theorem raw_full_B_physical (k : Nat) :
    ∃ p : Int,
      BB6.Portfolio.run D0 (12*k*k+49*k+40)
        (some (BB6.Portfolio.F0Pure (3*k+2) 0)) =
          some (BB6.Portfolio.F0Pure (8*k+9) p) := by
  let c : CryptidBoundary.Cfg :=
    CryptidBoundary.init (List.replicate (3*k) true ++ [false])
  let t := 12*k*k+49*k+40
  have hstart : pack (unary (3*k+2)) 0 = pack c 0 := by
    rw [unary_eq_init_replicate (3*k)]
    change pack ⟨[],false,true::true::List.replicate (3*k) true,5⟩ 0 =
      pack ⟨[],false,(true::true::List.replicate (3*k) true)++[false],5⟩ 0
    exact (pack_right_append_zero [] _ false 5 0).symm
  have hreturn : CryptidBoundary.run t c = unary (8*k+9) := by
    simpa [t,c,unary] using (CryptidBoundary.full_B k [])
  refine ⟨posAfter t c 0, ?_⟩
  calc
    BB6.Portfolio.run D0 t (some (BB6.Portfolio.F0Pure (3*k+2) 0)) =
        pack (CryptidBoundary.run t (unary (3*k+2)))
          (posAfter t (unary (3*k+2)) 0) := by
            rw [←pack_unary, run_pack]
    _ = pack (CryptidBoundary.run t c) (posAfter t c 0) :=
          physical_run_congruence _ _ 0 0 hstart t
    _ = some (BB6.Portfolio.F0Pure (8*k+9) (posAfter t c 0)) := by
          rw [hreturn, pack_unary]

#print axioms pack_right_append_zero
#print axioms physical_run_congruence
#print axioms raw_full_B_physical
end BB6.RawBoundaryBridge
