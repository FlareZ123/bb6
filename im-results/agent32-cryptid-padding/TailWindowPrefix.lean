import TailWindowCore
import Lean.Elab.Tactic.Omega

namespace TailWindow
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/- A fixed right-hand word followed by zeros; the head is E scanning 0. -/
def startLocalWord (w : List Bool) : Cfg :=
  ⟨4, 0, fun i =>
    if i < 0 then
      ([false, false, true, false, true] : List Bool).getD ((-i - 1).toNat) false
    else if i = 0 then false
    else (tailPrefix ++ w).getD (i.toNat - 1) false⟩

/- The actual left stack has m repetitions of 10 and a terminal 11.
   A second, arbitrary right suffix is allowed. -/
def startActualWord (m : Nat) (w : List Bool) : Cfg :=
  ⟨4, 0, fun i =>
    if i < 0 then
      (actualLeft m).getD ((-i - 1).toNat) false
    else if i = 0 then false
    else (tailPrefix ++ w).getD (i.toNat - 1) false⟩

private theorem getD_append_of_lt (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    (xs ++ ys).getD i false = xs.getD i false := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ j =>
          have h : j < xs.length := by
            simp only [List.length_cons] at hi
            omega
          simpa [List.getD] using ih j h

/- Source-left identity and right-prefix locality. All cells in the
   audited interval are independent of the arbitrary appended word ys. -/
theorem initialWordEqOn (m : Nat) (w ys : List Bool) (hm : 3 ≤ m) :
    ConfigEqOn (-5) (7 + w.length : Int)
      (startLocalWord w) (startActualWord m (w ++ ys)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i hlo hhi
  by_cases hneg : i < 0
  · have hb := (initialEqOn m 0 0 (7 + w.length) hm).2.2 i hlo hhi
    simpa [startLocalWord, startActualWord,
      startLocal, startActual, localTape, actualTape, hneg] using hb.symm
  · by_cases hzero : i = 0
    · subst i
      simp [startLocalWord, startActualWord]
    · have hpos : 0 < i := by omega
      have hj : i.toNat - 1 < (tailPrefix ++ w).length := by
        simp only [List.length_append]
        simp [tailPrefix]
        omega
      have ht := getD_append_of_lt (tailPrefix ++ w) ys (i.toNat - 1) hj
      simpa [startLocalWord, startActualWord, hneg, hzero,
        List.append_assoc] using ht.symm

/- The checker certifies an exact nth terminal configuration and a bounded
   head trajectory; a mere transient F/1 observation is insufficient. -/
def haltCheckWord (n : Nat) (w : List Bool) : Bool :=
  match run (n - 1) (some (startLocalWord w)) with
  | none => false
  | some c =>
      match step c with
      | none => false
      | some d =>
          decide (d.state = 5 ∧ d.tape d.pos = true ∧ step d = none) &&
            within n (some (startLocalWord w)) (-5) (7 + w.length : Int)

theorem haltCheckWord_sound (n : Nat) (w : List Bool)
    (hn : 0 < n) (hcheck : haltCheckWord n w = true) :
    ∃ d, run n (some (startLocalWord w)) = some d ∧
      d.state = 5 ∧ d.tape d.pos = true ∧ step d = none ∧
      Stays (-5) (7 + w.length : Int) n (some (startLocalWord w)) := by
  unfold haltCheckWord at hcheck
  cases hr : run (n - 1) (some (startLocalWord w)) with
  | none => simp [hr] at hcheck
  | some c0 =>
      cases hs : step c0 with
      | none => simp [hr, hs] at hcheck
      | some d =>
          simp only [hr, hs] at hcheck
          have hparts := Bool.and_eq_true_iff.mp hcheck
          rcases hparts with ⟨hdec, hwithin⟩
          have ⟨hstate, hhead, hhalt⟩ := of_decide_eq_true hdec
          have hlocal : run n (some (startLocalWord w)) = some d := by
            rw [← Nat.sub_add_cancel hn, run_succ_right]
            simp [hr, hs]
          exact ⟨d, hlocal, hstate, hhead, hhalt,
            (within_iff_Stays (-5) (7 + w.length : Int) n
              (some (startLocalWord w))).1 hwithin⟩

/- The formal cylinder theorem: ANY right extension ys and ANY alternating
   left stack of length m >= 3 halt by the indicated number of raw steps.
   All data-sensitive checks take place in the finite [-5,7+|w|] window. -/
theorem halts_with_arbitrary_suffix (n m : Nat) (w ys : List Bool)
    (hn : 0 < n) (hm : 3 ≤ m)
    (hc : haltCheckWord n w = true) :
    ∃ c, run n (some (startActualWord m (w ++ ys))) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  obtain ⟨d, hlocal, hstate, hhead, hhalt, hstay⟩ :=
    haltCheckWord_sound n w hn hc
  have hEq0 := initialWordEqOn m w ys hm
  have hrunEq := runEqOn (-5) (7 + w.length : Int) n
    (some (startLocalWord w)) (some (startActualWord m (w ++ ys)))
    hEq0 hstay
  rw [hlocal] at hrunEq
  cases hrun : run n (some (startActualWord m (w ++ ys))) with
  | none => simp only [hrun, OptionEqOn] at hrunEq
  | some c =>
      simp only [hrun, OptionEqOn] at hrunEq
      change ConfigEqOn (-5) (7 + w.length : Int) d c at hrunEq
      rcases hrunEq with ⟨hstate', hpos, htape⟩
      have hwin : -5 ≤ d.pos ∧ d.pos ≤ (7 + w.length : Int) := by
        simpa [hlocal] using
          (stays_run_pos (-5) (7 + w.length : Int) n
            (some (startLocalWord w)) hstay)
      have hread : c.tape c.pos = d.tape d.pos := by
        rw [← hpos]
        exact (htape d.pos hwin.1 hwin.2).symm
      have hcstate : c.state = 5 := hstate'.symm.trans hstate
      refine ⟨c, rfl, hcstate, ?_, ?_⟩
      · rw [hread]; exact hhead
      · simp [step, hcstate, hread, hhead, instr]

/- Prefix-free base set. Every individual boolean check is exact,
   and the universal theorem above upgrades it to arbitrary exterior. -/
theorem prefix_000 : haltCheckWord 113 [false,false,false] = true := by decide
theorem prefix_00100 : haltCheckWord 117 [false,false,true,false,false] = true := by decide
theorem prefix_01100 : haltCheckWord 74 [false,true,true,false,false] = true := by decide
theorem prefix_001100 : haltCheckWord 123 [false,false,true,true,false,false] = true := by decide
theorem prefix_010000 : haltCheckWord 127 [false,true,false,false,false,false] = true := by decide
theorem prefix_0010100 : haltCheckWord 121 [false,false,true,false,true,false,false] = true := by decide
theorem prefix_0110100 : haltCheckWord 78 [false,true,true,false,true,false,false] = true := by decide
theorem prefix_0110111 : haltCheckWord 131 [false,true,true,false,true,true,true] = true := by decide

/- This prefix-free trie has 64 leaves of length at most 12. Each entry
   (w,n) is checked as an exact finite raw trace; the single theorem below
   proves the entire union, rather than assuming results of a simulator. -/
def prefixTable : List (List Bool × Nat) := [
  ([false, false, false], 113),
  ([false, false, true, false, false], 117),
  ([false, true, true, false, false], 74),
  ([false, false, true, true, false, false], 123),
  ([false, true, false, false, false, false], 127),
  ([false, false, true, false, true, false, false], 121),
  ([false, true, true, false, true, false, false], 78),
  ([false, true, true, false, true, true, true], 131),
  ([false, false, true, false, true, true, false, false], 127),
  ([false, false, true, true, false, true, false, false], 127),
  ([false, false, true, true, false, true, true, true], 131),
  ([false, true, false, false, false, true, false, false], 131),
  ([false, true, false, false, false, true, true, true], 135),
  ([false, true, true, false, true, true, false, false], 81),
  ([false, false, true, false, true, false, true, false, false], 125),
  ([false, false, true, true, false, true, true, false, false], 169),
  ([false, true, false, false, false, true, true, false, false], 173),
  ([false, true, false, true, false, true, true, false, false], 131),
  ([false, true, true, false, true, false, true, false, false], 82),
  ([false, true, true, false, true, false, true, true, true], 137),
  ([false, false, true, false, true, false, true, true, false, false], 131),
  ([false, false, true, false, true, true, false, true, false, false], 131),
  ([false, false, true, false, true, true, false, true, true, true], 135),
  ([false, false, true, true, false, true, false, true, false, false], 131),
  ([false, false, true, true, false, true, false, true, true, true], 137),
  ([false, true, false, false, false, true, false, true, false, false], 135),
  ([false, true, false, false, false, true, false, true, true, true], 141),
  ([false, true, false, true, true, false, true, true, true, false], 153),
  ([false, true, true, false, true, false, true, true, false, false], 94),
  ([false, true, true, false, true, true, false, true, false, false], 85),
  ([false, true, true, false, true, true, false, true, true, true], 92),
  ([false, false, true, false, true, false, true, false, true, false, false], 129),
  ([false, false, true, false, true, true, false, true, true, false, false], 173),
  ([false, false, true, true, false, true, false, true, true, false, false], 137),
  ([false, false, true, true, false, true, true, false, true, false, false], 173),
  ([false, false, true, true, false, true, true, false, true, true, true], 141),
  ([false, true, false, false, false, true, false, true, true, false, false], 141),
  ([false, true, false, false, false, true, true, false, true, false, false], 177),
  ([false, true, false, false, false, true, true, false, true, true, true], 145),
  ([false, true, false, true, false, true, false, true, true, false, false], 153),
  ([false, true, false, true, false, true, true, false, true, false, false], 135),
  ([false, true, false, true, true, false, true, true, false, false, false], 129),
  ([false, true, true, false, true, false, true, false, true, false, false], 86),
  ([false, true, true, false, true, false, true, false, true, true, true], 143),
  ([false, true, true, false, true, true, false, true, true, false, false], 88),
  ([false, false, true, false, true, false, true, false, true, true, false, false], 135),
  ([false, false, true, false, true, false, true, true, false, true, false, false], 135),
  ([false, false, true, false, true, false, true, true, false, true, true, true], 139),
  ([false, false, true, false, true, true, false, true, false, true, false, false], 135),
  ([false, false, true, false, true, true, false, true, false, true, true, true], 141),
  ([false, false, true, true, false, true, false, true, false, true, false, false], 135),
  ([false, false, true, true, false, true, false, true, false, true, true, true], 143),
  ([false, false, true, true, false, true, true, false, true, true, false, false], 165),
  ([false, true, false, false, false, true, false, true, false, true, false, false], 139),
  ([false, true, false, false, false, true, false, true, false, true, true, true], 147),
  ([false, true, false, false, false, true, true, false, true, true, false, false], 169),
  ([false, true, false, true, true, false, true, false, true, true, true, false], 163),
  ([false, true, false, true, true, false, true, true, true, true, false, false], 157),
  ([false, true, false, true, true, false, true, true, true, true, true, true], 165),
  ([false, true, true, false, true, false, true, false, true, true, false, false], 92),
  ([false, true, true, false, true, false, true, true, false, true, false, false], 98),
  ([false, true, true, false, true, false, true, true, false, true, true, true], 96),
  ([false, true, true, false, true, true, false, true, false, true, false, false], 89),
  ([false, true, true, false, true, true, false, true, false, true, true, true], 98)
]

/- One kernel-evaluated, proof-carrying table certificate. -/
theorem prefixTable_checked :
    ∀ e ∈ prefixTable, 0 < e.2 ∧ haltCheckWord e.2 e.1 = true := by
  decide

/- Every table entry describes an infinite cylinder of halting right tapes,
   uniformly for all left pair-stack lengths m >= 3. -/
theorem all_prefix_table_halting (m n : Nat) (w ys : List Bool)
    (hm : 3 ≤ m) (hmem : (w,n) ∈ prefixTable) :
    ∃ c, run n (some (startActualWord m (w ++ ys))) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  have h := prefixTable_checked (w,n) hmem
  exact halts_with_arbitrary_suffix n m w ys h.1 hm h.2

#print axioms prefixTable_checked
#print axioms all_prefix_table_halting

#print axioms initialWordEqOn
#print axioms haltCheckWord_sound
#print axioms halts_with_arbitrary_suffix
#print axioms prefix_000
#print axioms prefix_01100
end TailWindow
