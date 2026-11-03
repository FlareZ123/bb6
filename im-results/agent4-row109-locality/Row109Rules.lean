import Row109Locality

namespace BB6.Row109Locality

/-
Generated from the exact 67 source-listed row109 block rewrites in
im-results/agent2-row109-semantic-audit/macro_rule_audit.cjs,
which embeds jhuang97/turing_machine pinned 6aeb2384173cf4c93a9a7c7f418bb9b39.
The two variable X^n rules are separately source-proved by Agent 2;
these 65 fixed clauses are checked here using complete primitive-step windows.
Each clause below gives an all-exterior universal theorem through
all_rules_universal, provided its explicitly listed input cylinder holds.
-/

-- Original rule 1: S0 < M M -> S0 < D1
def rule_0 : Certificate :=
  { beforeBits := 967, initialState := 4, initialHead := 3,
    afterBits := 967, afterShift := 0, finalState := 4,
    finalHead := 3, steps := 0, lo := 0, hi := 9 }
theorem rule_0_valid : accepted rule_0 = true := by decide

-- Original rule 2: D1 < M M -> D1 < D1
def rule_1 : Certificate :=
  { beforeBits := 975, initialState := 4, initialHead := 3,
    afterBits := 975, afterShift := 0, finalState := 4,
    finalHead := 3, steps := 0, lo := 0, hi := 9 }
theorem rule_1_valid : accepted rule_1 = true := by decide

-- Original rule 3: c> M M -> c> D1
def rule_2 : Certificate :=
  { beforeBits := 61, initialState := 2, initialHead := 2,
    afterBits := 61, afterShift := 0, finalState := 2,
    finalHead := 2, steps := 0, lo := 0, hi := 5 }
theorem rule_2_valid : accepted rule_2 = true := by decide

-- Original rule 4: e> M M -> e> D1
def rule_3 : Certificate :=
  { beforeBits := 63, initialState := 4, initialHead := 2,
    afterBits := 63, afterShift := 0, finalState := 4,
    finalHead := 2, steps := 0, lo := 0, hi := 5 }
theorem rule_3_valid : accepted rule_3 = true := by decide

-- Original rule 5: S0 < M U -> S0 < D0
def rule_4 : Certificate :=
  { beforeBits := 199, initialState := 4, initialHead := 3,
    afterBits := 199, afterShift := 0, finalState := 4,
    finalHead := 3, steps := 0, lo := 0, hi := 9 }
theorem rule_4_valid : accepted rule_4 = true := by decide

-- Original rule 6: D1 < M U -> D1 < D0
def rule_5 : Certificate :=
  { beforeBits := 207, initialState := 4, initialHead := 3,
    afterBits := 207, afterShift := 0, finalState := 4,
    finalHead := 3, steps := 0, lo := 0, hi := 9 }
theorem rule_5_valid : accepted rule_5 = true := by decide

-- Original rule 7: c> M R -> c> D0 R
def rule_6 : Certificate :=
  { beforeBits := 13, initialState := 2, initialHead := 2,
    afterBits := 13, afterShift := 0, finalState := 2,
    finalHead := 2, steps := 0, lo := 0, hi := 5 }
theorem rule_6_valid : accepted rule_6 = true := by decide

-- Original rule 8: e> M R -> e> D0 R
def rule_7 : Certificate :=
  { beforeBits := 15, initialState := 4, initialHead := 2,
    afterBits := 15, afterShift := 0, finalState := 4,
    finalHead := 2, steps := 0, lo := 0, hi := 5 }
theorem rule_7_valid : accepted rule_7 = true := by decide

-- Original rule 9: D1 <a -> < D1
def rule_8 : Certificate :=
  { beforeBits := 47, initialState := 0, initialHead := 3,
    afterBits := 60, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 16, lo := 0, hi := 5 }
theorem rule_8_valid : accepted rule_8 = true := by decide

-- Original rule 10: c> M D0 -> c> D1 U
def rule_9 : Certificate :=
  { beforeBits := 61, initialState := 2, initialHead := 2,
    afterBits := 61, afterShift := 0, finalState := 2,
    finalHead := 2, steps := 0, lo := 0, hi := 7 }
theorem rule_9_valid : accepted rule_9 = true := by decide

-- Original rule 11: e> M D0 -> e> D1 U
def rule_10 : Certificate :=
  { beforeBits := 63, initialState := 4, initialHead := 2,
    afterBits := 63, afterShift := 0, finalState := 4,
    finalHead := 2, steps := 0, lo := 0, hi := 7 }
theorem rule_10_valid : accepted rule_10 = true := by decide

-- Original rule 13: L < -> L X X c>
def rule_11 : Certificate :=
  { beforeBits := 0, initialState := 4, initialHead := -1,
    afterBits := 7, afterShift := -2, finalState := 2,
    finalHead := 2, steps := 11, lo := -2, hi := 1 }
theorem rule_11_valid : accepted rule_11 = true := by decide

-- Original rule 15: D1 < -> < D1
def rule_12 : Certificate :=
  { beforeBits := 15, initialState := 4, initialHead := 3,
    afterBits := 60, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 20, lo := 0, hi := 5 }
theorem rule_12_valid : accepted rule_12 = true := by decide

-- Original rule 16: S0 < -> < D0
def rule_13 : Certificate :=
  { beforeBits := 7, initialState := 4, initialHead := 3,
    afterBits := 12, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 8, lo := 0, hi := 5 }
theorem rule_13_valid : accepted rule_13 = true := by decide

-- Original rule 17: c> D0 -> S0 e>
def rule_14 : Certificate :=
  { beforeBits := 13, initialState := 2, initialHead := 2,
    afterBits := 55, afterShift := 0, finalState := 4,
    finalHead := 6, steps := 8, lo := 0, hi := 5 }
theorem rule_14_valid : accepted rule_14 = true := by decide

-- Original rule 18: e> D0 -> D1 c>
def rule_15 : Certificate :=
  { beforeBits := 15, initialState := 4, initialHead := 2,
    afterBits := 31, afterShift := 0, finalState := 2,
    finalHead := 6, steps := 10, lo := 0, hi := 5 }
theorem rule_15_valid : accepted rule_15 = true := by decide

-- Original rule 19: c> D1 -> D1 c>
def rule_16 : Certificate :=
  { beforeBits := 61, initialState := 2, initialHead := 2,
    afterBits := 31, afterShift := 0, finalState := 2,
    finalHead := 6, steps := 12, lo := 0, hi := 5 }
theorem rule_16_valid : accepted rule_16 = true := by decide

-- Original rule 20: e> D1 -> S0 e>
def rule_17 : Certificate :=
  { beforeBits := 63, initialState := 4, initialHead := 2,
    afterBits := 55, afterShift := 0, finalState := 4,
    finalHead := 6, steps := 6, lo := 0, hi := 5 }
theorem rule_17_valid : accepted rule_17 = true := by decide

-- Original rule 21: c> K -> M J D>
def rule_18 : Certificate :=
  { beforeBits := 5, initialState := 2, initialHead := 2,
    afterBits := 11, afterShift := 0, finalState := 3,
    finalHead := 4, steps := 4, lo := 0, hi := 3 }
theorem rule_18_valid : accepted rule_18 = true := by decide

-- Original rule 22: e> K -> M e>
def rule_19 : Certificate :=
  { beforeBits := 7, initialState := 4, initialHead := 2,
    afterBits := 15, afterShift := 0, finalState := 4,
    finalHead := 4, steps := 2, lo := 0, hi := 3 }
theorem rule_19_valid : accepted rule_19 = true := by decide

-- Original rule 23: F> K -> M B>
def rule_20 : Certificate :=
  { beforeBits := 1, initialState := 5, initialHead := 0,
    afterBits := 3, afterShift := 0, finalState := 1,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_20_valid : accepted rule_20 = true := by decide

-- Original rule 24: D> K -> J E>
def rule_21 : Certificate :=
  { beforeBits := 1, initialState := 3, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 4,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_21_valid : accepted rule_21 = true := by decide

-- Original rule 25: E> K -> e>
def rule_22 : Certificate :=
  { beforeBits := 1, initialState := 4, initialHead := 0,
    afterBits := 3, afterShift := 0, finalState := 4,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_22_valid : accepted rule_22 = true := by decide

-- Original rule 26: a> K -> <C K J
def rule_23 : Certificate :=
  { beforeBits := 6, initialState := 0, initialHead := 2,
    afterBits := 9, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 7, lo := 0, hi := 3 }
theorem rule_23_valid : accepted rule_23 = true := by decide

-- Original rule 27: c> J -> K K F>
def rule_24 : Certificate :=
  { beforeBits := 9, initialState := 2, initialHead := 2,
    afterBits := 5, afterShift := 0, finalState := 5,
    finalHead := 4, steps := 2, lo := 0, hi := 3 }
theorem rule_24_valid : accepted rule_24 = true := by decide

-- Original rule 28: e> J -> < M
def rule_25 : Certificate :=
  { beforeBits := 11, initialState := 4, initialHead := 2,
    afterBits := 12, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 3, lo := 0, hi := 3 }
theorem rule_25_valid : accepted rule_25 = true := by decide

-- Original rule 29: F> J -> M D>
def rule_26 : Certificate :=
  { beforeBits := 2, initialState := 5, initialHead := 0,
    afterBits := 3, afterShift := 0, finalState := 3,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_26_valid : accepted rule_26 = true := by decide

-- Original rule 30: D> J -> M D>
def rule_27 : Certificate :=
  { beforeBits := 2, initialState := 3, initialHead := 0,
    afterBits := 3, afterShift := 0, finalState := 3,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_27_valid : accepted rule_27 = true := by decide

-- Original rule 31: B> J -> c>
def rule_28 : Certificate :=
  { beforeBits := 2, initialState := 1, initialHead := 0,
    afterBits := 1, afterShift := 0, finalState := 2,
    finalHead := 2, steps := 4, lo := 0, hi := 1 }
theorem rule_28_valid : accepted rule_28 = true := by decide

-- Original rule 32: E> J -> <C M
def rule_29 : Certificate :=
  { beforeBits := 2, initialState := 4, initialHead := 0,
    afterBits := 3, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 1, lo := 0, hi := 1 }
theorem rule_29_valid : accepted rule_29 = true := by decide

-- Original rule 33: c> M -> M c>
def rule_30 : Certificate :=
  { beforeBits := 13, initialState := 2, initialHead := 2,
    afterBits := 7, afterShift := 0, finalState := 2,
    finalHead := 4, steps := 6, lo := 0, hi := 3 }
theorem rule_30_valid : accepted rule_30 = true := by decide

-- Original rule 34: e> M -> M K F>
def rule_31 : Certificate :=
  { beforeBits := 15, initialState := 4, initialHead := 2,
    afterBits := 7, afterShift := 0, finalState := 5,
    finalHead := 4, steps := 2, lo := 0, hi := 3 }
theorem rule_31_valid : accepted rule_31 = true := by decide

-- Original rule 35: F> M -> e>
def rule_32 : Certificate :=
  { beforeBits := 3, initialState := 5, initialHead := 0,
    afterBits := 3, afterShift := 0, finalState := 4,
    finalHead := 2, steps := 4, lo := 0, hi := 1 }
theorem rule_32_valid : accepted rule_32 = true := by decide

-- Original rule 36: D> M -> a>
def rule_33 : Certificate :=
  { beforeBits := 3, initialState := 3, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 0,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_33_valid : accepted rule_33 = true := by decide

-- Original rule 37: E> M -> K F>
def rule_34 : Certificate :=
  { beforeBits := 3, initialState := 4, initialHead := 0,
    afterBits := 1, afterShift := 0, finalState := 5,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_34_valid : accepted rule_34 = true := by decide

-- Original rule 38: a> M -> J M D>
def rule_35 : Certificate :=
  { beforeBits := 14, initialState := 0, initialHead := 2,
    afterBits := 14, afterShift := 0, finalState := 3,
    finalHead := 4, steps := 4, lo := 0, hi := 3 }
theorem rule_35_valid : accepted rule_35 = true := by decide

-- Original rule 39: c> U -> K e>
def rule_36 : Certificate :=
  { beforeBits := 1, initialState := 2, initialHead := 2,
    afterBits := 13, afterShift := 0, finalState := 4,
    finalHead := 4, steps := 2, lo := 0, hi := 3 }
theorem rule_36_valid : accepted rule_36 = true := by decide

-- Original rule 40: e> U -> < K
def rule_37 : Certificate :=
  { beforeBits := 3, initialState := 4, initialHead := 2,
    afterBits := 4, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 3, lo := 0, hi := 3 }
theorem rule_37_valid : accepted rule_37 = true := by decide

-- Original rule 41: F> U -> <a
def rule_38 : Certificate :=
  { beforeBits := 0, initialState := 5, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 0,
    finalHead := -1, steps := 3, lo := 0, hi := 1 }
theorem rule_38_valid : accepted rule_38 = true := by decide

-- Original rule 42: D> U -> <a
def rule_39 : Certificate :=
  { beforeBits := 0, initialState := 3, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 0,
    finalHead := -1, steps := 3, lo := 0, hi := 1 }
theorem rule_39_valid : accepted rule_39 = true := by decide

-- Original rule 43: B> U -> J D>
def rule_40 : Certificate :=
  { beforeBits := 0, initialState := 1, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 3,
    finalHead := 2, steps := 2, lo := 0, hi := 1 }
theorem rule_40_valid : accepted rule_40 = true := by decide

-- Original rule 44: E> U -> <C K
def rule_41 : Certificate :=
  { beforeBits := 0, initialState := 4, initialHead := 0,
    afterBits := 1, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 1, lo := 0, hi := 1 }
theorem rule_41_valid : accepted rule_41 = true := by decide

-- Original rule 45: a> U -> J c>
def rule_42 : Certificate :=
  { beforeBits := 2, initialState := 0, initialHead := 2,
    afterBits := 6, afterShift := 0, finalState := 2,
    finalHead := 4, steps := 2, lo := 0, hi := 3 }
theorem rule_42_valid : accepted rule_42 = true := by decide

-- Original rule 46: c> R -> <a U K R
def rule_43 : Certificate :=
  { beforeBits := 1, initialState := 2, initialHead := 2,
    afterBits := 18, afterShift := 0, finalState := 0,
    finalHead := -1, steps := 7, lo := 0, hi := 5 }
theorem rule_43_valid : accepted rule_43 = true := by decide

-- Original rule 47: e> R -> < K R
def rule_44 : Certificate :=
  { beforeBits := 3, initialState := 4, initialHead := 2,
    afterBits := 4, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 3, lo := 0, hi := 3 }
theorem rule_44_valid : accepted rule_44 = true := by decide

-- Original rule 48: F> R -> <a R
def rule_45 : Certificate :=
  { beforeBits := 0, initialState := 5, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 0,
    finalHead := -1, steps := 3, lo := 0, hi := 1 }
theorem rule_45_valid : accepted rule_45 = true := by decide

-- Original rule 49: D> R -> <a R
def rule_46 : Certificate :=
  { beforeBits := 0, initialState := 3, initialHead := 0,
    afterBits := 2, afterShift := 0, finalState := 0,
    finalHead := -1, steps := 3, lo := 0, hi := 1 }
theorem rule_46_valid : accepted rule_46 = true := by decide

-- Original rule 50: B> R -> <C K J R
def rule_47 : Certificate :=
  { beforeBits := 0, initialState := 1, initialHead := 0,
    afterBits := 9, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 7, lo := 0, hi := 3 }
theorem rule_47_valid : accepted rule_47 = true := by decide

-- Original rule 51: E> R -> <C K R
def rule_48 : Certificate :=
  { beforeBits := 0, initialState := 4, initialHead := 0,
    afterBits := 1, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 1, lo := 0, hi := 1 }
theorem rule_48_valid : accepted rule_48 = true := by decide

-- Original rule 52: a> R -> <C K J U K R
def rule_49 : Certificate :=
  { beforeBits := 2, initialState := 0, initialHead := 2,
    afterBits := 73, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 11, lo := 0, hi := 7 }
theorem rule_49_valid : accepted rule_49 = true := by decide

-- Original rule 53: K < -> <a U
def rule_50 : Certificate :=
  { beforeBits := 1, initialState := 4, initialHead := 1,
    afterBits := 2, afterShift := 0, finalState := 0,
    finalHead := -1, steps := 2, lo := 0, hi := 3 }
theorem rule_50_valid : accepted rule_50 = true := by decide

-- Original rule 54: K <a -> M c>
def rule_51 : Certificate :=
  { beforeBits := 9, initialState := 0, initialHead := 1,
    afterBits := 7, afterShift := 0, finalState := 2,
    finalHead := 4, steps := 5, lo := 0, hi := 3 }
theorem rule_51_valid : accepted rule_51 = true := by decide

-- Original rule 55: K <C -> M D>
def rule_52 : Certificate :=
  { beforeBits := 1, initialState := 2, initialHead := 1,
    afterBits := 3, afterShift := 0, finalState := 3,
    finalHead := 2, steps := 1, lo := 0, hi := 1 }
theorem rule_52_valid : accepted rule_52 = true := by decide

-- Original rule 56: M < -> < M
def rule_53 : Certificate :=
  { beforeBits := 3, initialState := 4, initialHead := 1,
    afterBits := 12, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 10, lo := 0, hi := 3 }
theorem rule_53_valid : accepted rule_53 = true := by decide

-- Original rule 57: M <a -> < M
def rule_54 : Certificate :=
  { beforeBits := 11, initialState := 0, initialHead := 1,
    afterBits := 12, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 6, lo := 0, hi := 3 }
theorem rule_54_valid : accepted rule_54 = true := by decide

-- Original rule 58: M <C -> <
def rule_55 : Certificate :=
  { beforeBits := 3, initialState := 2, initialHead := 1,
    afterBits := 0, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 2, lo := 0, hi := 1 }
theorem rule_55_valid : accepted rule_55 = true := by decide

-- Original rule 59: J < -> <C K J
def rule_56 : Certificate :=
  { beforeBits := 2, initialState := 4, initialHead := 1,
    afterBits := 9, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 6, lo := 0, hi := 3 }
theorem rule_56_valid : accepted rule_56 = true := by decide

-- Original rule 60: J <a -> <C K J
def rule_57 : Certificate :=
  { beforeBits := 10, initialState := 0, initialHead := 1,
    afterBits := 9, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 2, lo := 0, hi := 3 }
theorem rule_57_valid : accepted rule_57 = true := by decide

-- Original rule 61: J <C -> c>
def rule_58 : Certificate :=
  { beforeBits := 2, initialState := 2, initialHead := 1,
    afterBits := 1, afterShift := 0, finalState := 2,
    finalHead := 2, steps := 3, lo := 0, hi := 1 }
theorem rule_58_valid : accepted rule_58 = true := by decide

-- Original rule 62: D> D1 -> J M D>
def rule_59 : Certificate :=
  { beforeBits := 15, initialState := 3, initialHead := 0,
    afterBits := 14, afterShift := 0, finalState := 3,
    finalHead := 4, steps := 6, lo := 0, hi := 3 }
theorem rule_59_valid : accepted rule_59 = true := by decide

-- Original rule 63: F> D1 -> M K F>
def rule_60 : Certificate :=
  { beforeBits := 15, initialState := 5, initialHead := 0,
    afterBits := 7, afterShift := 0, finalState := 5,
    finalHead := 4, steps := 6, lo := 0, hi := 3 }
theorem rule_60_valid : accepted rule_60 = true := by decide

-- Original rule 64: a> D1 -> J M a>
def rule_61 : Certificate :=
  { beforeBits := 62, initialState := 0, initialHead := 2,
    afterBits := 46, afterShift := 0, finalState := 0,
    finalHead := 6, steps := 6, lo := 0, hi := 5 }
theorem rule_61_valid : accepted rule_61 = true := by decide

-- Original rule 65: D> D0 -> J c>
def rule_62 : Certificate :=
  { beforeBits := 3, initialState := 3, initialHead := 0,
    afterBits := 6, afterShift := 0, finalState := 2,
    finalHead := 4, steps := 4, lo := 0, hi := 3 }
theorem rule_62_valid : accepted rule_62 = true := by decide

-- Original rule 66: F> D0 -> < K
def rule_63 : Certificate :=
  { beforeBits := 3, initialState := 5, initialHead := 0,
    afterBits := 4, afterShift := 0, finalState := 4,
    finalHead := -1, steps := 7, lo := 0, hi := 3 }
theorem rule_63_valid : accepted rule_63 = true := by decide

-- Original rule 67: a> D0 -> <C K J M
def rule_64 : Certificate :=
  { beforeBits := 14, initialState := 0, initialHead := 2,
    afterBits := 57, afterShift := 0, finalState := 2,
    finalHead := -1, steps := 19, lo := 0, hi := 5 }
theorem rule_64_valid : accepted rule_64 = true := by decide

def allRules : List Certificate := [rule_0, rule_1, rule_2, rule_3, rule_4, rule_5, rule_6, rule_7, rule_8, rule_9, rule_10, rule_11, rule_12, rule_13, rule_14, rule_15, rule_16, rule_17, rule_18, rule_19, rule_20, rule_21, rule_22, rule_23, rule_24, rule_25, rule_26, rule_27, rule_28, rule_29, rule_30, rule_31, rule_32, rule_33, rule_34, rule_35, rule_36, rule_37, rule_38, rule_39, rule_40, rule_41, rule_42, rule_43, rule_44, rule_45, rule_46, rule_47, rule_48, rule_49, rule_50, rule_51, rule_52, rule_53, rule_54, rule_55, rule_56, rule_57, rule_58, rule_59, rule_60, rule_61, rule_62, rule_63, rule_64]

theorem all_valid : allRules.all accepted = true := by
  simp [allRules, rule_0_valid, rule_1_valid, rule_2_valid, rule_3_valid, rule_4_valid, rule_5_valid, rule_6_valid, rule_7_valid, rule_8_valid, rule_9_valid, rule_10_valid, rule_11_valid, rule_12_valid, rule_13_valid, rule_14_valid, rule_15_valid, rule_16_valid, rule_17_valid, rule_18_valid, rule_19_valid, rule_20_valid, rule_21_valid, rule_22_valid, rule_23_valid, rule_24_valid, rule_25_valid, rule_26_valid, rule_27_valid, rule_28_valid, rule_29_valid, rule_30_valid, rule_31_valid, rule_32_valid, rule_33_valid, rule_34_valid, rule_35_valid, rule_36_valid, rule_37_valid, rule_38_valid, rule_39_valid, rule_40_valid, rule_41_valid, rule_42_valid, rule_43_valid, rule_44_valid, rule_45_valid, rule_46_valid, rule_47_valid, rule_48_valid, rule_49_valid, rule_50_valid, rule_51_valid, rule_52_valid, rule_53_valid, rule_54_valid, rule_55_valid, rule_56_valid, rule_57_valid, rule_58_valid, rule_59_valid, rule_60_valid, rule_61_valid, rule_62_valid, rule_63_valid, rule_64_valid]

theorem all_rules_universal (r : Certificate) (hr : r ∈ allRules)
    (t : Int → Bool)
    (ht : ∀ p, InWindow r.lo r.hi p → t p = wordTape r.beforeBits p) :
    let out := run r.steps {st := r.initialState, h := r.initialHead, tape := t}
    out.st = r.finalState ∧ out.h = r.finalHead ∧
    ∀ p, out.tape p =
      (if r.lo ≤ p ∧ p ≤ r.hi then wordTape r.afterBits (p - r.afterShift)
      else t p) := by
  exact accepted_sound r ((List.all_eq_true.mp all_valid) r hr) t ht

#print axioms all_valid
#print axioms all_rules_universal
end BB6.Row109Locality
