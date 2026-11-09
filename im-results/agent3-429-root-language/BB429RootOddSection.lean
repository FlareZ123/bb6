import BB429RootPairNormalizer
import Lean.Elab.Tactic.Omega

namespace BB429RootOddSection
open Frontier429

private theorem af_pair (l r : List Bool) :
    run 2 ⟨0,true::true::l,true,r⟩ =
    some ⟨0,l,true,true::false::r⟩ := by rfl

private theorem af_sweep (m : Nat) (l r : List Bool) :
    run (2*m) ⟨0,ones2 m ++ l,true,r⟩ =
    some ⟨0,l,true,pairs m ++ r⟩ := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
      rw [show 2*(m+1)=2+2*m by omega,run_add]
      simp only [ones2, List.cons_append, af_pair, Option.bind_some]
      rw [ih]
      simp only [pairs_succ_tail, List.append_assoc, List.cons_append, List.nil_append]

private theorem first3 (k : Nat) (l : List Bool) :
    run 3 ⟨2, true :: ones2 (k+1) ++ (false :: true :: false :: l), false, []⟩ =
      some ⟨0,ones2 (k+1) ++ (false :: true :: false :: l),true,[false,true]⟩ := by
  simpa only [List.cons_append] using cdeBlank true
      (ones2 (k+1) ++ (false :: true :: false :: l))

private theorem last5 (k : Nat) (l : List Bool) :
    run 5 ⟨0,false :: true :: false :: l,true,pairs (k+1) ++ [false,true]⟩ =
      some ⟨4,l,false,[true,true,true,true,false] ++ pairs k ++ [false,true]⟩ := by
  rfl

/-- Exact original-table C/0 prefix into E/0, for every initial odd block
    length 2k+3 and arbitrary unexamined left tail. -/
theorem c0_odd_prefix_to_e0 (k : Nat) (l : List Bool) :
    run (2*k+10)
      ⟨2,true :: ones2 (k+1) ++ (false :: true :: false :: l),false,[]⟩ =
    some ⟨4,l,false,[true,true,true,true,false] ++ pairs k ++ [false,true]⟩ := by
  have htime : 2*k+10 = 3+(2*(k+1)+5) := by omega
  rw [htime,run_add,first3]
  simp only [Option.bind_some]
  rw [run_add,af_sweep]
  simp only [Option.bind_some]
  exact last5 k l

/-- An infinite family of exact nonterminal E/0 endpoint states, after
    removing 2n alternating 10 pairs from the left through original
    six-state primitive steps. No time or parameter cutoff. -/
theorem c0_odd_pairs_to_e0 (k n : Nat) (l : List Bool) :
    run (2*k+10+6*n)
      ⟨2,true :: ones2 (k+1) ++
           (false :: true :: false :: BB429RootPairNormalizer.inWords n ++ l),false,[]⟩ =
    some ⟨4,l,false,BB429RootPairNormalizer.outWords n ++
                   ([true,true,true,true,false] ++ pairs k ++ [false,true])⟩ := by
  have hpref : run (2*k+10)
      ⟨2,true :: ones2 (k+1) ++
        (false :: true :: false :: BB429RootPairNormalizer.inWords n ++ l),false,[]⟩ =
      some ⟨4, BB429RootPairNormalizer.inWords n ++ l,false,
        [true,true,true,true,false] ++ pairs k ++ [false,true]⟩ := by
    simpa only [List.cons_append, List.append_assoc] using
      (c0_odd_prefix_to_e0 k (BB429RootPairNormalizer.inWords n ++ l))
  rw [run_add, hpref]
  simp only [Option.bind_some]
  exact BB429RootPairNormalizer.e0_pair_normalize n l _

#print axioms c0_odd_prefix_to_e0
#print axioms c0_odd_pairs_to_e0
end BB429RootOddSection
