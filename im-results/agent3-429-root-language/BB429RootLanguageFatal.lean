import Frontier429
import Lean.Elab.Tactic.Omega
namespace BB429RootLanguageFatal
open Frontier429

private theorem c0_to_e0 (m : Nat) :
    run 10 ⟨2,[true,false,true,true,true,false] ++ ones2 m ++ [false],false,[]⟩ =
    some ⟨4,ones2 m ++ [false],false,[true,true,true,true,true,false,true]⟩ := by
  rfl

private theorem e0_even_left_to_A (m : Nat) (r : List Bool) :
    run (2*m+1) ⟨4,ones2 m ++ [false],false,r⟩ =
    some ⟨0,[],false,pairs m ++ false::r⟩ := by
  cases m with
  | zero => rfl
  | succ m =>
      have h1 : run 1 ⟨4,ones2 (m+1) ++ [false],false,r⟩ =
          some (ae (m+1) [] (false::r)) := by rfl
      rw [show 2*(m+1)+1=1+2*(m+1) by omega,run_add,h1]
      simp only [Option.bind_some]
      simpa only [ae] using ae_sweep (m+1) [] (false::r)

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

private theorem a0_ten_to_a1 (m : Nat) :
    run 10 ⟨0,ones2 m,false,[false,true,true,true,true,true,false,true]⟩ =
    some ⟨0,ones2 (m+3),true,[false,true]⟩ := by
  simp only [show m+3=(m+1)+2 by omega]
  rfl

private theorem a1_four_to_e0 (r : List Bool) :
    run 4 ⟨0,[],true,r⟩ =
    some ⟨4,[],false,[true,true] ++ r⟩ := by rfl

private theorem a0_terminal (m : Nat) :
    run (2*(m+3)+8)
      ⟨0,[],false,[false,true,true] ++ pairs (m+3) ++ [false,true]⟩ =
    some ⟨2,pairs (m+2) ++ ones2 3,false,[true]⟩ := by
  have h8 := odd_first8 (m+2) ([] : List Bool)
  have h2 := odd_a2c (m+2) (ones2 2)
  have hs := cp_sweep (m+2) (ones2 3)
  have heq : ones2 3 = true::true::ones2 2 := by rfl
  have hsum : 2*(m+3)+8=8+(2+2*(m+2)) := by omega
  rw [hsum,run_add,h8]
  simp only [Option.bind_some]
  simp only [List.append_nil]
  rw [run_add,h2]
  simp only [Option.bind_some]
  rw [show true::true::ones2 2=ones2 3 by rfl, hs]
  rfl

/-- On the literal #429 source table, all prepared C/0 tapes with
nearest-first left word `1011101^(2m)` and entirely blank right tape
reach C/0 again with right neighbor 1. This family lies inside the
candidate grammar seen on the actual blank-run frontier. -/
theorem root_grammar_contains_fatal_family (m : Nat) :
    run (46+8*m)
      ⟨2,[true,false,true,true,true,false] ++ ones2 m ++ [false],false,[]⟩ =
    some ⟨2,pairs (m+2) ++ ones2 3,false,[true]⟩ := by
  have h0 := c0_to_e0 m
  have h1 := e0_even_left_to_A m [true,true,true,true,true,false,true]
  have h2 := ab_sweep m [] [false,true,true,true,true,true,false,true]
  have h3 := a0_ten_to_a1 m
  have h4 := af_sweep (m+3) [] [false,true]
  have h5 := a1_four_to_e0 (pairs (m+3) ++ [false,true])
  have h6 : run 1 ⟨4,[],false,[true,true] ++ pairs (m+3) ++ [false,true]⟩ =
      some ⟨0,[],false,[false,true,true] ++ pairs (m+3) ++ [false,true]⟩ := by rfl
  have h7 := a0_terminal m
  have ht : 46+8*m = 10 + ((2*m+1) + (2*m + (10 + (2*(m+3) + (4 + (1 + (2*(m+3)+8))))))) := by omega
  rw [ht,run_add,h0]
  simp only [Option.bind_some]
  rw [run_add,h1]
  simp only [Option.bind_some]
  rw [run_add,h2]
  simp only [Option.bind_some]
  simp only [List.append_nil]
  rw [run_add,h3]
  simp only [Option.bind_some]
  simp only [List.append_nil] at h4
  rw [run_add,h4]
  simp only [Option.bind_some]
  rw [run_add,h5]
  simp only [Option.bind_some]
  simp only [List.append_assoc] at h6
  rw [run_add,h6]
  simp only [Option.bind_some]
  exact h7

/-- One source transition after the marked-right C/0 gate reaches D/1;
    the following halt query is undefined. -/
theorem root_grammar_fatal_halts (m : Nat) :
    run (48+8*m)
      ⟨2,[true,false,true,true,true,false] ++ ones2 m ++ [false],false,[]⟩ = none := by
  rw [show 48+8*m=(46+8*m)+2 by omega,run_add,
    root_grammar_contains_fatal_family]
  rfl

#print axioms root_grammar_contains_fatal_family
#print axioms root_grammar_fatal_halts
end BB429RootLanguageFatal
