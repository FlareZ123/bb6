module

public import Agent19P1HaltingBridge
public import P1ReachBridge

@[expose] public section

namespace BB6.Agent22P1
open BusyBeaver

/-- The original six-state blank-tape machine has a halting run exactly
when its certified sparse P1 gate reaches an exponent outside the newly
excluded full residue class 10 modulo 16. -/
theorem raw_halts_iff_surviving_critical_index :
    IsHalt BB6.P1Bridge.Source.target ↔
    ∃ n : Nat, n%16 ≠ 10 ∧
      BB6.HaltingFunnel.ReachT 2 1 2 (14*2^n-2*n-10) := by
  constructor
  · intro h
    obtain ⟨n,hr⟩ := BB6.P1Bridge.raw_halts_iff_sparse_gate.mp h
    refine ⟨n, ?_, hr⟩
    intro hn
    have hs : n = 16*(n/16)+10 := by
      have hd := Nat.mod_add_div n 16
      omega
    rw [hs] at hr
    exact blank_reachT_excludes_10_mod16 (n/16) hr
  · rintro ⟨n,_,hr⟩
    exact BB6.P1Bridge.raw_halts_iff_sparse_gate.mpr ⟨n,hr⟩

#print axioms BB6.Agent22P1.raw_halts_iff_surviving_critical_index
end BB6.Agent22P1
