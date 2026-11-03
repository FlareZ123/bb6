import Lean.Elab.Tactic.Omega
import PacketSource

namespace BB6.Agent31PacketPaths
open CryptidBoundary BB6.Agent31PacketSource

structure State where
  a : Nat
  q : Nat
  p : Nat
  deriving Repr, DecidableEq

def rank (s : State) : Nat := s.q+s.p
def physical (s : State) (ys : List Bool) : Cfg := packet s.a s.q s.p ys

/-- The complete guarded packet source-identity relations, with primitive times. -/
inductive Edge : State → Nat → State → Prop
  | b (k q p : Nat) :
      Edge ⟨3*k+2, q+1, p⟩ (12*k*k+49*k+40) ⟨8*k+10, q, p⟩
  | e (k q p : Nat) :
      Edge ⟨3*k+4, q, p+3⟩ (12*k*k+49*k+58+6*q) ⟨8*k+9, q+2, p⟩

theorem edge_sound {s d : State} {duration : Nat} (h : Edge s duration d)
    (ys : List Bool) :
    run duration (physical s ys) = physical d ys := by
  cases h with
  | b k q p => exact b_packet k q p ys
  | e k q p => exact e_packet k q p ys

theorem edge_rank {s d : State} {duration : Nat}
    (h : Edge s duration d) : rank d+1=rank s := by
  cases h with
  | b k q p => simp [rank]; omega
  | e k q p => simp [rank]; omega

/-- Chains record number of B/E packet calls and exact cumulative raw time. -/
inductive Path : State → Nat → Nat → State → Prop
  | nil (s : State) : Path s 0 0 s
  | cons {s mid dst : State} {duration count cost : Nat}
      (h : Edge s duration mid)
      (hrest : Path mid count cost dst) :
      Path s (count+1) (duration+cost) dst

/-- Every guarded packet chain is an exact literal-machine run, any binary tail. -/
theorem path_sound {s dst : State} {count cost : Nat}
    (h : Path s count cost dst) (ys : List Bool) :
    run cost (physical s ys) = physical dst ys := by
  induction h with
  | nil s => rfl
  | cons h hs ih =>
    rw [run_add, edge_sound h ys, ih]

/-- Remaining rank and number of processed packets never exceed initial rank. -/
theorem path_rank_bound {s dst : State} {count cost : Nat}
    (h : Path s count cost dst) :
    count + rank dst ≤ rank s := by
  induction h with
  | nil s => omega
  | cons h hs ih =>
    have hr := edge_rank h
    omega

theorem path_count_bound {s dst : State} {count cost : Nat}
    (h : Path s count cost dst) : count ≤ s.q+s.p := by
  have ht := path_rank_bound h
  simp only [rank] at ht
  omega

#print axioms edge_sound
#print axioms edge_rank
#print axioms path_sound
#print axioms path_rank_bound
#print axioms path_count_bound
end BB6.Agent31PacketPaths
