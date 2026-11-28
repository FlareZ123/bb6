import Mod96Graph
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Source-counter proof that the finite modulo-96 graph is a conservative
overapproximation of all genuine F321 seed trajectories. The exact source
CounterMove relation is imported, not postulated. The sole initial state
outside the graph is (1,1); its only outgoing transition is (6,1).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent2F321Mod96
open BB6.Agent31F321Density

theorem hit_of_mods {a d b c:Nat}
    (ha:a%96=b%96) (hd:d%96=c%96)
    (h:hit b c=true) : hit a d=true := by
  simpa only [hit,ha,hd] using h

theorem high_first_mod (a d:Nat) (h:d+2≤a) :
    (a-d-2)%96=(a%96+192-d%96-2)%96 := by omega

theorem high_second_mod (d:Nat) :
    (2*d+3)%96=(2*(d%96)+3)%96 := by omega

theorem far_first_mod (a:Nat) :
    (4*a+6)%96=(4*(a%96)+6)%96 := by omega

theorem far_second_mod (a d:Nat) (h:3*a+1≤d) :
    (d-3*a)%96=(d%96+288-3*(a%96))%96 := by omega

theorem equal_first_mod (a:Nat) :
    (2*a+4)%96=(2*(a%96)+4)%96 := by omega

/-- For every actual live source-counter move, modulo-96 membership
is preserved by the checked nondeterministic superset graph. -/
theorem source_closed {a d A D:Nat}
    (h:CounterMove a d A D) (hl:hit a d=true) :
    hit A D=true := by
  let x : Fin 96 := ⟨a%96,Nat.mod_lt _ (by decide)⟩
  let y : Fin 96 := ⟨d%96,Nat.mod_lt _ (by decide)⟩
  have hxy:hit x.val y.val = true := by
    simpa [x,y,hit] using hl
  have hc:=closed_graph x y hxy
  cases h with
  | high d hg =>
    have hH:hit (H (a%96) (d%96)).1 (H (a%96) (d%96)).2=true := by
      simpa [x,y] using hc.1
    apply hit_of_mods (b:=(H (a%96) (d%96)).1) (c:=(H (a%96) (d%96)).2)
    · simpa only [H,Prod.fst,Nat.mod_mod] using high_first_mod a d hg
    · simpa only [H,Prod.snd,Nat.mod_mod] using high_second_mod d
    · exact hH
  | equal =>
    have hE:hit (E (a%96) (a%96)).1 (E (a%96) (a%96)).2=true := by
      simpa [x,y] using hc.2.2.2.2 rfl
    apply hit_of_mods (b:=(E (a%96) (a%96)).1) (c:=(E (a%96) (a%96)).2)
    · simpa only [E,Prod.fst,Nat.mod_mod] using equal_first_mod a
    · simp [E]
    · exact hE
  | far d h1 h2 =>
    have hF:hit (F (a%96) (d%96)).1 (F (a%96) (d%96)).2=true := by
      simpa [x,y] using hc.2.1
    apply hit_of_mods (b:=(F (a%96) (d%96)).1) (c:=(F (a%96) (d%96)).2)
    · simpa only [F,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simpa only [F,Prod.snd,Nat.mod_mod] using far_second_mod a d h2
    · exact hF
  | middleEven d h1 h2 hp =>
    have hM:hit (M2 (a%96) (d%96)).1 (M2 (a%96) (d%96)).2=true := by
      simpa [x,y] using hc.2.2.2.1
    apply hit_of_mods (b:=(M2 (a%96) (d%96)).1) (c:=(M2 (a%96) (d%96)).2)
    · simpa only [M2,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simp [M2]
    · exact hM
  | middleOdd d h1 h2 hp =>
    have hM:hit (M1 (a%96) (d%96)).1 (M1 (a%96) (d%96)).2=true := by
      simpa [x,y] using hc.2.2.1
    apply hit_of_mods (b:=(M1 (a%96) (d%96)).1) (c:=(M1 (a%96) (d%96)).2)
    · simpa only [M1,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simp [M1]
    · exact hM

theorem seed_only_equal {A D:Nat}
    (h:CounterMove 1 1 A D) : A=6 ∧ D=1 := by
  cases h <;> omega

theorem source_reached_live_or_seed {n a d:Nat}
    (hr:CounterReach 1 1 n a d) :
    (a=1 ∧ d=1) ∨ hit a d=true := by
  induction hr with
  | nil => exact Or.inl ⟨rfl,rfl⟩
  | @step n a d A D hr hm ih =>
    rcases ih with ⟨ha,hd⟩ | hl
    · have hn : A=6 ∧ D=1 := seed_only_equal (by simpa [ha,hd] using hm)
      exact Or.inr (by simpa only [hn.1,hn.2] using seed_live)
    · exact Or.inr (source_closed hm hl)

/-- New all-time zero-cutoff obstruction at d ≡ 13 (mod96).
The true seed (1,1) has no relation to a terminal H_d with d%96=13,
and the checked 96^2 graph excludes the pair residue (14,13). -/
theorem terminal13_never (d:Nat) (hd:d%96=13) :
    ∀ n, ¬CounterReach 1 1 n (d+1) d := by
  intro n hr
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · have hg : hit (d+1) d=false := by
      have ha : (d+1)%96=14 := by omega
      simpa [hit,ha,hd] using forbidden_gate_13
    rw [hg] at hl
    contradiction

#print axioms terminal13_never
#print axioms source_closed
end BB6.Agent2F321Mod96
