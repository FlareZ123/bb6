import Mod384Graph
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Source-counter proof that the finite modulo-384 graph is a conservative
overapproximation of all genuine F321 seed trajectories. The exact source
CounterMove relation is imported, not postulated. The sole initial state
outside the graph is (1,1); its only outgoing transition is (6,1).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent31F321Mod384
open BB6.Agent31F321Density

theorem hit_of_mods {a d b c:Nat}
    (ha:a%384=b%384) (hd:d%384=c%384)
    (h:hit b c=true) : hit a d=true := by
  simpa only [hit,ha,hd] using h

theorem high_first_mod (a d:Nat) (h:d+2≤a) :
    (a-d-2)%384=(a%384+768-d%384-2)%384 := by omega

theorem high_second_mod (d:Nat) :
    (2*d+3)%384=(2*(d%384)+3)%384 := by omega

theorem far_first_mod (a:Nat) :
    (4*a+6)%384=(4*(a%384)+6)%384 := by omega

theorem far_second_mod (a d:Nat) (h:3*a+1≤d) :
    (d-3*a)%384=(d%384+1152-3*(a%384))%384 := by omega

theorem equal_first_mod (a:Nat) :
    (2*a+4)%384=(2*(a%384)+4)%384 := by omega

/-- For every actual live source-counter move, modulo-384 membership
is preserved by the checked nondeterministic superset graph. -/
theorem source_closed {a d A D:Nat}
    (h:CounterMove a d A D) (hl:hit a d=true) :
    hit A D=true := by
  let x : Fin 384 := ⟨a%384,Nat.mod_lt _ (by decide)⟩
  let y : Fin 384 := ⟨d%384,Nat.mod_lt _ (by decide)⟩
  have hxy:hit x.val y.val = true := by
    simpa [x,y,hit] using hl
  have hc:=closed_graph x y hxy
  cases h with
  | high d hg =>
    have hH:hit (H (a%384) (d%384)).1 (H (a%384) (d%384)).2=true := by
      simpa [x,y] using hc.1
    apply hit_of_mods (b:=(H (a%384) (d%384)).1) (c:=(H (a%384) (d%384)).2)
    · simpa only [H,Prod.fst,Nat.mod_mod] using high_first_mod a d hg
    · simpa only [H,Prod.snd,Nat.mod_mod] using high_second_mod d
    · exact hH
  | equal =>
    have hE:hit (E (a%384) (a%384)).1 (E (a%384) (a%384)).2=true := by
      simpa [x,y] using hc.2.2.2.2 rfl
    apply hit_of_mods (b:=(E (a%384) (a%384)).1) (c:=(E (a%384) (a%384)).2)
    · simpa only [E,Prod.fst,Nat.mod_mod] using equal_first_mod a
    · simp [E]
    · exact hE
  | far d h1 h2 =>
    have hF:hit (F (a%384) (d%384)).1 (F (a%384) (d%384)).2=true := by
      simpa [x,y] using hc.2.1
    apply hit_of_mods (b:=(F (a%384) (d%384)).1) (c:=(F (a%384) (d%384)).2)
    · simpa only [F,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simpa only [F,Prod.snd,Nat.mod_mod] using far_second_mod a d h2
    · exact hF
  | middleEven d h1 h2 hp =>
    have hM:hit (M2 (a%384) (d%384)).1 (M2 (a%384) (d%384)).2=true := by
      simpa [x,y] using (hc.2.2.2.1 (by omega))
    apply hit_of_mods (b:=(M2 (a%384) (d%384)).1) (c:=(M2 (a%384) (d%384)).2)
    · simpa only [M2,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simp [M2]
    · exact hM
  | middleOdd d h1 h2 hp =>
    have hM:hit (M1 (a%384) (d%384)).1 (M1 (a%384) (d%384)).2=true := by
      simpa [x,y] using (hc.2.2.1 (by omega))
    apply hit_of_mods (b:=(M1 (a%384) (d%384)).1) (c:=(M1 (a%384) (d%384)).2)
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

/-- New all-time zero-cutoff obstruction at d ≡ 373 (mod384).
The true seed (1,1) has no relation to a terminal H_d with d%384=373,
and the checked 384^2 graph excludes the pair residue (374,373). -/
theorem terminal373_never (d:Nat) (hd:d%384=373) :
    ∀ n, ¬CounterReach 1 1 n (d+1) d := by
  intro n hr
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · have hg : hit (d+1) d=false := by
      have ha : (d+1)%384=374 := by omega
      simpa [hit,ha,hd] using forbidden_gate_373
    rw [hg] at hl
    contradiction

#print axioms terminal373_never
#print axioms source_closed

/-- The source seed can reach a terminal gate only in 15 residue classes. -/
theorem terminal_mod384_candidates (d n : Nat)
  (hr : CounterReach 1 1 n (d+1) d) :
     d%384 ∈ possibleGates := by
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · have hx : hit ((d%384+1)%384) (d%384) = true := by
      simpa [hit, Nat.add_mod, Nat.mod_mod] using hl
    exact gate_table_complete ⟨d%384, Nat.mod_lt _ (by decide)⟩ hx

#print axioms terminal_mod384_candidates
end BB6.Agent31F321Mod384
