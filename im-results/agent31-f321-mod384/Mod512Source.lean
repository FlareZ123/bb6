import Mod512Graph
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Source-counter proof that the finite modulo-512 graph is a conservative
overapproximation of all genuine F321 seed trajectories. The exact source
CounterMove relation is imported, not postulated. The sole initial state
outside the graph is (1,1); its only outgoing transition is (6,1).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent31F321Mod512
open BB6.Agent31F321Density

theorem hit_of_mods {a d b c:Nat}
    (ha:a%512=b%512) (hd:d%512=c%512)
    (h:hit b c=true) : hit a d=true := by
  simpa only [hit,ha,hd] using h

theorem high_first_mod (a d:Nat) (h:d+2≤a) :
    (a-d-2)%512=(a%512+1024-d%512-2)%512 := by omega

theorem high_second_mod (d:Nat) :
    (2*d+3)%512=(2*(d%512)+3)%512 := by omega

theorem far_first_mod (a:Nat) :
    (4*a+6)%512=(4*(a%512)+6)%512 := by omega

theorem far_second_mod (a d:Nat) (h:3*a+1≤d) :
    (d-3*a)%512=(d%512+1536-3*(a%512))%512 := by omega

theorem equal_first_mod (a:Nat) :
    (2*a+4)%512=(2*(a%512)+4)%512 := by omega

/-- For every actual live source-counter move, modulo-512 membership
is preserved by the checked nondeterministic superset graph. -/
theorem source_closed {a d A D:Nat}
    (h:CounterMove a d A D) (hl:hit a d=true) :
    hit A D=true := by
  let x : Fin 512 := ⟨a%512,Nat.mod_lt _ (by decide)⟩
  let y : Fin 512 := ⟨d%512,Nat.mod_lt _ (by decide)⟩
  have hxy:hit x.val y.val = true := by
    simpa [x,y,hit] using hl
  have hc:=closed_graph x y hxy
  cases h with
  | high d hg =>
    have hH:hit (H (a%512) (d%512)).1 (H (a%512) (d%512)).2=true := by
      simpa [x,y] using hc.1
    apply hit_of_mods (b:=(H (a%512) (d%512)).1) (c:=(H (a%512) (d%512)).2)
    · simpa only [H,Prod.fst,Nat.mod_mod] using high_first_mod a d hg
    · simpa only [H,Prod.snd,Nat.mod_mod] using high_second_mod d
    · exact hH
  | equal =>
    have hE:hit (E (a%512) (a%512)).1 (E (a%512) (a%512)).2=true := by
      simpa [x,y] using hc.2.2.2.2 rfl
    apply hit_of_mods (b:=(E (a%512) (a%512)).1) (c:=(E (a%512) (a%512)).2)
    · simpa only [E,Prod.fst,Nat.mod_mod] using equal_first_mod a
    · simp [E]
    · exact hE
  | far d h1 h2 =>
    have hF:hit (F (a%512) (d%512)).1 (F (a%512) (d%512)).2=true := by
      simpa [x,y] using hc.2.1
    apply hit_of_mods (b:=(F (a%512) (d%512)).1) (c:=(F (a%512) (d%512)).2)
    · simpa only [F,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simpa only [F,Prod.snd,Nat.mod_mod] using far_second_mod a d h2
    · exact hF
  | middleEven d h1 h2 hp =>
    have hM:hit (M2 (a%512) (d%512)).1 (M2 (a%512) (d%512)).2=true := by
      have hpSum : (a+d)%2=0 := by omega
      have hpResidue : (a%512+d%512)%2=0 := by omega
      have hpFin : (x.val+y.val)%2=0 := by simpa [x,y] using hpResidue
      simpa [x,y] using (hc.2.2.2.1 hpFin)
    apply hit_of_mods (b:=(M2 (a%512) (d%512)).1) (c:=(M2 (a%512) (d%512)).2)
    · simpa only [M2,Prod.fst,Nat.mod_mod] using far_first_mod a
    · simp [M2]
    · exact hM
  | middleOdd d h1 h2 hp =>
    have hM:hit (M1 (a%512) (d%512)).1 (M1 (a%512) (d%512)).2=true := by
      have hpSum : (a+d)%2=1 := by omega
      have hpResidue : (a%512+d%512)%2=1 := by omega
      have hpFin : (x.val+y.val)%2=1 := by simpa [x,y] using hpResidue
      simpa [x,y] using (hc.2.2.1 hpFin)
    apply hit_of_mods (b:=(M1 (a%512) (d%512)).1) (c:=(M1 (a%512) (d%512)).2)
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
The true seed (1,1) has no relation to a terminal H_d with d%512=373,
and the checked 512^2 graph excludes the pair residue (374,373). -/
theorem terminal373_never (d:Nat) (hd:d%512=373) :
    ∀ n, ¬CounterReach 1 1 n (d+1) d := by
  intro n hr
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · have hg : hit (d+1) d=false := by
      have ha : (d+1)%512=374 := by omega
      simpa [hit,ha,hd] using forbidden_gate_373
    rw [hg] at hl
    contradiction

#print axioms terminal373_never
#print axioms source_closed

/-- The source seed can reach a terminal gate only in 39 residue classes. -/
theorem terminal_mod512_candidates (d n : Nat)
  (hr : CounterReach 1 1 n (d+1) d) :
     d%512 ∈ possibleGates := by
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · have hx : hit ((d%512+1)%512) (d%512) = true := by
      simpa [hit, Nat.add_mod, Nat.mod_mod] using hl
    exact gate_table_complete ⟨d%512, Nat.mod_lt _ (by decide)⟩ hx

#print axioms terminal_mod512_candidates
end BB6.Agent31F321Mod512
