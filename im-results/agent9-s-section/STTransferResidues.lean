import Init.Omega
import Std
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace BB6.Agent9STResidues

/-- Repeated T-stage affine quotient stage from the published highLevelNext. -/
def g (m : Nat) : Nat := 4*(m/3)+7
def g2 (m : Nat) : Nat := g (g m)
def g3 (m : Nat) : Nat := g (g2 m)
def g4 (m : Nat) : Nat := 4*((g3 m)/3)+6

/-- Tag for the target of one complete high-level T macro transition.
0 Tn; 1 S; 2 T; 3 Eb; 4 Ed; 5 immediate high-level halt. -/
def tTag (m : Nat) : Nat :=
  if m%3=0 then 0
  else if m%3=2 then 1
  else if (g m)%3=0 then 2
  else if (g m)%3=2 then 3
  else if (g2 m)%3=0 then 2
  else if (g2 m)%3=2 then 4
  else if (g3 m)%3≠0 then 5
  else if (g4 m)%3=1 then 5 else 2

theorem g_shift243 (k r : Nat) :
    g (243*k+r)=324*k+g r := by unfold g; omega

theorem g_shift324 (k r : Nat) :
    g (324*k+r)=432*k+g r := by unfold g; omega

theorem g_shift432 (k r : Nat) :
    g (432*k+r)=576*k+g r := by unfold g; omega

theorem g2_shift (k r : Nat) :
    g2 (243*k+r)=432*k+g2 r := by
  unfold g2
  rw [g_shift243, g_shift324]

theorem g3_shift (k r : Nat) :
    g3 (243*k+r)=576*k+g3 r := by
  unfold g3
  rw [g2_shift]
  rw [g_shift432]

theorem g4_shift (k r : Nat) :
    g4 (243*k+r)=768*k+g4 r := by
  unfold g4
  rw [g3_shift]
  omega

theorem tTag_shift (k r : Nat) :
    tTag (243*k+r) = tTag r := by
  have h0 : (243*k+r)%3=r%3 := by omega
  have h1 : (g (243*k+r))%3=(g r)%3 := by
    rw [g_shift243]; omega
  have h2 : (g2 (243*k+r))%3=(g2 r)%3 := by
    rw [g2_shift]; omega
  have h3 : (g3 (243*k+r))%3=(g3 r)%3 := by
    rw [g3_shift]; omega
  have h4 : (g4 (243*k+r))%3=(g4 r)%3 := by
    rw [g4_shift]; omega
  unfold tTag
  simp only [h0,h1,h2,h3,h4]

def immediateHalt (m : Nat) : Prop := tTag m=5

theorem immediate_halt_seven_residues (m : Nat) :
    immediateHalt m ↔
    m%243=10 ∨ m%243=37 ∨ m%243=64 ∨ m%243=91 ∨
    m%243=145 ∨ m%243=172 ∨ m%243=226 := by
  have hm : m=243*(m/243)+m%243 := by omega
  have htag : tTag m=tTag (m%243) := by
    calc
      tTag m = tTag (243*(m/243)+m%243) := congrArg tTag hm
      _ = tTag (m%243) := tTag_shift (m/243) (m%243)
  change tTag m=5 ↔ _
  rw [htag]
  have hr : m%243 < 243 := Nat.mod_lt m (by omega)
  have hf : ∀ (r : Fin 243),
      (tTag r.val=5 ↔
       r.val=10 ∨ r.val=37 ∨ r.val=64 ∨ r.val=91 ∨
       r.val=145 ∨ r.val=172 ∨ r.val=226) := by decide
  exact hf ⟨m%243,hr⟩

#print axioms BB6.Agent9STResidues.immediate_halt_seven_residues
end BB6.Agent9STResidues
