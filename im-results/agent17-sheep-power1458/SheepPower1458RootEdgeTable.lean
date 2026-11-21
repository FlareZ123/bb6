import SheepPower1458LowRows
import SheepPower1458All

/-!
# Root-gate to frozen affine-edge lookup for the five 1458 families

The eight root gate alternatives are filtered by the stored residue progressions.
The output is exactly the existing root-edge set for each family. No new
arithmetic residues are introduced. This source interface is uncompiled pending
the required local Lean 4.36.0-rc2 preflight.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace SheepPower1458

abbrev RootGenericGate (h a t : Nat) : Prop :=
  (h=1 ∧ a=1 ∧ t%2=1) ∨
  (h=1 ∧ a=3 ∧ t%4=2) ∨
  (h=3 ∧ a=1 ∧ t%2=1) ∨
  (h=3 ∧ a=6 ∧ t%7=5) ∨
  (h=5 ∧ a=1 ∧ t%2=1) ∨
  (h=7 ∧ a=1 ∧ t%2=1) ∨
  (h=7 ∧ a=2 ∧ t%9=1) ∨
  (h=7 ∧ a=4 ∧ t%15=8)

theorem progression_mod {T r k q : Nat} (hT : T%q=0) :
    (r+T*k)%q = r%q := by
  rw [Nat.add_mod, Nat.mul_mod, hT]
  simp


theorem residue_mods_t1 (r : Nat) (hr : r ∈ residues_t1) :
    r%2=1 ∧ r%4=1 ∧ r%7=1 ∧ r%9=1 ∧ r%15=1 := by
  simp [residues_t1] at hr
  subst r
  decide

theorem progression_mods_t1 (r k : Nat) (hr : r ∈ residues_t1) :
    (r+period_t1*k)%2=1 ∧ (r+period_t1*k)%4=1 ∧ (r+period_t1*k)%7=1 ∧ (r+period_t1*k)%9=1 ∧ (r+period_t1*k)%15=1 := by
  rcases residue_mods_t1 r hr with ⟨h2r,h4r,h7r,h9r,h15r⟩
  have h2 : period_t1%2=0 := by decide
  have h4 : period_t1%4=0 := by decide
  have h7 : period_t1%7=0 := by decide
  have h9 : period_t1%9=0 := by decide
  have h15 : period_t1%15=0 := by decide
  have m2 : (r+period_t1*k)%2=r%2 := by
    exact progression_mod (T:=period_t1) (r:=r) (k:=k) (q:=2) h2
  have m4 : (r+period_t1*k)%4=r%4 := by
    exact progression_mod (T:=period_t1) (r:=r) (k:=k) (q:=4) h4
  have m7 : (r+period_t1*k)%7=r%7 := by
    exact progression_mod (T:=period_t1) (r:=r) (k:=k) (q:=7) h7
  have m9 : (r+period_t1*k)%9=r%9 := by
    exact progression_mod (T:=period_t1) (r:=r) (k:=k) (q:=9) h9
  have m15 : (r+period_t1*k)%15=r%15 := by
    exact progression_mod (T:=period_t1) (r:=r) (k:=k) (q:=15) h15
  omega

def rootEdgeSpecs_t1 : List (Nat × Nat × Nat) :=
  [⟨1,1,1⟩, ⟨3,1,2⟩, ⟨5,1,3⟩, ⟨7,1,4⟩, ⟨7,2,5⟩]

theorem rootGate_child_t1 (t h a : Nat)
    (ht : ∃ r ∈ residues_t1, ∃ k, t=r+period_t1*k)
    (hg : RootGenericGate h a t) :
    ∃ child, (h,a,child) ∈ rootEdgeSpecs_t1 := by
  rcases ht with ⟨r,hr,k,rfl⟩
  have mods := progression_mods_t1 r k hr
  rcases hg with
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,hmod⟩
  · exact ⟨1, by simp [rootEdgeSpecs_t1]⟩
  · omega
  · exact ⟨2, by simp [rootEdgeSpecs_t1]⟩
  · omega
  · exact ⟨3, by simp [rootEdgeSpecs_t1]⟩
  · exact ⟨4, by simp [rootEdgeSpecs_t1]⟩
  · exact ⟨5, by simp [rootEdgeSpecs_t1]⟩
  · omega


theorem residue_mods_h1a3 (r : Nat) (hr : r ∈ residues_h1a3) :
    r%2=0 ∧ r%4=2 ∧ r%7≠5 ∧ r%9≠1 ∧ r%15≠8 := by
  simp [residues_h1a3] at hr
  omega

theorem progression_mods_h1a3 (r k : Nat) (hr : r ∈ residues_h1a3) :
    (r+period_h1a3*k)%2=0 ∧ (r+period_h1a3*k)%4=2 ∧ (r+period_h1a3*k)%7≠5 ∧ (r+period_h1a3*k)%9≠1 ∧ (r+period_h1a3*k)%15≠8 := by
  rcases residue_mods_h1a3 r hr with ⟨h2r,h4r,h7r,h9r,h15r⟩
  have h2 : period_h1a3%2=0 := by decide
  have h4 : period_h1a3%4=0 := by decide
  have h7 : period_h1a3%7=0 := by decide
  have h9 : period_h1a3%9=0 := by decide
  have h15 : period_h1a3%15=0 := by decide
  have m2 : (r+period_h1a3*k)%2=r%2 := by
    exact progression_mod (T:=period_h1a3) (r:=r) (k:=k) (q:=2) h2
  have m4 : (r+period_h1a3*k)%4=r%4 := by
    exact progression_mod (T:=period_h1a3) (r:=r) (k:=k) (q:=4) h4
  have m7 : (r+period_h1a3*k)%7=r%7 := by
    exact progression_mod (T:=period_h1a3) (r:=r) (k:=k) (q:=7) h7
  have m9 : (r+period_h1a3*k)%9=r%9 := by
    exact progression_mod (T:=period_h1a3) (r:=r) (k:=k) (q:=9) h9
  have m15 : (r+period_h1a3*k)%15=r%15 := by
    exact progression_mod (T:=period_h1a3) (r:=r) (k:=k) (q:=15) h15
  omega

def rootEdgeSpecs_h1a3 : List (Nat × Nat × Nat) :=
  [⟨1,3,1⟩]

theorem rootGate_child_h1a3 (t h a : Nat)
    (ht : ∃ r ∈ residues_h1a3, ∃ k, t=r+period_h1a3*k)
    (hg : RootGenericGate h a t) :
    ∃ child, (h,a,child) ∈ rootEdgeSpecs_h1a3 := by
  rcases ht with ⟨r,hr,k,rfl⟩
  have mods := progression_mods_h1a3 r k hr
  rcases hg with
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,hmod⟩
  · omega
  · exact ⟨1, by simp [rootEdgeSpecs_h1a3]⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega


theorem residue_mods_h3a6 (r : Nat) (hr : r ∈ residues_h3a6) :
    r%2=0 ∧ r%4=0 ∧ r%7=5 ∧ r%9≠1 ∧ r%15≠8 := by
  simp [residues_h3a6] at hr
  omega

theorem progression_mods_h3a6 (r k : Nat) (hr : r ∈ residues_h3a6) :
    (r+period_h3a6*k)%2=0 ∧ (r+period_h3a6*k)%4=0 ∧ (r+period_h3a6*k)%7=5 ∧ (r+period_h3a6*k)%9≠1 ∧ (r+period_h3a6*k)%15≠8 := by
  rcases residue_mods_h3a6 r hr with ⟨h2r,h4r,h7r,h9r,h15r⟩
  have h2 : period_h3a6%2=0 := by decide
  have h4 : period_h3a6%4=0 := by decide
  have h7 : period_h3a6%7=0 := by decide
  have h9 : period_h3a6%9=0 := by decide
  have h15 : period_h3a6%15=0 := by decide
  have m2 : (r+period_h3a6*k)%2=r%2 := by
    exact progression_mod (T:=period_h3a6) (r:=r) (k:=k) (q:=2) h2
  have m4 : (r+period_h3a6*k)%4=r%4 := by
    exact progression_mod (T:=period_h3a6) (r:=r) (k:=k) (q:=4) h4
  have m7 : (r+period_h3a6*k)%7=r%7 := by
    exact progression_mod (T:=period_h3a6) (r:=r) (k:=k) (q:=7) h7
  have m9 : (r+period_h3a6*k)%9=r%9 := by
    exact progression_mod (T:=period_h3a6) (r:=r) (k:=k) (q:=9) h9
  have m15 : (r+period_h3a6*k)%15=r%15 := by
    exact progression_mod (T:=period_h3a6) (r:=r) (k:=k) (q:=15) h15
  omega

def rootEdgeSpecs_h3a6 : List (Nat × Nat × Nat) :=
  [⟨3,6,1⟩]

theorem rootGate_child_h3a6 (t h a : Nat)
    (ht : ∃ r ∈ residues_h3a6, ∃ k, t=r+period_h3a6*k)
    (hg : RootGenericGate h a t) :
    ∃ child, (h,a,child) ∈ rootEdgeSpecs_h3a6 := by
  rcases ht with ⟨r,hr,k,rfl⟩
  have mods := progression_mods_h3a6 r k hr
  rcases hg with
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,hmod⟩
  · omega
  · omega
  · omega
  · exact ⟨1, by simp [rootEdgeSpecs_h3a6]⟩
  · omega
  · omega
  · omega
  · omega


theorem residue_mods_h7a2 (r : Nat) (hr : r ∈ residues_h7a2) :
    r%2=0 ∧ r%4=0 ∧ r%7≠5 ∧ r%9=1 ∧ r%15≠8 := by
  simp [residues_h7a2] at hr
  omega

theorem progression_mods_h7a2 (r k : Nat) (hr : r ∈ residues_h7a2) :
    (r+period_h7a2*k)%2=0 ∧ (r+period_h7a2*k)%4=0 ∧ (r+period_h7a2*k)%7≠5 ∧ (r+period_h7a2*k)%9=1 ∧ (r+period_h7a2*k)%15≠8 := by
  rcases residue_mods_h7a2 r hr with ⟨h2r,h4r,h7r,h9r,h15r⟩
  have h2 : period_h7a2%2=0 := by decide
  have h4 : period_h7a2%4=0 := by decide
  have h7 : period_h7a2%7=0 := by decide
  have h9 : period_h7a2%9=0 := by decide
  have h15 : period_h7a2%15=0 := by decide
  have m2 : (r+period_h7a2*k)%2=r%2 := by
    exact progression_mod (T:=period_h7a2) (r:=r) (k:=k) (q:=2) h2
  have m4 : (r+period_h7a2*k)%4=r%4 := by
    exact progression_mod (T:=period_h7a2) (r:=r) (k:=k) (q:=4) h4
  have m7 : (r+period_h7a2*k)%7=r%7 := by
    exact progression_mod (T:=period_h7a2) (r:=r) (k:=k) (q:=7) h7
  have m9 : (r+period_h7a2*k)%9=r%9 := by
    exact progression_mod (T:=period_h7a2) (r:=r) (k:=k) (q:=9) h9
  have m15 : (r+period_h7a2*k)%15=r%15 := by
    exact progression_mod (T:=period_h7a2) (r:=r) (k:=k) (q:=15) h15
  omega

def rootEdgeSpecs_h7a2 : List (Nat × Nat × Nat) :=
  [⟨7,2,1⟩]

theorem rootGate_child_h7a2 (t h a : Nat)
    (ht : ∃ r ∈ residues_h7a2, ∃ k, t=r+period_h7a2*k)
    (hg : RootGenericGate h a t) :
    ∃ child, (h,a,child) ∈ rootEdgeSpecs_h7a2 := by
  rcases ht with ⟨r,hr,k,rfl⟩
  have mods := progression_mods_h7a2 r k hr
  rcases hg with
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,hmod⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact ⟨1, by simp [rootEdgeSpecs_h7a2]⟩
  · omega


theorem residue_mods_h7a4 (r : Nat) (hr : r ∈ residues_h7a4) :
    r%2=0 ∧ r%4=0 ∧ r%7≠5 ∧ r%9≠1 ∧ r%15=8 := by
  simp [residues_h7a4] at hr
  omega

theorem progression_mods_h7a4 (r k : Nat) (hr : r ∈ residues_h7a4) :
    (r+period_h7a4*k)%2=0 ∧ (r+period_h7a4*k)%4=0 ∧ (r+period_h7a4*k)%7≠5 ∧ (r+period_h7a4*k)%9≠1 ∧ (r+period_h7a4*k)%15=8 := by
  rcases residue_mods_h7a4 r hr with ⟨h2r,h4r,h7r,h9r,h15r⟩
  have h2 : period_h7a4%2=0 := by decide
  have h4 : period_h7a4%4=0 := by decide
  have h7 : period_h7a4%7=0 := by decide
  have h9 : period_h7a4%9=0 := by decide
  have h15 : period_h7a4%15=0 := by decide
  have m2 : (r+period_h7a4*k)%2=r%2 := by
    exact progression_mod (T:=period_h7a4) (r:=r) (k:=k) (q:=2) h2
  have m4 : (r+period_h7a4*k)%4=r%4 := by
    exact progression_mod (T:=period_h7a4) (r:=r) (k:=k) (q:=4) h4
  have m7 : (r+period_h7a4*k)%7=r%7 := by
    exact progression_mod (T:=period_h7a4) (r:=r) (k:=k) (q:=7) h7
  have m9 : (r+period_h7a4*k)%9=r%9 := by
    exact progression_mod (T:=period_h7a4) (r:=r) (k:=k) (q:=9) h9
  have m15 : (r+period_h7a4*k)%15=r%15 := by
    exact progression_mod (T:=period_h7a4) (r:=r) (k:=k) (q:=15) h15
  omega

def rootEdgeSpecs_h7a4 : List (Nat × Nat × Nat) :=
  [⟨7,4,1⟩]

theorem rootGate_child_h7a4 (t h a : Nat)
    (ht : ∃ r ∈ residues_h7a4, ∃ k, t=r+period_h7a4*k)
    (hg : RootGenericGate h a t) :
    ∃ child, (h,a,child) ∈ rootEdgeSpecs_h7a4 := by
  rcases ht with ⟨r,hr,k,rfl⟩
  have mods := progression_mods_h7a4 r k hr
  rcases hg with
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,_⟩ |
    ⟨rfl,rfl,hmod⟩ |
    ⟨rfl,rfl,hmod⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact ⟨1, by simp [rootEdgeSpecs_h7a4]⟩


theorem rootEdgeSpec_mem_edges_t1 {h a child : Nat}
    (hm : (h,a,child) ∈ rootEdgeSpecs_t1) :
    (0,child,h,a) ∈ edges_t1 := by
  simp [rootEdgeSpecs_t1, edges_t1] at hm ⊢
  omega

theorem rootEdgeSpec_mem_edges_h1a3 {h a child : Nat}
    (hm : (h,a,child) ∈ rootEdgeSpecs_h1a3) :
    (0,child,h,a) ∈ edges_h1a3 := by
  simp [rootEdgeSpecs_h1a3, edges_h1a3] at hm ⊢
  omega

theorem rootEdgeSpec_mem_edges_h3a6 {h a child : Nat}
    (hm : (h,a,child) ∈ rootEdgeSpecs_h3a6) :
    (0,child,h,a) ∈ edges_h3a6 := by
  simp [rootEdgeSpecs_h3a6, edges_h3a6] at hm ⊢
  omega

theorem rootEdgeSpec_mem_edges_h7a2 {h a child : Nat}
    (hm : (h,a,child) ∈ rootEdgeSpecs_h7a2) :
    (0,child,h,a) ∈ edges_h7a2 := by
  simp [rootEdgeSpecs_h7a2, edges_h7a2] at hm ⊢
  omega

theorem rootEdgeSpec_mem_edges_h7a4 {h a child : Nat}
    (hm : (h,a,child) ∈ rootEdgeSpecs_h7a4) :
    (0,child,h,a) ∈ edges_h7a4 := by
  simp [rootEdgeSpecs_h7a4, edges_h7a4] at hm ⊢
  omega

end SheepPower1458
