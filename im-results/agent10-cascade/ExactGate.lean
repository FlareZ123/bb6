import GateNecessary

namespace CascadeExactGate
open CascadeSource CascadeSweep CascadeNecessaryGate

private def A (k : Nat) : Nat := 4*2^k-2
private def B (h k : Nat) : Nat := 2*h+2*k+9-8*2^k
private def H (n : Nat) : Nat := 4*2^n-n-4

private theorem pow_ge (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem height_eq (n : Nat) : H n+n+4=4*2^n := by
  have h:=pow_ge n
  dsimp [H]
  omega

private theorem height_step (n : Nat) : H n≤H (n+1) := by
  have h:=height_eq n
  have h1:=height_eq (n+1)
  have hpow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ];omega
  omega

private theorem height_mono (a b : Nat) (h : a≤b) : H a≤H b := by
  obtain ⟨d,rfl⟩ : ∃d, b=a+d := ⟨b-a,by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    have hs:=height_step (a+d)
    have hb : a+(d+1)=(a+d)+1 := by omega
    rw [hb]
    omega

private theorem height_base (k : Nat) : H (k+1)+k+5=8*2^k := by
  have hh:=height_eq (k+1)
  have hp : 2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
  omega

private theorem fatal_guard (n k : Nat) (hk : k<n) :
    8*2^k≤H n+k+5 := by
  have hb:=height_base k
  have hm:=height_mono (k+1) n (by omega)
  omega

private theorem cstep_large (a b : Nat) (hb : 2≤b)
    (hd : 2*a≤b-2) :
    Cstep a b=some (2*a+2,b-2-2*a) := by
  obtain ⟨d,rfl⟩ : ∃ d,b=d+2 := ⟨b-2,by omega⟩
  have h : 2*a≤d := by omega
  simp [Cstep,h]

/-- Exact growing cascade transition under its sharp weak guard. -/
theorem cascade_one (h k : Nat) (hh : 8*2^k≤h+k+5) :
    Cstep (A k) (B h k) = some (A (k+1),B h (k+1)) := by
  have hp : 1≤2^k := Nat.one_le_pow _ _ (by decide)
  have ha : A k+2=4*2^k := by dsimp [A];omega
  have hb : B h k+8*2^k=2*h+2*k+9 := by dsimp [B];omega
  have hb2 : 2≤B h k := by omega
  have hd : 2*(A k)≤B h k-2 := by omega
  rw [cstep_large (A k) (B h k) hb2 hd]
  have hpow : 2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
  have ha2 : 2*(A k)+2=A (k+1) := by dsimp [A];omega
  have hb3 : B h k-2-2*(A k)=B h (k+1) := by dsimp [B];omega
  rw [ha2,hb3]

/-- The source episode relation is transitive, retaining exact step order. -/
theorem reach_trans {x y z : Nat×Nat}
    (h : ReachC x y) (k : ReachC y z) : ReachC x z := by
  induction k with
  | refl => exact h
  | push p he ih => exact ReachC.push ih he

/-- Every fatal reset produces a finite successful cascade ending at a state
    whose next source episode is the undefined halting transition. -/
theorem fatal_path (n : Nat) :
    ∃ a, ReachC (H n,0) (a,1) ∧ Cstep a 1=none := by
  have hrun : ∀m, (∀k<m,8*2^k≤H n+k+5) →
      ReachC (H n,0) (A m,B (H n) m) := by
    intro m
    induction m with
    | zero =>
      intro _
      have he : Cstep (H n) 0=some (A 0,B (H n) 0) := by
        simp [Cstep,A,B]
      exact ReachC.push (ReachC.refl _) he
    | succ m ih =>
      intro hh
      have hm := ih (by intro k hk; exact hh k (by omega))
      exact ReachC.push hm (cascade_one (H n) m (hh m (by omega)))
  have hr := hrun n (fatal_guard n)
  have hbn : B (H n) n=1 := by
    have hh:=height_eq n
    dsimp [B]
    omega
  rw [hbn] at hr
  exact ⟨A n,hr,rfl⟩

/-- Complete characterization in the exact source C-episode semantics:
    halting from its true post-initial root iff it visits a fatal reset
    with an index n>=6 in residue classes 4 or 5 mod 6. -/
theorem halt_iff_complementary_reached :
    (∃a, ReachC (2,0) (a,1)) ↔
    (∃n, 6≤n ∧ (n%6=4∨n%6=5) ∧
      ReachC (2,0) (4*2^n-n-4,0)) := by
  constructor
  · rintro ⟨a,ha⟩
    exact halt_requires_surviving_gate a ha
  · rintro ⟨n,hn,hmod,hr⟩
    obtain ⟨a,hpath,hh⟩ := fatal_path n
    exact ⟨a,reach_trans hr hpath⟩

#print axioms cascade_one
#print axioms fatal_path
#print axioms halt_iff_complementary_reached
end CascadeExactGate
