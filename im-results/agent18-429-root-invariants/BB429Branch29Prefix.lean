import BB429InverseKernel
import BB429Reset31
import Lean.Elab.Tactic.Omega

/-!
Adaptive dyadic-prefix inverse cover for the #429 29(mod32)
last-reset burst equation.  Every successful prefix cert excludes an
*infinite* arithmetic progression of burst-index parameters, and the
Boolean trie combines them over a finite initial interval without
enumerating that interval.  This is intermediate, not a decision of BB6.
-/
namespace BB429Branch29Prefix
open BB429Reset31
set_option maxHeartbeats 80000000
set_option maxRecDepth 30000
set_option maxRecDepth 30000

def residue (E r : Nat) : Nat :=
  (2^E - (3*r+4)%(2^E))%(2^E)

def affine (E r : Nat) : BB429Kernel.Affine :=
  ⟨32*(2^E),32*(residue E r)+29,
   64*(2^E),64*(residue E r)+55⟩

/-- A prefix `k % 2^E = r` is excluded by the sound affine inverse
certificate, or its two children are recursively excluded.  Prefixes
with `r>=N` are empty in the finite interval `k<N`. -/
def cover : Nat → Nat → Nat → Nat → Bool
  | 0,E,r,N =>
    if N≤r then true else BB429Kernel.cert 64 (affine E r)
  | fuel+1,E,r,N =>
    if N≤r then true
    else if BB429Kernel.cert 64 (affine E r) = true then true
    else cover fuel (E+1) r N &&
         cover fuel (E+1) (r+2^E) N


private theorem complementary_residues
    (M a b : Nat)
    (hM : 0<M) (ha : a<M) (hb : b<M)
    (hmod : (a+b)%M=0) :
    a=(M-b)%M := by
  by_cases hlo : a+b<M
  · have hs : (a+b)%M=a+b := Nat.mod_eq_of_lt hlo
    have hz : a=0 ∧ b=0 := by omega
    rcases hz with ⟨rfl,rfl⟩
    simp
  · have hge : M≤a+b := by omega
    have hs : (a+b)%M=a+b-M := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt (by omega)
    have hsum : a+b=M := by omega
    have hbpos : 0<b := by omega
    have hsub : M-b<M := by omega
    rw [Nat.mod_eq_of_lt hsub]
    omega

private theorem mod_doubling (k M r : Nat)
    (hm : 0<M) (hr : r<M) (hk : k%M=r) :
    k%(2*M)=r ∨ k%(2*M)=r+M := by
  let z := k%(2*M)
  have hzlim : z<2*M := Nat.mod_lt _ (by omega)
  have hdiv : M ∣ 2*M := ⟨2, by omega⟩
  have hzmod : z%M=r := by
    dsimp [z]
    rw [Nat.mod_mod_of_dvd k hdiv]
    exact hk
  by_cases hsmall : z<M
  · have hzm : z%M=z := Nat.mod_eq_of_lt hsmall
    left
    omega
  · have hge : M≤z := by omega
    have hzm : z%M=z-M := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt (by omega)
    right
    omega

private theorem certified_prefix_excludes
    (E r k q n : Nat)
    (hr : r < 2^E)
    (hk : k%(2^E)=r)
    (hn : E≤n-5)
    (heq : q+3*k+4=3*2^(n-5))
    (hc : BB429Kernel.cert 64 (affine E r)=true)
    (hroot : Reach (32*q+29) (64*q+55)) : False := by
  have hsplit : n-5 = E+(n-5-E) := by omega
  have hsum : (q+3*k+4)%(2^E)=0 := by
    rw [heq, hsplit, Nat.pow_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hkr : r%(2^E)=r := Nat.mod_eq_of_lt hr
  have hk3 : (3*k+4)%(2^E)=(3*r+4)%(2^E) := by
    simp [Nat.add_mod, Nat.mul_mod, hk, hkr]
  have hmodrew :
      (q+3*k+4)%(2^E) =
      (q%(2^E)+(3*r+4)%(2^E))%(2^E) := by
    calc
      (q+3*k+4)%(2^E) = (q+(3*k+4))%(2^E) := by
        congr 1
      _ = (q%(2^E)+(3*k+4)%(2^E))%(2^E) := by
        rw [Nat.add_mod]
      _ = (q%(2^E)+(3*r+4)%(2^E))%(2^E) := by
        rw [hk3]
  have hz : (q%(2^E)+(3*r+4)%(2^E))%(2^E)=0 := by
    rw [←hmodrew]
    exact hsum
  have hq : q%(2^E)=residue E r := by
    simpa [residue] using
      (complementary_residues (2^E)
        (q%(2^E)) ((3*r+4)%(2^E))
        (by omega)
        (Nat.mod_lt q (by omega))
        (Nat.mod_lt (3*r+4) (by omega)) hz)
  have hdiv : q%(2^E)+(2^E)*(q/(2^E))=q :=
    Nat.mod_add_div q (2^E)
  have ha : BB429Kernel.va (affine E r) (q/(2^E))=32*q+29 := by
    dsimp [affine, BB429Kernel.va]
    calc
      32*(2^E)*(q/(2^E))+32*(residue E r)+29 =
        32*((2^E)*(q/(2^E))+residue E r)+29 := by
          simp [Nat.mul_add, Nat.mul_assoc]
      _ = 32*q+29 := by omega
  have hb : BB429Kernel.vb (affine E r) (q/(2^E))=64*q+55 := by
    dsimp [affine, BB429Kernel.vb]
    calc
      64*(2^E)*(q/(2^E))+64*(residue E r)+55 =
        64*((2^E)*(q/(2^E))+residue E r)+55 := by
          simp [Nat.mul_add, Nat.mul_assoc]
      _ = 64*q+55 := by omega
  obtain ⟨i,hi⟩ := hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va (affine E r) (q/(2^E)))
      (BB429Kernel.vb (affine E r) (q/(2^E))) := by
    exact ⟨i, by simpa only [ha,hb] using hi⟩
  exact (BB429Kernel.cert_sound 64 (affine E r) (q/(2^E)) hc) hs

/-- A successful adaptive prefix Boolean tree excludes every true
blank-root terminal reset with a small enough burst index. -/
theorem cover_sound :
    ∀ fuel E r N k q n : Nat,
      r < 2^E →
      k%(2^E)=r →
      k<N →
      E+fuel≤n-5 →
      q+3*k+4=3*2^(n-5) →
      cover fuel E r N = true →
      Reach (32*q+29) (64*q+55) →
      False := by
  intro fuel
  induction fuel with
  | zero =>
      intro E r N k q n hr hk hsmall hn heq hc hroot
      by_cases hstop : N≤r
      · have hrle : r≤k := by simpa only [hk] using Nat.mod_le k (2^E)
        omega
      · have hcert : BB429Kernel.cert 64 (affine E r)=true := by
          simpa [cover,hstop] using hc
        exact certified_prefix_excludes E r k q n hr hk (by omega) heq hcert hroot
  | succ fuel ih =>
      intro E r N k q n hr hk hsmall hn heq hc hroot
      by_cases hstop : N≤r
      · have hrle : r≤k := by simpa only [hk] using Nat.mod_le k (2^E)
        omega
      · by_cases hcert : BB429Kernel.cert 64 (affine E r)=true
        · exact certified_prefix_excludes E r k q n hr hk (by omega) heq hcert hroot
        · have hpair :
            cover fuel (E+1) r N &&
            cover fuel (E+1) (r+2^E) N = true := by
              simpa [cover,hstop,hcert] using hc
          have hleft : cover fuel (E+1) r N = true := by
            cases hl : cover fuel (E+1) r N <;> simp [hl] at hpair ⊢
          have hright : cover fuel (E+1) (r+2^E) N = true := by
            cases hl : cover fuel (E+1) (r+2^E) N <;> simp [hl] at hpair ⊢
          have hpow : 2^(E+1)=2*(2^E) := by
            rw [Nat.pow_succ]
            omega
          have hdich : k%(2^(E+1))=r ∨ k%(2^(E+1))=r+2^E := by
            rw [hpow]
            exact mod_doubling k (2^E) r (by omega) hr hk
          rcases hdich with h1 | h2
          · exact ih (E+1) r N k q n
              (by rw [hpow];omega) h1 hsmall (by omega)
              heq hleft hroot
          · exact ih (E+1) (r+2^E) N k q n
              (by rw [hpow];omega) h2 hsmall (by omega)
              heq hright hroot

/-- A source-halting equation on this feeder gives a precise high
power minus linear relation; no heuristic orbit extrapolation. -/
private theorem exact_offset (q n k : Nat)
    (hn : n=127+128*k)
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    q+3*k+4=3*2^(n-5) := by
  have hpow : 2^(n+2)=128*2^(n-5) := by
    have hp : n+2=7+(n-5) := by omega
    rw [hp, Nat.pow_add]
  rw [hpow] at heq
  omega

/-- A small instance exercising the adaptive Boolean certificate. -/
theorem cover_one_thousand :
    cover 23 0 0 1000 = true := by decide

theorem no_root_k_lt1000 (q n k : Nat)
    (hk : k<1000)
    (hn : n=127+128*k)
    (heq : 128*q+3*n+131=3*2^(n+2))
    (hroot : Reach (32*q+29) (64*q+55)) : False := by
  exact cover_sound 23 0 0 1000 k q n
    (by decide) (by omega) hk (by omega)
    (exact_offset q n k hn heq) cover_one_thousand hroot


/-- The adaptive inverse trie covers one million actual burst indices
with only 2227 disjoint certified dyadic cylinders and 2764 empty
prefixes, not one million individual Lean proof obligations. -/
theorem cover_one_million :
    cover 46 0 0 1000000 = true := by decide

theorem no_root_k_lt_million (q n k : Nat)
    (hk : k<1000000)
    (hn : n=127+128*k)
    (heq : 128*q+3*n+131=3*2^(n+2))
    (hroot : Reach (32*q+29) (64*q+55)) : False := by
  exact cover_sound 46 0 0 1000000 k q n
    (by decide) (by omega) hk (by omega)
    (exact_offset q n k hn heq) cover_one_million hroot

/-- An unbounded blank-root theorem, conditional on the exact
29(mod32) final-reset branch7 terminal-burst equation. -/
theorem rooted_branch29_final_burst_ge128000127
    (q n : Nat)
    (hn : 18≤n)
    (hroot : Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    128000127≤n := by
  by_cases hlarge : 128000127≤n
  · exact hlarge
  · have hpow : 2^(n+2)=128*2^(n-5) := by
      have hp : n+2=7+(n-5) := by omega
      rw [hp, Nat.pow_add]
    have hmod : (128*q+3*n+131)%128=0 := by
      rw [heq,hpow]
      omega
    let k := n/128
    have hnr : n%128=127 := by omega
    have hnform : n=127+128*k := by dsimp [k]; omega
    have hk : k<1000000 := by omega
    exact False.elim (no_root_k_lt_million q n k hk hnform heq hroot)

#print axioms cover_one_million
#print axioms rooted_branch29_final_burst_ge128000127

#print axioms cover_sound
#print axioms no_root_k_lt1000
end BB429Branch29Prefix
