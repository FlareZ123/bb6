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
  have hq : q%(2^E)=residue E r := by
    dsimp [residue]
    omega
  let M := 2^E
  have hdiv : q%M+M*(q/M)=q := Nat.mod_add_div q M
  have ha : BB429Kernel.va (affine E r) (q/M)=32*q+29 := by
    dsimp [affine, BB429Kernel.va, M]
    calc
      32*(2^E)*(q/(2^E))+32*(residue E r)+29 =
        32*((2^E)*(q/(2^E))+residue E r)+29 := by
          simp [Nat.mul_add, Nat.mul_assoc]
      _ = 32*q+29 := by omega
  have hb : BB429Kernel.vb (affine E r) (q/M)=64*q+55 := by
    dsimp [affine, BB429Kernel.vb, M]
    calc
      64*(2^E)*(q/(2^E))+64*(residue E r)+55 =
        64*((2^E)*(q/(2^E))+residue E r)+55 := by
          simp [Nat.mul_add, Nat.mul_assoc]
      _ = 64*q+55 := by omega
  obtain ⟨i,hi⟩ := hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va (affine E r) (q/M))
      (BB429Kernel.vb (affine E r) (q/M)) := by
    exact ⟨i, by simpa only [ha,hb] using hi⟩
  exact (BB429Kernel.cert_sound 64 (affine E r) (q/M) hc) hs

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
      · omega
      · have hcert : BB429Kernel.cert 64 (affine E r)=true := by
          simpa [cover,hstop] using hc
        exact certified_prefix_excludes E r k q n hr hk (by omega) heq hcert hroot
  | succ fuel ih =>
      intro E r N k q n hr hk hsmall hn heq hc hroot
      by_cases hstop : N≤r
      · omega
      · by_cases hcert : BB429Kernel.cert 64 (affine E r)=true
        · exact certified_prefix_excludes E r k q n hr hk (by omega) heq hcert hroot
        · have hpair :
            cover fuel (E+1) r N &&
            cover fuel (E+1) (r+2^E) N = true := by
              simpa [cover,hstop,hcert] using hc
          have hleft : cover fuel (E+1) r N = true :=
            (Bool.and_eq_true.mp hpair).1
          have hright : cover fuel (E+1) (r+2^E) N = true :=
            (Bool.and_eq_true.mp hpair).2
          have hpow : 2^(E+1)=2*(2^E) := by
            rw [Nat.pow_succ]
            omega
          have hdich : k%(2^(E+1))=r ∨ k%(2^(E+1))=r+2^E := by
            rw [hpow]
            omega
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
    (by decide) (by simp) hk (by omega)
    (exact_offset q n k hn heq) cover_one_thousand hroot

#print axioms cover_sound
#print axioms no_root_k_lt1000
end BB429Branch29Prefix
