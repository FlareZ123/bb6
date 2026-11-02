import Lean

/-!
Conditional 3-adic finite-branch synchronisation theorem.
Abstract return oracle next is not claimed to be the original Cryptid machine.
The remaining mathematical task is to prove shift3/grows for its raw F-to-F return.
-/

namespace BB6.CryptidContinuity
universe u
variable {Suffix : Type u}

def shift (d : Nat) (o : Option (Nat × Suffix)) : Option (Nat × Suffix) :=
  o.map (fun p => (p.1 + d, p.2))

@[simp] theorem shift_none (d : Nat) : shift (Suffix := Suffix) d none = none := rfl
@[simp] theorem shift_some (d n : Nat) (s : Suffix) :
    shift d (some (n, s)) = some (n+d,s) := rfl

theorem shift_shift (a b : Nat) (o : Option (Nat × Suffix)) :
    shift a (shift b o) = shift (b+a) o := by
  cases o with
  | none => rfl
  | some p =>
    obtain ⟨n,s⟩ := p
    simp [shift, Nat.add_assoc]

/-- A symbolic F-to-F return step. none represents an unavailable next
    return, possibly because of halt or divergence. -/
def iterate (next : Nat → Suffix → Option (Nat × Suffix)) :
    Nat → Nat → Suffix → Option (Nat × Suffix)
  | 0, n, s => some (n,s)
  | k+1, n, s => (next n s).bind (fun p => iterate next k p.1 p.2)

/-- The single-increment conjecture is sufficient for any multiple of three. -/
theorem shift_multiple
    (next : Nat → Suffix → Option (Nat × Suffix))
    (shift3 : ∀ n s, 5 ≤ n → next (n+3) s = shift 8 (next n s))
    (n q : Nat) (s : Suffix) (hn : 5 ≤ n) :
    next (n+3*q) s = shift (8*q) (next n s) := by
  induction q with
  | zero => simp [shift]
  | succ q ih =>
    have h : 5 ≤ n + 3*q := by omega
    have hs := shift3 (n+3*q) s h
    have hh : n+3*(q+1) = (n+3*q)+3 := by omega
    rw [hh, hs, ih, shift_shift]
    congr 1

/-- An arbitrary finite number of returns has the expected 3-adic scaling. -/
theorem iterate_shift
    (next : Nat → Suffix → Option (Nat × Suffix))
    (shift3 : ∀ n s, 5 ≤ n → next (n+3) s = shift 8 (next n s))
    (grows : ∀ n s m t, 5 ≤ n → next n s = some (m,t) → 5 ≤ m)
    (k : Nat) : ∀ (n : Nat) (s : Suffix) (q : Nat), 5 ≤ n →
    iterate next k (n + 3^k*q) s =
      shift (8^k*q) (iterate next k n s) := by
  induction k with
  | zero =>
    intro n s q hn
    simp [iterate, shift]
  | succ k ih =>
    intro n s q hn
    have hpow : n + 3^(k+1)*q = n + 3*(3^k*q) := by
      simp only [Nat.pow_succ]
      ac_rfl
    rw [hpow]
    have h := shift_multiple next shift3 n (3^k*q) s hn
    simp only [iterate]
    rw [h]
    cases hstep : next n s with
    | none => simp [shift]
    | some p =>
      obtain ⟨m,t⟩ := p
      have hg := grows n s m t hn hstep
      have ih' := ih m t (8*q) hg
      have hadd : 8 * (3^k*q) = 3^k*(8*q) := by ac_rfl
      rw [hadd]
      simp only [shift_some, Option.bind_some]
      rw [ih']
      simp only [shift]
      congr 1
      simp only [Nat.pow_succ]
      ac_rfl

/-- Every prefix of length j ≤ k is paired with the precise offset. -/
theorem prefix_shift
    (next : Nat → Suffix → Option (Nat × Suffix))
    (shift3 : ∀ n s, 5 ≤ n → next (n+3) s = shift 8 (next n s))
    (grows : ∀ n s m t, 5 ≤ n → next n s = some (m,t) → 5 ≤ m)
    (k j n q : Nat) (s : Suffix) (hj : j ≤ k) (hn : 5 ≤ n) :
    iterate next j (n+3^k*q) s =
      shift (8^j*3^(k-j)*q) (iterate next j n s) := by
  have he : j+(k-j)=k := by omega
  have hp : 3^k = 3^j*3^(k-j) := by
    calc
      3^k = 3^(j+(k-j)) := by rw [he]
      _ = _ := Nat.pow_add 3 j (k-j)
  have hh : n + 3^k*q = n + 3^j*(3^(k-j)*q) := by
    rw [hp]
    ac_rfl
  rw [hh]
  simpa only [Nat.mul_assoc] using
    (iterate_shift next shift3 grows j n s (3^(k-j)*q) hn)

/-- Completed prefixes have identical suffixes and branch residues mod 3. -/
theorem prefix_branch_mod_three
    (next : Nat → Suffix → Option (Nat × Suffix))
    (shift3 : ∀ n s, 5 ≤ n → next (n+3) s = shift 8 (next n s))
    (grows : ∀ n s m t, 5 ≤ n → next n s = some (m,t) → 5 ≤ m)
    (k j n q m : Nat) (s t : Suffix)
    (hj : j < k) (hn : 5 ≤ n)
    (hsm : iterate next j n s = some (m,t)) :
    ∃ m', iterate next j (n+3^k*q) s = some (m',t) ∧ m'%3=m%3 := by
  have hjle : j ≤ k := by omega
  have hs := prefix_shift next shift3 grows k j n q s hjle hn
  rw [hsm] at hs
  simp only [shift_some] at hs
  have hx : 0 < k-j := by omega
  obtain ⟨v, hv⟩ : ∃ v, k-j=v+1 := by
    cases hsub : k-j with
    | zero => omega
    | succ v => exact ⟨v,rfl⟩
  have hd : ∃ b, 8^j*3^(k-j)*q = 3*b := by
    refine ⟨8^j*3^v*q, ?_⟩
    rw [hv, Nat.pow_succ]
    ac_rfl
  obtain ⟨b,hb⟩ := hd
  refine ⟨m+8^j*3^(k-j)*q, ?_, ?_⟩
  · exact hs
  · rw [hb]
    simp [Nat.add_mod]

end BB6.CryptidContinuity
#print axioms BB6.CryptidContinuity.shift_multiple
#print axioms BB6.CryptidContinuity.iterate_shift
#print axioms BB6.CryptidContinuity.prefix_shift
#print axioms BB6.CryptidContinuity.prefix_branch_mod_three
