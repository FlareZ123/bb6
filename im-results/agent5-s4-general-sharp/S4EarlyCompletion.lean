import S4PrefixGate64
import Lean.Elab.Tactic.Omega

/-! General one-digit terminal completion for the original-source S4 triple-drain.
    Holds at arbitrary prefix depths, under an explicit early-stop hypothesis. -/
namespace S4EarlyCompletion
open S4Power S4Octet S4Toggle S4PrefixCausal S4PrefixGate64
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- True iff the H carry drain hits an even branch while at least one
    entry of its designated finite prefix still remains. -/
def earlyH : Nat → List Nat → Bool
  | _, [] => false
  | a, b::L => if a%2=0 then true else earlyH (b+a/2+1) L

def earlyG (c : Nat) : List Nat → Bool
  | [] => false
  | b::L => earlyH (b+c) L

/-- With an early even branch, the exact H map preserves an arbitrary suffix
    verbatim; the finite prefix is transformed by the existing hp. -/
theorem H_early_copy (a : Nat) (xs S : List Nat)
    (he : earlyH a xs = true) :
    H a (xs++S) = some (hp a xs ++ S) := by
  induction xs generalizing a with
  | nil => simp [earlyH] at he
  | cons b L ih =>
      by_cases hh : a%2=0
      · simp [earlyH,hh,H,hp]
      · have he' : earlyH (b+a/2+1) L = true := by
          simpa [earlyH,hh] using he
        have hr := ih (b+a/2+1) he'
        simp [H,hp,hh,hr]

theorem G_early_copy (c : Nat) (xs S : List Nat)
    (he : earlyG c xs = true) :
    G c (xs++S) = some (gp c xs ++ S) := by
  cases xs with
  | nil => simp [earlyG] at he
  | cons b L =>
      simpa [G,gp,earlyG] using H_early_copy (b+c) L S (by simpa [earlyG] using he)

private theorem pow2_covers (q : Nat) : q+1 ≤ 2^(q+1) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have h : 2^(q+2)=2*(2^(q+1)) := by
        rw [show q+2=(q+1)+1 by omega,Nat.pow_succ]
        omega
      rw [h]
      omega

/-- Universal power-gate completion of any compatible finite prefix.
    No bound on the prefix depth, digit values or other tail is assumed. -/
theorem terminal_completion (c k : Nat) (xs : List Nat) (hc : 0<c)
  (hl : xs.length=k) (hm : (W xs+c) % (2^k)=0) :
    ∃ t : Nat, G c (xs++[t])=none := by
  let q := (W xs+c)/(2^k)
  let t := 2^(q+1)-q-1
  have hp : q+1 ≤ 2^(q+1) := pow2_covers q
  have hdiv : W xs+c = (2^k)*q := by
    have hh := Nat.mod_add_div (W xs+c) (2^k)
    rw [hm] at hh
    dsimp [q]
    omega
  have ht : q+(t+1)=2^(q+1) := by
    dsimp [t]
    omega
  refine ⟨t,(G_none_iff_power c _ hc).mpr ⟨k+(q+1), ?_⟩⟩
  calc
    W (xs++[t])+c = (W xs+c)+(2^k)*(t+1) := by
      rw [W_append,hl]
      simp [W]
      omega
    _ = (2^k)*q+(2^k)*(t+1) := by rw [hdiv]
    _ = (2^k)*(q+(t+1)) := by simp [Nat.mul_add]
    _ = (2^k)*2^(q+1) := by rw [ht]
    _ = 2^(k+(q+1)) := (Nat.pow_add 2 k (q+1)).symm

/-- Source-map stage-two synthetic halt whenever the first drain
    finishes before the designated finite prefix is exhausted. -/
theorem second_completion (k : Nat) (xs : List Nat)
  (hl : xs.length=k) (he : earlyG 509 xs = true)
  (hm : (W (gp 509 xs)+290) % (2^k)=0) :
  ∃ t : Nat, P (xs++[t])=none := by
  have hlen : (gp 509 xs).length=k := by rw [gp_length,hl]
  obtain ⟨t,ht⟩ := terminal_completion 290 k (gp 509 xs) (by omega) hlen hm
  have h0 : G 509 (xs++[t]) = some (gp 509 xs++[t]) := G_early_copy 509 xs [t] he
  exact ⟨t,by simp [P,h0,ht]⟩

/-- Source-map stage-three synthetic halt when both predecessor drains
    finish inside their prescribed finite prefixes. -/
theorem third_completion (k : Nat) (xs : List Nat)
  (hl : xs.length=k) (he0 : earlyG 509 xs = true)
  (he1 : earlyG 290 (gp 509 xs) = true)
  (hm : (W (gp 290 (gp 509 xs))+219) % (2^k)=0) :
  ∃ t : Nat, P (xs++[t])=none := by
  have hlen : (gp 290 (gp 509 xs)).length=k := by simp [gp_length,hl]
  obtain ⟨t,ht⟩ := terminal_completion 219 k (gp 290 (gp 509 xs)) (by omega) hlen hm
  have h0 : G 509 (xs++[t]) = some (gp 509 xs++[t]) := G_early_copy 509 xs [t] he0
  have h1 : G 290 (gp 509 xs++[t]) =
    some (gp 290 (gp 509 xs)++[t]) := G_early_copy 290 (gp 509 xs) [t] he1
  exact ⟨t,by simp [P,h0,h1,ht]⟩

#print axioms G_early_copy
#print axioms terminal_completion
#print axioms second_completion
#print axioms third_completion
end S4EarlyCompletion
