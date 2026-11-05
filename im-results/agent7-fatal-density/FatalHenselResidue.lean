import FatalValuationExact
set_option maxHeartbeats 0
namespace CascadeFatalDensity
open CascadeManyShield CascadeFatalValuation

def z (n : Nat) : Nat := 2*fatal n+5
def fatalSector (s j:Nat):Nat:=s+6*j

/-- Each surviving index sector starts with at least one factor of three. -/
theorem sector_base_three (s j:Nat) (hs:s=4 ∨ s=5):
    z (fatalSector s j)%3=0:=by
  rcases hs with rfl|rfl
  · have h:=fatal_shift_keeps_divisibility 1 4 j (by decide) (by decide)
    simpa [z,fatalSector] using h
  · have h:=fatal_shift_keeps_divisibility 1 5 j (by decide) (by decide)
    simpa [z,fatalSector] using h

private theorem sector_algebra (s b j P:Nat):
    s+6*(b+P*j)=s+6*b+2*(P*3)*j:=by
  rw [Nat.mul_add]
  simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,show (2:Nat)*3=6 by decide]
  omega

/-- Periodicity of the fatal inverse numerator modulo 3^k under its
    entire source-index stride, without assuming initial divisibility. -/
theorem shift_periodic (k n j:Nat) (hn:4≤n):
    z (n+2*3^k*j)%(3^k)=z n%(3^k):=by
  obtain ⟨m,hm⟩:=fatal_shift_balance k n j hn
  have hh:=congrArg (fun a:Nat=>a%(3^k)) hm
  simpa [z,Nat.add_mod,Nat.mul_mod,Nat.mul_assoc] using hh

/-- At dyadic stage k the unique successful ternary digit is determined by
    the current source-certified numerator quotient. -/
def liftResidue (s :Nat):Nat→Nat
  | 0=>0
  | k+1 => liftResidue s k + 3^k*((z (fatalSector s (liftResidue s k))/3^(k+1))%3)

/-- The recursive Hensel lift stays in one canonical ternary residue interval,
    and every chosen residue has exactly the requested 3-adic divisibility. -/
theorem lift_residue_good (s k:Nat) (hs:s=4 ∨ s=5):
    liftResidue s k < 3^k ∧
      z (fatalSector s (liftResidue s k)) % 3^(k+1)=0:=by
  induction k with
  | zero=>
    simp only [liftResidue, Nat.pow_zero]
    constructor
    · omega
    · simpa [z,fatalSector] using sector_base_three s 0 hs
  | succ k ih=>
    let b:=liftResidue s k
    let j:=(z (fatalSector s b)/3^(k+1))%3
    have hj:j<3:=Nat.mod_lt _ (by decide)
    have hb:b<3^k:=ih.1
    have hdiv:z (fatalSector s b)%3^(k+1)=0:=ih.2
    have hidx:4≤fatalSector s b:=by
      dsimp [fatalSector]; rcases hs with h|h <;> omega
    have hsucceed:= (fatal_shift_exact (k+1) (fatalSector s b) j hidx (by simpa [z] using hdiv) hj).mpr rfl
    have hshift: fatalSector s (b+3^k*j) = fatalSector s b+2*3^(k+1)*j:=by
      simpa only [fatalSector,Nat.pow_succ] using sector_algebra s b j (3^k)
    have hbound:b+3^k*j<3^(k+1):=by
      have hjcase : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases hjcase with h|h|h
      · rw [h]; simp only [Nat.mul_zero,Nat.add_zero,Nat.pow_succ]; omega
      · rw [h]; simp only [Nat.mul_one,Nat.pow_succ]; omega
      · rw [h]; simp only [Nat.pow_succ]; omega
    have hgood:z (fatalSector s (b+3^k*j))%3^((k+1)+1)=0:=by
      rw [hshift]
      exact hsucceed
    change (b+3^k*j<3^(k+1)) ∧
      z (fatalSector s (b+3^k*j)) %3^((k+1)+1)=0
    exact ⟨hbound,hgood⟩

/-- Each complete 3^k index block in either surviving mod-six
    sector has at most one position with 3^(k+1) dividing its numerator. -/
theorem lift_residue_unique (s k j:Nat) (hs:s=4 ∨ s=5)
    (hj:j<3^k)
    (hdiv:z (fatalSector s j)%3^(k+1)=0):
    j=liftResidue s k:=by
  induction k generalizing j with
  | zero=>
    simp only [Nat.pow_zero] at hj
    have hzero:j=0:=by omega
    simpa [liftResidue] using hzero
  | succ k ih=>
    let P:=3^k
    let a:=j%P
    let t:=j/P
    have hp:0<P:=Nat.pow_pos (by decide)
    have ha:a<P:=Nat.mod_lt _ hp
    have ht:t<3:=by
      have h3:j<3*P:=by
        simpa only [P,Nat.pow_succ,Nat.mul_comm] using hj
      exact (Nat.div_lt_iff_lt_mul hp).mpr h3
    have hsplit:j=a+P*t:=by
      dsimp [a,t]
      exact (Nat.mod_add_div j P).symm
    have hshift:fatalSector s j = fatalSector s a+2*3^(k+1)*t:=by
      rw [hsplit]
      simpa only [fatalSector,P,Nat.pow_succ] using sector_algebra s a t P
    have hsmall:z (fatalSector s j)%3^(k+1)=0:=by
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.dvd_trans (Nat.pow_dvd_pow 3 (by omega : k+1≤(k+1)+1))
        (Nat.dvd_of_mod_eq_zero hdiv)
    have hidx:4≤fatalSector s a:=by
      dsimp [fatalSector]; rcases hs with h|h <;> omega
    have hbase:z (fatalSector s a)%3^(k+1)=0:=by
      have hh:=shift_periodic (k+1) (fatalSector s a) t hidx
      rw [←hshift] at hh
      rw [hsmall] at hh
      exact hh.symm
    have heq:a=liftResidue s k:=ih a ha hbase
    have htd:t=(z (fatalSector s a)/3^(k+1))%3:=by
      apply (fatal_shift_exact (k+1) (fatalSector s a) t hidx
        (by simpa only [z] using hbase) ht).mp
      rw [←hshift]
      exact hdiv
    calc
      j = a+P*t := hsplit
      _ = liftResidue s k + 3^k*((z (fatalSector s (liftResidue s k))/3^(k+1))%3) := by
        rw [heq] at htd
        rw [heq, htd]
      _ = liftResidue s (k+1) := by rfl

/-- Exactly one residue in every complete 3^k-block has valuation at least k+1. -/
theorem lift_residue_unique_and_exists (s k:Nat) (hs:s=4 ∨ s=5):
    ∃j:Nat, j<3^k ∧ z (fatalSector s j)%3^(k+1)=0 ∧
      ∀l:Nat,l<3^k → z (fatalSector s l)%3^(k+1)=0 → l=j :=by
  obtain ⟨hb,hd⟩ := lift_residue_good s k hs
  refine ⟨liftResidue s k,hb,hd,?_⟩
  intro j hj hjdiv
  exact lift_residue_unique s k j hs hj hjdiv

/-- Exact modular characterization at arbitrary index, without truncation. -/
theorem lift_residue_iff (s k j:Nat) (hs:s=4 ∨ s=5):
    z (fatalSector s j)%3^(k+1)=0 ↔ j%(3^k)=liftResidue s k:=by
  let P:=3^k
  let a:=j%P
  let t:=j/P
  have hp:0<P:=Nat.pow_pos (by decide)
  have ha:a<P:=Nat.mod_lt _ hp
  have hsplit:j=a+P*t:=by
    dsimp [a,t]
    exact (Nat.mod_add_div j P).symm
  have hshift:fatalSector s j = fatalSector s a+2*3^(k+1)*t:=by
    rw [hsplit]
    simpa only [fatalSector,P,Nat.pow_succ] using sector_algebra s a t P
  have hidx:4≤fatalSector s a:=by
    dsimp [fatalSector]; rcases hs with h|h <;> omega
  have hper:=shift_periodic (k+1) (fatalSector s a) t hidx
  have heq:z (fatalSector s j)%3^(k+1)=z (fatalSector s a)%3^(k+1):=by
    rw [hshift]
    exact hper
  constructor
  · intro h
    have hsmall:z (fatalSector s a)%3^(k+1)=0:=by
      rw [←heq]
      exact h
    exact lift_residue_unique s k a hs ha hsmall
  · intro h
    have hcanon:a=liftResidue s k := h
    rw [heq,hcanon]
    exact (lift_residue_good s k hs).2

#print axioms lift_residue_iff
#print axioms lift_residue_unique
#print axioms lift_residue_unique_and_exists
#print axioms sector_base_three
#print axioms lift_residue_good
end CascadeFatalDensity
