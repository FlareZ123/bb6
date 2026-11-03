import SheepOddInverse
import SheepGeneralVal

namespace ValWord
open SheepOddInverse
open SheepValuationComplete
open GeneralVal

inductive WordRun : List Nat → Nat → Prop where
  | last (a x : Nat) (hval : x%2^(a+1)=2^a) : WordRun [a] x
  | cons (a b : Nat) (bs : List Nat) (x y : Nat)
      (hval : x%2^(a+1)=2^a) (step : Step x y)
      (rest : WordRun (b::bs) y) : WordRun (a::b::bs) x

private theorem source_val (a w : Nat) :
    (2^a*(2*w+1)) % 2^(a+1) = 2^a := by
  rw [Nat.pow_succ, Nat.mul_mod_mul_left]
  have hodd : (2*w+1)%2=1 := by omega
  rw [hodd, Nat.mul_one]

private theorem pow_ge_two (k : Nat) (hk : 1≤k) : 2≤2^k := by
  have hp := Nat.pow_le_pow_right (n:=2) (by decide) hk
  simpa only [show (2:Nat)^1=2 by decide] using hp

/-- Construct the predecessor cylinder that implements a prescribed first
    positive valuation a in front of an already certified suffix word. -/
theorem prepend (a b : Nat) (bs : List Nat) (r k : Nat)
    (hk : 1≤k) (hr : r<2^k)
    (hrest : ∀ n, 1≤n → WordRun (b::bs) (r+2^k*n)) :
    ∃ r' k', 1≤k' ∧ r'<2^k' ∧
      ∀ n, 1≤n → WordRun (a::b::bs) (r'+2^k'*n) := by
  let M := 2^k
  let c := 2^(a+1)+1
  let d := 2^a+a
  let w0 := solve k c d r
  let r' := 2^a*(2*w0+1)
  let k' := a+1+k
  have hc : c%2=1 := by
    dsimp [c]
    rw [Nat.pow_succ]
    omega
  have hsol : (c*w0+d)%M=r%M := solve_correct k c d r hc
  have hw0 : w0<M := solve_lt k c d r
  have hprec : 2^k' = 2^a*2*M := by
    dsimp [k',M]
    rw [show a+1+k=a+(1+k) by omega, Nat.pow_add, Nat.pow_add]
    simp only [show (2:Nat)^1=2 by decide]
    ac_rfl
  have hr' : r'<2^k' := by
    have hp : 0<2^a := Nat.pow_pos (by decide)
    have hsmall : 2*w0+1<2*M := by omega
    have hh := Nat.mul_lt_mul_of_pos_left hsmall hp
    dsimp [r']
    rw [hprec]
    simpa only [Nat.mul_assoc] using hh
  refine ⟨r',k',by dsimp [k']; omega,hr',?_⟩
  intro n hn
  let w := w0+M*n
  let x := r'+2^k'*n
  let y := c*w+d
  have hw : 2≤w := by
    have hM : 2≤M := pow_ge_two k hk
    have hn1 : M≤M*n := by
      have hh:=Nat.mul_le_mul_left M hn
      simpa only [Nat.mul_one] using hh
    dsimp [w]
    omega
  have hx : x=2^a*(2*w+1) := by
    dsimp [x,r',w]
    rw [hprec]
    simp only [Nat.mul_add]
    ac_rfl
  have hstep : Step x y := by
    rw [hx]
    dsimp [y,c,d]
    simpa only [Nat.add_assoc] using generic_formula a w hw
  have hval : x%2^(a+1)=2^a := by
    rw [hx]
    exact source_val a w
  have hy_mod : y%M=r := by
    have heq : y=(c*w0+d)+M*(c*n) := by
      dsimp [y,w]
      rw [Nat.mul_add]
      ac_rfl
    rw [heq, mod_add_multiple, hsol]
    exact Nat.mod_eq_of_lt hr
  have hyge : M≤y := by
    have hcge : 1≤c := by dsimp [c]; omega
    have hm1 : M≤M*n := by
      have hh:=Nat.mul_le_mul_left M hn
      simpa only [Nat.mul_one] using hh
    have hm2 : M*n≤c*(M*n) := by
      have hh:=Nat.mul_le_mul_right (M*n) hcge
      simpa only [Nat.one_mul] using hh
    dsimp [y,w]
    rw [Nat.mul_add]
    omega
  let n' := y/M
  have hn' : 1≤n' := by
    dsimp [n']
    exact (Nat.one_le_div_iff (by dsimp [M]; exact Nat.pow_pos (by decide))).mpr hyge
  have hy : y=r+M*n' := by
    have hmdiv:=Nat.mod_add_div y M
    rw [hy_mod] at hmdiv
    simpa only [n'] using hmdiv.symm
  have htail : WordRun (b::bs) y := by
    rw [hy]
    exact hrest n' hn'
  change WordRun (a::b::bs) x
  exact WordRun.cons a b bs x y hval hstep htail

/-- All finite positive valuation words have a whole arithmetic progression
    of legal coherent generic Sheep section histories. -/
theorem any_positive_word : ∀ (word : List Nat), word ≠ [] →
    (∀ a, a ∈ word → 1≤a) →
    ∃ r k, 1≤k ∧ r<2^k ∧
      ∀ n, 1≤n → WordRun word (r+2^k*n) := by
  intro word
  induction word with
  | nil =>
      intro hn
      contradiction
  | cons a tail ih =>
      intro hn hpos
      cases tail with
      | nil =>
          have hp : 0<2^a := Nat.pow_pos (by decide)
          have hbound : 2^a<2^(a+1) := by
            rw [Nat.pow_succ]
            omega
          refine ⟨2^a, a+1, by omega, hbound, ?_⟩
          intro n hn
          have hx : 2^a+2^(a+1)*n =2^a*(2*n+1) := by
            rw [Nat.pow_succ, Nat.mul_add]
            ac_rfl
          rw [hx]
          exact WordRun.last a (2^a*(2*n+1)) (source_val a n)
      | cons b bs =>
          have htailpos : ∀ t, t∈(b::bs) → 1≤t := by
            intro t ht
            exact hpos t (List.mem_cons_of_mem a ht)
          obtain ⟨r,k,hk,hr,hcyl⟩ := ih (by simp) htailpos
          exact prepend a b bs r k hk hr hcyl

#print axioms prepend
#print axioms any_positive_word
end ValWord
