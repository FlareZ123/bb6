import BB429Rank
import BB429Burst
import BB429DyadicStarts
import Lean.Elab.Tactic.Omega

namespace Agent6TwoBurstZero
set_option maxHeartbeats 10000000

def c (q : Nat) : Nat := q+2
def p (q : Nat) : Nat := 2^(c q)
def k (q : Nat) : Nat := 4*p q-11
def n (q : Nat) : Nat := k q+c q+1
def Q (q : Nat) : Nat := 2^(n q)
def demand (q : Nat) : Nat := 12*Q q - 24*p q + 39 - 3*c q
def firstU (q : Nat) : Nat := 3*Q q-3
def firstW (q : Nat) : Nat := 6*Q q+15-12*p q
def secondU (q : Nat) : Nat := 6*p q-3
def secondW (q : Nat) : Nat := 12*Q q+26-24*p q

private theorem pow_linear (j : Nat) : j+1≤2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

private theorem elementary_bounds (q : Nat) :
   c q+1 ≤ p q ∧ 4 ≤ p q ∧ k q+11=4*p q ∧ 5≤k q := by
  have h := pow_linear (c q)
  have hc : 2≤c q := by simp [c]
  have hp : 4≤p q := by
    have h2 : 4≤2^(c q) := by
      obtain ⟨j,hj⟩ : ∃ j, c q=j+2 := ⟨q,by simp [c]⟩
      rw [hj, Nat.pow_add]
      have he : 0<2^j := Nat.pow_pos (by omega)
      omega
    simpa [p] using h2
  change c q+1 ≤ p q at h
  simp only [k]
  omega

private theorem Q_factor (q : Nat) : Q q=2*p q*2^(k q) := by
  have he : n q = (c q+1)+k q := by simp only [n]; omega
  rw [show Q q=2^(n q) by rfl, he, Nat.pow_add, Nat.pow_succ]
  simp only [p]
  ac_rfl

private theorem positive_bounds (q : Nat) :
  4*p q ≤ Q q ∧ c q+1 ≤ p q ∧ 3 ≤ 3*Q q := by
  have ⟨hc,hp,hk,hk5⟩ := elementary_bounds q
  have hfac := Q_factor q
  have hkk : 2≤2^(k q) := by
    have he : k q = (k q-1)+1 := by omega
    rw [he, Nat.pow_succ]
    have hpz : 0<2^(k q-1) := Nat.pow_pos (by omega)
    omega
  have hmul := Nat.mul_le_mul_left (2*p q) hkk
  have hpos : 0<p q := by omega
  have hq : 0<Q q := Nat.pow_pos (by omega)
  constructor
  · omega
  constructor
  · exact hc
  · omega

private theorem arithmetic (q : Nat) :
  24*p q+3*c q ≤ 12*Q q+39 ∧
  12*p q ≤ 6*Q q+15 ∧
  24*p q ≤ 12*Q q+26 ∧
  demand q+3*n q=12*Q q-12*p q+9 ∧
  firstU q+3=3*Q q ∧
  firstW q+12*p q=6*Q q+15 ∧
  secondU q+3=6*p q ∧
  secondW q+24*p q=12*Q q+26 ∧
  2*firstU q+firstW q=demand q+3*n q := by
  have ⟨hb,hc,hpos⟩ := positive_bounds q
  have ⟨hpc,hpp,hk,hk5⟩ := elementary_bounds q
  simp only [demand,firstU,firstW,secondU,secondW,n]
  omega

private theorem first_success (q : Nat) :
  BB429Burst.firstRun (n q) (0,demand q)=some (firstU q,firstW q) := by
  have ⟨hbound,_,_⟩ := positive_bounds q
  have hbase := arithmetic q
  have hcost := hbase.2.2.2.1
  have hk := (elementary_bounds q).2.2.1
  have hn : n q=(n q-1)+1 := by
    simp only [n]
    omega
  have hpow : Q q=2*2^(n q-1) := by
    calc
      Q q = 2^((n q-1)+1) := by rw [show Q q=2^(n q) by rfl, ←hn]
      _ = 2*2^(n q-1) := by rw [Nat.pow_succ]; omega
  have hg : 4*((0+3)*2^(n q-1)) ≤ 2*0+demand q+3*(n q-1)+9 := by
    have hfrom : 6*Q q ≤ demand q+3*(n q-1)+9 := by
      have hlinear : n q=(k q+c q+1) := rfl
      omega
    omega
  obtain ⟨a,b,hr⟩ :=
    (BB429Burst.prefix_exists_iff 0 (demand q) (n q-1)).mpr hg
  have hr' : BB429Burst.firstRun (n q) (0,demand q)=some (a,b) := by
    rw [hn]
    exact hr
  obtain ⟨ha,hb⟩ := BB429Burst.prefix_formula 0 (demand q) (n q) a b hr'
  have hp : 2^(n q)=Q q := rfl
  have heq := arithmetic q
  have heq1 : a=firstU q := by omega
  have heq2 : b=firstW q := by omega
  simpa [heq1,heq2] using hr'

private theorem odd_reset (q : Nat) :
  BB429.next (firstU q,firstW q)=some (secondU q,secondW q) := by
  have ha := arithmetic q
  have ⟨hbound,hc,hpos⟩ := positive_bounds q
  have hP := elementary_bounds q
  have hwlt : firstW q<2*firstU q := by omega
  have hodd : firstW q%2≠0 := by omega
  have hbig : firstW q≠1 := by omega
  have hd : firstU q-firstW q/2=6*p q-10 := by omega
  have hd2 : firstU q-firstW q/2≠1 := by omega
  have hd3 : firstU q-firstW q/2≠2 := by omega
  have hdeven : (firstU q-firstW q/2)%2=0 := by omega
  have houtU : firstU q-firstW q/2+7=secondU q := by omega
  have houtW : 2*firstW q-4=secondW q := by omega
  simp [BB429.next, show ¬ (firstW q≥2*firstU q+3) by omega,
    show firstW q≠2*firstU q+2 by omega,
    show firstW q≠2*firstU q+1 by omega,
    show firstW q≠2*firstU q by omega,
    hodd,hd2,hd3,hdeven,hbig,houtU,houtW]

private theorem second_gateway (q : Nat) :
  ∃ m a b, BB429.run m (secondU q,secondW q)=some (a,b) ∧
    BB429.next (a,b)=none := by
  have ha := arithmetic q
  have hk := (elementary_bounds q).2.2.1
  have hfac := Q_factor q
  have hprod : 4*((secondU q+3)*2^(k q))=12*Q q := by
    have he : secondU q+3=6*p q := ha.2.2.2.2.2.2.1
    rw [he,hfac]
    have hmul4 (x : Nat) : 4*(6*x)=24*x := by
      rw [← Nat.mul_assoc]
    have hmul12 (x : Nat) : 12*(2*x)=24*x := by
      rw [← Nat.mul_assoc]
    calc
      4*((6*p q)*2^(k q)) = 4*(6*(p q*2^(k q))) := by rw [Nat.mul_assoc]
      _ = 24*(p q*2^(k q)) := hmul4 _
      _ = 12*(2*(p q*2^(k q))) := (hmul12 _).symm
      _ = 12*((2*p q)*2^(k q)) := by rw [Nat.mul_assoc]
  have hgate : 2*secondU q+secondW q+3*k q+13 =
    4*((secondU q+3)*2^(k q)) := by
    rw [hprod]
    omega
  obtain ⟨m,a,b,hr,hline⟩ :=
    (BB429Burst.burst_gateway_iff (secondU q) (secondW q)).mpr ⟨k q,hgate⟩
  exact ⟨m,a,b,BB429DyadicStarts.first_prefix_is_source _ _ _ hr,
    (BB429.next_none_iff_halt_line a b).mpr hline⟩

theorem full_source_synthetic_halt (q : Nat) :
  ∃ m a b, BB429.run m (0,demand q)=some (a,b) ∧
    BB429.next (a,b)=none := by
  obtain ⟨j,a,b,hr,hh⟩ := second_gateway q
  have h1 : BB429.run (n q) (0,demand q)=some (firstU q,firstW q) :=
    BB429DyadicStarts.first_prefix_is_source _ _ _ (first_success q)
  have h2 := odd_reset q
  refine ⟨n q+1+j,a,b,?_,hh⟩
  rw [show n q+1+j=(n q+1)+j by omega, BB429.run_add]
  have hm : BB429.run (n q+1) (0,demand q)=some (secondU q,secondW q) := by
    change (BB429.run (n q) (0,demand q)).bind BB429.next = _
    simp [h1,h2]
  simp [hm,hr]

#print axioms full_source_synthetic_halt
end Agent6TwoBurstZero
