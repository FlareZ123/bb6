import ResetAncestry
import RootTerminal

namespace CascadeFatalExclusion
open CascadeSource CascadeSweep CascadeAncestry

private def P (n : Nat) : Nat := 2^(n-1)
private def K (n : Nat) : Nat := 2*n+3
private def T (n i : Nat) : Nat := 8*P n+n-1-K n*2^i
private def X (n : Nat) : Nat := 2*P n+n

private theorem exp_ge (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

private theorem p_pos (n : Nat) : 1≤P n := by
  exact Nat.one_le_pow _ _ (by omega)

private theorem full_relation (n i : Nat)
    (h : K n*2^i ≤ 8*P n+n-1) :
    T n i + K n*2^i = 8*P n+n-1 := by
  dsimp [T]
  exact Nat.sub_add_cancel h

/-- All entries up to the last stay index are in the unique dyadic band. -/
theorem in_band (n j i : Nat) (hn : 6≤n) (hi : i≤j)
    (hstay : K n*2^j ≤ X n) :
    (6*P n-1≤T n i ∧ T n i≤8*P n-3) ∧
    T n i+K n*2^i=8*P n+n-1 := by
  have hp := p_pos n
  have hpwi : 1≤2^i := Nat.one_le_pow i 2 (by omega)
  have hpi : 2^i≤2^j := Nat.pow_le_pow_right (by omega) hi
  have hprod := Nat.mul_le_mul_left (K n) hpi
  have hscale : K n*2^i≤2*P n+n := by
    dsimp [X] at hstay
    omega
  have hklow : K n≤K n*2^i := by
    have := Nat.mul_le_mul_left (K n) hpwi
    omega
  have hmax : K n*2^i≤8*P n+n-1 := by omega
  have hrel := full_relation n i hmax
  dsimp [K] at hklow hrel hscale
  constructor
  · constructor
    · omega
    · omega
  · exact hrel

/-- The stopping-index bound also guarantees no subtraction truncation at its
    next index, and hence at every preceding index. -/
private theorem next_relation (n j i : Nat) (hn : 6≤n) (hi : i≤j)
    (hstay : K n*2^j ≤ X n) :
    T n (i+1)+K n*2^(i+1)=8*P n+n-1 := by
  have hp := p_pos n
  have hsmall : n+1≤2^n := exp_ge n
  have hn1 : n-1+1=n := by omega
  have hpow : 2^n=2*P n := by
    dsimp [P]
    have hrewrite : 2^n=2^((n-1)+1) := by rw [hn1]
    rw [Nat.pow_succ] at hrewrite
    omega
  have hbound : n+1≤4*P n := by omega
  have hpi : 2^(i+1)≤2^(j+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul := Nat.mul_le_mul_left (K n) hpi
  have hnext : K n*2^(j+1)=2*(K n*2^j) := by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hstay' : K n*2^j≤2*P n+n := by simpa [X] using hstay
  have hupper : K n*2^(i+1) ≤ 8*P n+n-1 := by omega
  exact full_relation n (i+1) hupper

private theorem t_bifurcation (n j i : Nat) (hn : 6≤n) (hi : i≤j)
    (hstay : K n*2^j≤X n) :
    2*T n i = 8*P n+(n-1)+T n (i+1) := by
  have hrel := (in_band n j i hn hi hstay).2
  have hnext := next_relation n j i hn hi hstay
  have htwice : K n*2^(i+1)=2*(K n*2^i) := by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- One exact backward reset on a blank-rooted trajectory, forcing its
    dyadic scale and uniquely determining the prior reset height. -/
theorem one_backward (n j i : Nat) (hn : 6≤n)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3)
    (hi : i≤j) (hstay : K n*2^j≤X n)
    (hr : ReachC (2,0) (T n i,0)) :
    ReachC (2,0) (T n (i+1),0) := by
  obtain ⟨hband,hrel⟩ := in_band n j i hn hi hstay
  have hodd : T n i%3≠2 := by
    have hz := ReverseResidue.mod3_ancestor n i (by omega) hc
    have hh : CascadeOdd.ancestor (P n) n i = T n i := by
      rfl
    rw [←hh]
    exact hz hrel
  obtain ⟨h,m,hhr,hmlo,hmhi,heq⟩ := reachable_even_reset_parent (T n i) hr hodd
  have hscale := even_band_unique (T n i) m (n-1)
    ⟨hmlo,hmhi⟩ hband
  subst m
  have hp : P n=2^(n-1) := rfl
  have heq' : 2*T n i=8*P n+h+(n-1) := by simpa [P] using heq
  have hidentify := t_bifurcation n j i hn hi hstay
  have hval : h=T n (i+1) := by omega
  rw [hval] at hhr
  exact hhr

/-- Reachability propagates backwards through every in-band predecessor,
    for a fixed valid dyadic stopping index. -/
theorem all_backwards (n j k : Nat) (hn : 6≤n)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3)
    (hstay : K n*2^j≤X n) (hk : k≤j+1)
    (hr : ReachC (2,0) (T n 0,0)) :
    ReachC (2,0) (T n k,0) := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    have hk' : k≤j := by omega
    exact one_backward n j k hn hc hk' hstay (ih (by omega))

/-- The stopping dyadic cell is certified even at the four small indices. -/
theorem exit_data (n : Nat) (hn : 6≤n) :
    ∃ j, K n*2^j≤X n ∧ X n<K n*2^(j+1) ∧
      4*P n-3<T n (j+1) ∧ T n (j+1)<6*P n-1 := by
  by_cases hlarge : 10≤n
  · obtain ⟨j,ha,hb⟩ := TerminalExit.exact_exit_exists n hlarge
    obtain ⟨hc,hd⟩ := TerminalExit.terminal_exit_band n j hlarge ha hb
    exact ⟨j,ha,hb,hc,hd⟩
  have hsmall : n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
  rcases hsmall with hh|hh|hh|hh
  · subst n; exact ⟨2,by decide,by decide,by decide,by decide⟩
  · subst n; exact ⟨2,by decide,by decide,by decide,by decide⟩
  · subst n; exact ⟨3,by decide,by decide,by decide,by decide⟩
  · subst n; exact ⟨4,by decide,by decide,by decide,by decide⟩

private theorem pow_swap (n : Nat) (hn : 1≤n) : 2^n=2*P n := by
  have hh : n-1+1=n := by omega
  have hw : 2^n=2^((n-1)+1) := by rw [hh]
  rw [Nat.pow_succ] at hw
  dsimp [P]
  omega

private theorem t0_fatal (n : Nat) (hn : 6≤n) :
    T n 0=4*2^n-n-4 := by
  have hp := p_pos n
  have hzero : 2^0=1 := by decide
  have hk : K n=2*n+3 := rfl
  have hpw := pow_swap n (by omega)
  have hexp := exp_ge n
  have hbig : n+4≤8*P n := by omega
  have hcalc : T n 0+n+4=8*P n := by
    have hdef : T n 0=8*P n+n-1-K n*2^0 := rfl
    rw [hzero,hk] at hdef
    omega
  have hlim : n+4≤4*2^n := by
    have hs:= exp_ge n
    omega
  have htarget : (4*2^n-n-4)+(n+4)=4*2^n := by omega
  omega

/-- Universal exact C-step source-model blank-root exclusion of the four
    proposed fatal-height residue classes, with all inverse ancestors checked. -/
theorem no_fatal_root (n : Nat) (hn : 6≤n)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3) :
    ¬ ReachC (2,0) (4*2^n-n-4,0) := by
  obtain ⟨j,hstay,hexit,hlow,hhigh⟩ := exit_data n hn
  intro hreach
  have hroot : ReachC (2,0) (T n 0,0) := by
    rw [t0_fatal n hn]
    exact hreach
  have hterm := all_backwards n j (j+1) hn hc hstay (by omega) hroot
  have hrel := next_relation n j j hn (by omega) hstay
  have hodd : T n (j+1)%3≠2 := by
    have hrev := ReverseResidue.mod3_ancestor n (j+1) (by omega) hc
    change T n (j+1)%3≠2
    have hh : CascadeOdd.ancestor (P n) n (j+1)=T n (j+1) := rfl
    rw [←hh]
    exact hrev hrel
  have hno : ∀m, ¬(6*2^m-1≤T n (j+1) ∧ T n (j+1)≤8*2^m-3) := by
    intro m
    exact TerminalExit.no_even_band n m (T n (j+1)) (by omega) hlow hhigh
  exact (root_excludes_nonimage (T n (j+1)) hodd hno) hterm

#print axioms exit_data
#print axioms no_fatal_root

#print axioms one_backward
#print axioms all_backwards
end CascadeFatalExclusion
