import ReverseUnitMap

/-! Exact guarded first-return reformulation of the P1 scalar critical gate. -/
namespace BB6.Agent9FirstReturn
open BB6P1Unit

/-- Forward critical inverse blocks in the shifted right coordinate. -/
inductive Gap (Q : Nat) : Nat → Nat → Prop
  | root : Gap Q 0 1
  | edge (m p k d : Nat) (prev : Gap Q m p) (hk : 0 < k)
      (hp : p+8+m ≤ Q) (hd : 2 ≤ d) (hsize : d+4+m+k ≤ Q)
      (he : p+(Q-m)=2^k*d) : Gap Q (m+k) d

def Safe (q d k : Nat) : Prop :=
  ∀ j < k, bit (q+j) (run q d j)=1 → run q d (j+1)+8 ≤ q+j+1

def FirstReturn (q k : Nat) : Prop :=
  0 < k ∧ run q 1 k = 1 ∧ ∀ j, 0 < j → j < k → 2 ≤ run q 1 j

/-- Borwein--Loring indexing, with initial parameter s. -/
def bl (s a : Nat) : Nat → Nat
  | 0 => a
  | k+1 => 2*(bl s a k % (s+k))

theorem bl_conjugacy (q d k : Nat) : bl (q+1) (2*d) k = 2*run q d k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bl, run, unit, ih]; congr 2 <;> omega

theorem gap_bounds {Q m d : Nat} (h : Gap Q m d) :
    m≤Q ∧ (0<m → 2≤d ∧ d+4+m≤Q) := by
  cases h with
  | root => omega
  | edge m p k d h hk hp hd hs he => omega

theorem path_safe {q d m e : Nat} (h : Path q d m e) (hq : 0<q) : Safe q d m := by
  induction h with
  | nil => intro j hj; omega
  | cons q d k t e ha ht ih =>
    intro j hj hb
    by_cases hlt : j+1<k
    · have hr := run_before_edge q d k j hq ha (by omega)
      have hn := no_early_cross q d k (j+1) hq ha hlt
      rw [Nat.pow_succ] at hn
      have hmul : 2^j*2*d=2*(2^j*d) := by ac_rfl
      rw [hmul] at hn
      rw [hr] at hb
      simp [bit, show ¬ q+j+1 ≤ 2*(2^j*d) by omega] at hb
    · by_cases heq : j+1=k
      · rw [heq, edge_run q d k hq ha]
        have hh := ha.2.2
        have hl := ha.2.1
        omega
      · let r := j-k
        have hkr : k+r=j := by dsimp [r]; omega
        have hkr1 : k+(r+1)=j+1 := by omega
        have hrun := edge_run q d k hq ha
        have hb' : bit (q+k+r) (run (q+k) (2^k*d-(q+k)) r)=1 := by
          rw [←hrun, ←run_add, hkr, Nat.add_assoc, hkr]
          exact hb
        have hm := ih (by omega) r (by omega) hb'
        rw [←hrun, ←run_add, hkr1] at hm
        omega

theorem gap_reverse {Q m d : Nat} (h : Gap Q m d) :
    Path (Q-m) d m 1 ∧ (∀ j<m, 2≤run (Q-m) d j) := by
  induction h with
  | root => exact ⟨by simpa using Path.nil Q 1, by omega⟩
  | edge m p k d h hk hp hd hs he ih =>
    let q := Q-(m+k)
    have hq : 0<q := by dsimp [q]; omega
    have hqm : q+k=Q-m := by dsimp [q]; omega
    have had : admissible q d k := by unfold admissible; omega
    have hval : 2^k*d-(q+k)=p := by omega
    have htail : Path (q+k) (2^k*d-(q+k)) m 1 := by rw [hval,hqm]; exact ih.1
    refine ⟨?_,?_⟩
    · have hpath := Path.cons q d k m 1 had htail
      simpa [q,Nat.add_comm m k] using hpath
    · intro j hj
      change 2≤run q d j
      by_cases hlt : j<k
      · rw [run_before_edge q d k j hq had hlt]
        have hh : 1≤2^j := Nat.one_le_pow _ _ (by decide)
        have hm := Nat.mul_le_mul_right d hh
        omega
      · let r := j-k
        have hr : k+r=j := by dsimp [r]; omega
        rw [←hr,run_add,edge_run q d k hq had,hval,hqm]
        exact ih.2 r (by omega)

theorem gap_of_path {Q q d m e : Nat} (h : Path q d m e) (hend : e=1) (hclock : q+m=Q)
    (hstart : 0<m → d+4≤q) (hpositive : ∀ j<m, 2≤run q d j) : Gap Q m d := by
  induction h generalizing Q with
  | nil q d =>
    subst d
    exact Gap.root
  | cons q d k t e ha ht ih =>
    let p := 2^k*d-(q+k)
    have hk := ha.1
    have hlo := ha.2.1
    have hhi := ha.2.2
    have he : p+(q+k)=2^k*d := by dsimp [p]; omega
    have hp : p+8≤q+k := by dsimp [p]; omega
    have hd : 2≤d := by simpa [run] using hpositive 0 (by omega)
    have hq : 0<q := by have := hstart (by omega); omega
    have htailpos : ∀ j<t, 2≤run (q+k) p j := by
      intro j hj
      have hh := hpositive (k+j) (by omega)
      rw [run_add,edge_run q d k hq ha] at hh
      exact hh
    have hgap : Gap Q t p := ih hend (by omega) (by omega) htailpos
    have hstep : Gap Q (t+k) d := Gap.edge t p k d hgap hk (by omega) hd
      (by have := hstart (by omega); omega) (by omega)
    simpa [Nat.add_comm t k] using hstep

theorem path_of_safe_one (q d k : Nat) (hd : d<q) (hk : 0<k)
    (hone : run q d k=1) (hs : Safe q d k) : Path q d k 1 := by
  obtain ⟨l,hl,hp,hz⟩ := guarded_prefix q d k hd hs
  have heq : l=k := by
    by_cases heq : l=k
    · exact heq
    ·
      have hh := hz (k-1) (by omega) (by omega)
      have he := unit_equation (q+(k-1)) (run q d (k-1)) (run_lt q d (k-1) hd)
      rw [hh,Nat.mul_zero,Nat.add_zero] at he
      have hu : unit (q+(k-1)) (run q d (k-1))=run q d k := by
        have hk' : k-1+1=k := by omega
        calc
          _ = run q d ((k-1)+1) := rfl
          _ = run q d k := congrArg (run q d) hk'
      rw [hu,hone] at he
      omega
  subst l
  simpa [hone] using hp

theorem seed_first (q : Nat) (hq : 5≤q) : run q 1 1=2 := by
  simp [run,unit,Nat.mod_eq_of_lt (by omega : 2<q+1)]

theorem seed_shift (q j : Nat) (hq : 5≤q) :
    run q 1 (j+1)=run (q+1) 2 j := by
  rw [Nat.add_comm j 1,run_add,seed_first q hq]

theorem right_five_iff (Q : Nat) : (∃ m, Gap Q m 2) ↔
    ∃ q k, 5≤q ∧ q+k=Q ∧ FirstReturn q k ∧ Safe q 1 k := by
  constructor
  · rintro ⟨m,h⟩
    have hm : 0<m := by cases h <;> omega
    have hb := (gap_bounds h).2 hm
    let q := Q-m-1
    have hq : 5≤q := by dsimp [q]; omega
    have hclock : q+(m+1)=Q := by dsimp [q]; omega
    have hsub : q+1=Q-m := by omega
    obtain ⟨hp,hpos⟩ := gap_reverse h
    have hend := path_run hp (by omega)
    have hsafe := path_safe hp (by omega)
    refine ⟨q,m+1,hq,hclock,⟨by omega,?_,?_⟩,?_⟩
    · rw [seed_shift q m hq,hsub,hend]
    · intro j hj hjlt
      have hj' : j-1+1=j := by omega
      have hrun : run q 1 j=run (Q-m) 2 (j-1) := by
        calc
          _ = run q 1 ((j-1)+1) := congrArg (run q 1) hj'.symm
          _ = _ := by rw [seed_shift q (j-1) hq,hsub]
      rw [hrun]
      exact hpos (j-1) (by omega)
    · intro j hj hb'
      by_cases hj0 : j=0
      · subst j; simp [run,bit,show ¬ q+1≤2 by omega] at hb'
      · have hj' : j-1+1=j := by omega
        have hrun : run q 1 j=run (Q-m) 2 (j-1) := by
          calc
            _ = run q 1 ((j-1)+1) := congrArg (run q 1) hj'.symm
            _ = _ := by rw [seed_shift q (j-1) hq,hsub]
        have hbit : bit (Q-m+(j-1)) (run (Q-m) 2 (j-1))=1 := by
          rw [←hrun,show Q-m+(j-1)=q+j by omega]
          exact hb'
        have hh := hsafe (j-1) (by omega) hbit
        rw [seed_shift q j hq,hsub]
        rw [hj'] at hh
        omega
  · rintro ⟨q,k,hq,hclock,hret,hsafe⟩
    have hk : 0<k := hret.1
    let m := k-1
    have hm' : m+1=k := by dsimp [m]; omega
    have hm : 0<m := by
      by_cases hzero : 0<m
      · exact hzero
      · have hkk : k=1 := by omega
        have hh := hret.2.1
        rw [hkk,seed_first q hq] at hh
        omega
    have hfinal : run (q+1) 2 m=1 := by
      rw [←seed_shift q m hq,hm']
      exact hret.2.1
    have hs : Safe (q+1) 2 m := by
      intro j hj hb
      have hh := hsafe (j+1) (by omega) (by
        rw [seed_shift q j hq,show q+(j+1)=q+1+j by omega]
        exact hb)
      rw [seed_shift q (j+1) hq] at hh
      omega
    have hp := path_of_safe_one (q+1) 2 m (by omega) hm hfinal hs
    refine ⟨m,gap_of_path hp rfl (by omega) (by omega) ?_⟩
    intro j hj
    have hh := hret.2.2 (j+1) (by omega) (by omega)
    rwa [seed_shift q j hq] at hh

#print axioms bl_conjugacy
#print axioms path_safe
#print axioms gap_reverse
#print axioms gap_of_path
#print axioms path_of_safe_one
#print axioms right_five_iff
end BB6.Agent9FirstReturn
