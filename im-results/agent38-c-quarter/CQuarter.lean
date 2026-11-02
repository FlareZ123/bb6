import Std
namespace BB6Agent38
abbrev S := Nat × Nat × Nat
def nextC : S → Option S
  | (a,k,1) => some (a,k+1,0)
  | (_,_,2) => none
  | (a,k,3) => some (a,k+2,1)
  | (0,k,0) => some (1,0,2*k+2)
  | (1,0,0) => some (5,0,1)
  | (1,k+1,0) => some (2,2,2*k+1)
  | (a+2,k,0) => some (a,1,2*k+1)
  | (0,k,d+4) => if k%2=0 then some (4*(k/2)+2,2,d+1) else some (4*(k/2)+5,0,d+4)
  | (a+1,k,d+4) => some (a,k+1,d+3)
def rank : S → Nat | (a,k,c) => a+2*k+c
def potential : S → Nat | (a,_,c) => a+c
def energy (s : S) : Nat := rank s * (rank s + 1) - 2 * potential s

theorem potential_le_rank (s : S) : potential s ≤ rank s := by
  rcases s with ⟨a,k,c⟩
  simp only [potential,rank]
  omega

theorem energy_bound (B : Nat) (s : S) (h : rank s ≤ B) : energy s ≤ B*(B+1) := by
  have hm : rank s * (rank s+1) ≤ B*(B+1) := by
    apply Nat.mul_le_mul <;> omega
  unfold energy
  omega

theorem two_potential_le (s:S):2*potential s≤rank s*(rank s+1):=by
  have hp:=potential_le_rank s
  by_cases hzero : rank s=0
  · simp only [hzero] at hp ⊢
    omega
  · have hr : 1≤rank s:=by omega
    have hm : 2*rank s ≤rank s*(rank s+1) := by
      calc
        2*rank s = rank s*2 := by omega
        _ ≤ rank s*(rank s+1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem energy_jump3 (s t:S) (hr:rank t=rank s+3) :energy s+4≤energy t:=by
  have hp:=potential_le_rank t
  unfold energy
  rw [hr] at hp ⊢
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem energy_jump4 (s t:S) (hr:rank t=rank s+4) :energy s+4≤energy t:=by
  have hp:=potential_le_rank t
  unfold energy
  rw [hr] at hp ⊢
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem energy_jump5 (s t:S) (hr:rank t=rank s+5) :energy s+4≤energy t:=by
  have hp:=potential_le_rank t
  unfold energy
  rw [hr] at hp ⊢
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem energy_jump2 (s t:S) (hr:rank t=rank s+2) (hp:potential t≤potential s) :energy s+4≤energy t:=by
  have hs:=two_potential_le s
  have ht:=two_potential_le t
  have hs0 := Nat.sub_add_cancel hs
  have ht0 := Nat.sub_add_cancel ht
  have hnum : rank s*(rank s+1)+2*potential t+4 ≤
      rank t*(rank t+1)+2*potential s := by
    rw [hr]
    simp only [Nat.add_mul,Nat.mul_add]
    omega
  unfold energy
  omega

theorem energy_jump1 (s t:S) (hr:rank t=rank s+1)
  (hp:2*potential t+2≤2*potential s+2*rank s):energy s+4≤energy t:=by
  have hs:=two_potential_le s
  have ht:=two_potential_le t
  have hs0 := Nat.sub_add_cancel hs
  have ht0 := Nat.sub_add_cancel ht
  have hnum : rank s*(rank s+1)+2*potential t+4 ≤
      rank t*(rank t+1)+2*potential s := by
    rw [hr]
    simp only [Nat.add_mul,Nat.mul_add]
    omega
  unfold energy
  omega

theorem energy_plateau (s t:S) (hr:rank t=rank s) (hp:potential t+2≤potential s):energy s+4≤energy t:=by
  have hs:=two_potential_le s
  have ht:=two_potential_le t
  have hs0 := Nat.sub_add_cancel hs
  have ht0 := Nat.sub_add_cancel ht
  have hnum : rank s*(rank s+1)+2*potential t+4 ≤
      rank t*(rank t+1)+2*potential s := by
    rw [hr]
    omega
  unfold energy
  omega

theorem energy_step (s t : S) (h : nextC s = some t) : energy s + 4 ≤ energy t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      apply energy_jump3
      simp only [rank]
      omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t
        apply energy_jump5
        decide
      · simp only [nextC,Option.some.injEq] at h
        subst t
        apply energy_jump4
        simp only [rank]
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      apply energy_jump1
      · simp only [rank]; omega
      · simp only [rank,potential]; omega
  · simp only [nextC,Option.some.injEq] at h
    subst t
    apply energy_jump1
    · simp only [rank]; omega
    · simp only [rank,potential]; omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t
    apply energy_jump2
    · simp only [rank]; omega
    · simp only [potential]; omega
  · rcases a with _|a
    · by_cases hk : k % 2 = 0
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        apply energy_jump3
        simp only [rank]
        omega
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        apply energy_jump3
        simp only [rank]
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      apply energy_plateau
      · simp only [rank]; omega
      · simp only [potential]; omega

def run : Nat → Option S → Option S
  | 0, o => o
  | n+1, o => run n (o.bind nextC)

theorem run_none (n : Nat) : run n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run] using ih

theorem energy_run (n : Nat) (s t : S) (h : run n (some s) = some t) :
    energy s + 4*n ≤ energy t := by
  induction n generalizing s t with
  | zero =>
      have hs : s = t := by simpa [run] using h
      subst t
      omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have ht : run n (some u) = some t := by simpa [run,hs] using h
          have hstep := energy_step s u hs
          have htail := ih u t ht
          omega

/-- Four-fold improvement in universal Machine C finite-target reachability. -/
theorem steps_to_target (n : Nat) (s t : S) (h : run n (some s) = some t) :
    4*n ≤ rank t*(rank t+1) := by
  have hprogress := energy_run n s t h
  have hcap := energy_bound (rank t) t (Nat.le_refl _)
  omega

theorem hit_target_iff_quarter_bound (s t : S) :
    (∃ n, run n (some s) = some t) ↔
    (∃ n, 4*n ≤ rank t*(rank t+1) ∧ run n (some s) = some t) := by
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,steps_to_target n s t hn,hn⟩
  · rintro ⟨n,_,hn⟩
    exact ⟨n,hn⟩

#print axioms energy_step
#print axioms energy_run
#print axioms hit_target_iff_quarter_bound
end BB6Agent38
