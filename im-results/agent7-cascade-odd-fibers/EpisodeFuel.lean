import SourceMacro

namespace CascadeSource

/-- Iteration of the original source-indexed accelerated C/P transition. -/
def iter : Nat → S → Option S
  | 0, s => some s
  | k+1, s => (next s).bind (iter k)

/-- Exact P-sweep duration is k+1 accelerated source steps. -/
theorem P_sweep_fuel (k n p : Nat) (hp : p≤2*k+2) :
    iter (k+1) (.P k n p) =
      some (.C (weight k n p/4) (weight k n p%4)) := by
  induction k generalizing n p with
  | zero =>
    have hp3 : p=0∨p=1∨p=2 := by omega
    rcases hp3 with rfl|rfl|rfl
    · have hh : weight 0 n 0 /4=n+1 ∧ weight 0 n 0%4=2 := by
        simp [weight];omega
      rw [hh.1,hh.2]
      rfl
    · have hh : weight 0 n 1 /4=n+1 ∧ weight 0 n 1%4=0 := by
        simp [weight];omega
      rw [hh.1,hh.2]
      rfl
    · have hh : weight 0 n 2 /4=n+2 ∧ weight 0 n 2%4=0 := by
        simp [weight];omega
      rw [hh.1,hh.2]
      rfl
  | succ k ih =>
    rcases p with _|_|p
    · simp only [iter, next, Option.bind_some]
      rw [w0 k n]
      exact ih (n+1) 2 (by omega)
    · simp only [iter, next, Option.bind_some]
      rw [w1 k n]
      exact ih (n+1) 0 (by omega)
    · simp only [iter, next, Option.bind_some]
      rw [w2 k n p]
      exact ih (n+2) p (by omega)

/-- Large P counter has the same exact duration k+1 before return to C. -/
theorem P_large_fuel (k n p : Nat) (hp : 2*k+2≤p) :
    iter (k+1) (.P k n p) =
      some (.C (n+2*k+2) (p-2*k-2)) := by
  induction k generalizing n p with
  | zero =>
    obtain ⟨r,rfl⟩ : ∃r, p=r+2 := ⟨p-2,by omega⟩
    have hh : n+2*0+2=n+2 ∧ r+2-2*0-2=r := by omega
    rw [hh.1,hh.2]
    rfl
  | succ k ih =>
    obtain ⟨r,rfl⟩ : ∃r, p=r+2 := ⟨p-2,by omega⟩
    have hh : n+2*(k+1)+2=(n+2)+2*k+2 ∧
        r+2-2*(k+1)-2=r-2*k-2 := by omega
    rw [hh.1,hh.2]
    simp only [iter, next, Option.bind_some]
    exact ih (n+2) r (by omega)

/-- Every nontrivial C episode has exact source duration a+2. -/
theorem C_step_exact_fuel (a b u v : Nat)
    (hb : 2≤b) (he : Cstep a b=some (u,v)) :
    iter (a+2) (.C a b) = some (.C u v) := by
  obtain ⟨d,rfl⟩ : ∃d,b=d+2 := ⟨b-2,by omega⟩
  have hzero : d+2≠0 := by omega
  have hone : d+2≠1 := by omega
  by_cases hbig : 2*a≤d
  · have ht : some (2*a+2,d-2*a)=some (u,v) := by
      simpa [Cstep,hzero,hone,hbig] using he
    have hu : u=2*a+2 ∧ v=d-2*a := by simpa using ht.symm
    rcases hu with ⟨rfl,rfl⟩
    have hs : 0+2*a+2=2*a+2 ∧ d+2-2*a-2=d-2*a := by omega
    change iter (a+1) (.P a 0 (d+2)) =
      some (.C (2*a+2) (d-2*a))
    simpa [hs.1,hs.2] using P_large_fuel a 0 (d+2) (by omega)
  · have ht : some ((6*a+d+(if d%2=0 then 8 else 5))/4,
      (6*a+d+(if d%2=0 then 8 else 5))%4)=some (u,v) := by
      simpa [Cstep,hzero,hone,hbig] using he
    have hu : u=(6*a+d+(if d%2=0 then 8 else 5))/4 ∧
      v=(6*a+d+(if d%2=0 then 8 else 5))%4 := by simpa using ht.symm
    rcases hu with ⟨rfl,rfl⟩
    have hp : d+2≤2*a+2 := by omega
    have hpar : (d+2)%2=d%2 := by omega
    have hw : weight a 0 (d+2)=6*a+d+(if d%2=0 then 8 else 5) := by
      simp only [weight,hpar]
      by_cases hval : d%2=0
      · simp only [if_pos hval];omega
      · simp only [if_neg hval];omega
    change iter (a+1) (.P a 0 (d+2)) =
      some (.C ((6*a+d+(if d%2=0 then 8 else 5))/4)
        ((6*a+d+(if d%2=0 then 8 else 5))%4))
    simpa [hw] using P_sweep_fuel a 0 (d+2) hp

#print axioms C_step_exact_fuel

end CascadeSource
