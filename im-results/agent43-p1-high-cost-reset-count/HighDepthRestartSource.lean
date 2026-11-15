import CountedWallStrongGateSource

namespace BB6.Agent43HighDepthRestart

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent47P1
open BB6.Agent43LastResetStrength

/-- The affine-wall defect and its shifted cost coordinate. -/
def wallDefect (n b m : Nat) : Int :=
  (b : Int) + 2*(m : Int) + 2*(n : Int) + 8 - 12*(2 : Int)^n

def wallBudget (n m : Nat) : Nat := m+n+6

/-- Exact one-step defect transport for an authentic inverse edge.
    Only source mass, left divisibility, inverse power, and inverse mass
    are used; no simulator or endpoint approximation enters. -/
theorem defect_step_exact (n b d m t k c : Nat)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (hk : 2≤k) :
    (2 : Int)^(t+1) * (wallDefect n (2*k-4) (m+t+1) + 6) =
      wallDefect n b m + 2*(wallBudget n m : Int) +
        ((2 : Int)^(t+2)-16)*(2 : Int)^n := by
  have hmassI : (b:Int)+(d:Int)+2*(m:Int)+2*(n:Int)+13=14*(2:Int)^n := by
    exact_mod_cast hmass
  have hinvI : 2*(k:Int)+(c:Int)+2*(t:Int)+2=(b:Int)+(d:Int) := by
    exact_mod_cast hinvMass
  have hdiv : 2*(b/2)=b := by omega
  have hdivI : 2*(b/2:Int)=(b:Int) := by exact_mod_cast hdiv
  have hpowerI : (2:Int)^t*((c:Int)+3)=(d:Int)+(b/2:Int)+3 := by
    exact_mod_cast hpower.symm
  have hpow1 : (2:Int)^(t+1)=2*(2:Int)^t := by
    rw [Int.pow_succ]
    omega
  have hpow2 : (2:Int)^(t+2)=2*(2:Int)^(t+1) := by
    rw [show t+2=(t+1)+1 by omega, Int.pow_succ]
    exact Int.mul_comm _ _
  have hF : wallDefect n (2*k-4) (m+t+1)+6 = 2*(2:Int)^n - ((c:Int)+3) := by
    unfold wallDefect
    push_cast
    omega
  calc
    (2:Int)^(t+1) * (wallDefect n (2*k-4) (m+t+1)+6)
        = (2:Int)^(t+1) * (2*(2:Int)^n - ((c:Int)+3)) := by rw [hF]
    _ = (2:Int)^(t+2)*(2:Int)^n - 2*((2:Int)^t*((c:Int)+3)) := by
      rw [Int.mul_sub, ←Int.mul_assoc]
      rw [Int.mul_comm ((2:Int)^(t+1)) 2, ←hpow2, hpow1, Int.mul_assoc]
    _ = (2:Int)^(t+2)*(2:Int)^n - 2*((d:Int)+(b/2:Int)+3) := by rw [hpowerI]
    _ = wallDefect n b m + 2*(wallBudget n m : Int) +
          ((2:Int)^(t+2)-16)*(2:Int)^n := by
      have hmass2 : 2*(b:Int)+2*(d:Int)+4*(m:Int)+4*(n:Int)+26=28*(2:Int)^n := by
        omega
      unfold wallDefect wallBudget
      rw [Int.sub_mul]
      push_cast
      omega

/-- For every depth at least three, the next defect is strictly positive.
    The bound n>=14 is inherited from the critical P1 root. -/
theorem pow_gap_coeff (t : Nat) (ht : 3 ≤ t) :
    (2 : Int)^(t-1) + 28 ≤ (2 : Int)^(t+2) := by
  have hpowNat : 2^(t+2) = 8*2^(t-1) := by
    calc
      2^(t+2) = 2^((t-1)+3) := by congr 1 <;> omega
      _ = 2^(t-1)*2^3 := by rw [Nat.pow_add]
      _ = 8*2^(t-1) := by rw [show 2^3=8 by decide, Nat.mul_comm]
  have hsmall : 4 ≤ 2^(t-1) := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^(t-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hcoeffNat : 2^(t-1)+28 ≤ 2^(t+2) := by
    rw [hpowNat]
    omega
  exact_mod_cast hcoeffNat

theorem defect_deep_positive (n b d m t k c : Nat)
    (hn : 14 ≤ n)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (hk : 2≤k)
    (ht : 3≤t) :
    0 < wallDefect n (2*k-4) (m+t+1) := by
  have hstep := defect_step_exact n b d m t k c hmass hb hpower hinvMass hk
  have hstepW : (2:Int)^(t+1) * (wallDefect n (2*k-4) (m+t+1)+6) =
      (b:Int)+4*(m:Int)+4*(n:Int)+20 +
        ((2:Int)^(t+2)-28)*(2:Int)^n := by
    rw [hstep]
    unfold wallDefect wallBudget
    simp only [Int.sub_mul]
    push_cast
    omega
  have hcoeff := pow_gap_coeff t ht
  have hcoeffI : (2:Int)^(t-1) ≤ (2:Int)^(t+2)-28 := by omega
  have hPnonneg : 0 ≤ (2:Int)^n := Int.le_of_lt (Int.pow_pos (by decide))
  have hmul : (2:Int)^(t-1)*(2:Int)^n ≤
      ((2:Int)^(t+2)-28)*(2:Int)^n :=
    Int.mul_le_mul_of_nonneg_right hcoeffI hPnonneg
  have hWnonneg : 0 ≤ (b:Int)+4*(m:Int)+4*(n:Int)+20 := by omega
  have hlower : (2:Int)^(t-1)*(2:Int)^n ≤
      (2:Int)^(t+1)*(wallDefect n (2*k-4) (m+t+1)+6) := by
    rw [hstepW]
    omega
  have hscale : (2:Int)^(t+1) = 4*(2:Int)^(t-1) := by
    calc
      (2:Int)^(t+1) = (2:Int)^((t-1)+2) := by congr 1 <;> omega
      _ = (2:Int)^(t-1)*(2:Int)^2 := by rw [Int.pow_add]
      _ = 4*(2:Int)^(t-1) := by rw [show (2:Int)^2=4 by decide, Int.mul_comm]
  have hX : 0 < (2:Int)^(t-1) := Int.pow_pos (by decide)
  have hdivided : (2:Int)^(t-1)*(2:Int)^n ≤
      (2:Int)^(t-1)*(4*(wallDefect n (2*k-4) (m+t+1)+6)) := by
    calc
      (2:Int)^(t-1)*(2:Int)^n ≤
          (2:Int)^(t+1)*(wallDefect n (2*k-4) (m+t+1)+6) := hlower
      _ = 4*(2:Int)^(t-1)*(wallDefect n (2*k-4) (m+t+1)+6) := by rw [hscale]
      _ = (2:Int)^(t-1)*(4*(wallDefect n (2*k-4) (m+t+1)+6)) := by
            calc
              4*(2:Int)^(t-1)*(wallDefect n (2*k-4) (m+t+1)+6)
                  = 4*((2:Int)^(t-1)*(wallDefect n (2*k-4) (m+t+1)+6)) := by
                      exact Int.mul_assoc _ _ _
              _ = (4*(2:Int)^(t-1))*(wallDefect n (2*k-4) (m+t+1)+6) := by
                      rw [←Int.mul_assoc]
              _ = ((2:Int)^(t-1)*4)*(wallDefect n (2*k-4) (m+t+1)+6) := by
                      rw [Int.mul_comm 4 ((2:Int)^(t-1))]
              _ = (2:Int)^(t-1)*(4*(wallDefect n (2*k-4) (m+t+1)+6)) := by
                      rw [Int.mul_assoc]
  have hPbound : (2:Int)^n ≤ 4*(wallDefect n (2*k-4) (m+t+1)+6) :=
    Int.le_of_mul_le_mul_left hdivided hX
  have hPnat : 24 < 2^n := by
    have hle : 2^14 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    have h24 : 24 < 2^14 := by decide
    omega
  have hP : 24 < (2:Int)^n := by exact_mod_cast hPnat
  omega

/-- Depth two preserves a positive defect once the shifted budget is at least 24. -/
theorem defect_two_positive (n b d m k c : Nat)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^2*(c+3))
    (hinvMass : 2*k+c+2*2+2=b+d)
    (hk : 2≤k)
    (hF : 0 < wallDefect n b m)
    (hB : 24 ≤ wallBudget n m) :
    0 < wallDefect n (2*k-4) (m+3) := by
  have hstep := defect_step_exact n b d m 2 k c hmass hb hpower hinvMass hk
  have hstep2 : 8*(wallDefect n (2*k-4) (m+3)+6) =
      wallDefect n b m + 2*(wallBudget n m : Int) := by
    simpa [wallBudget] using hstep
  omega

theorem wallDefect_negative_at_wall (n b m : Nat)
    (hwall : b+4*m+4*n+20=12*2^n) :
    wallDefect n b m < 0 := by
  have hwallI : (b:Int)+4*(m:Int)+4*(n:Int)+20=12*(2:Int)^n := by
    exact_mod_cast hwall
  unfold wallDefect
  omega

/-- A depth trace records every actual inverse depth, in constructor order. -/
def oddConeDepths {b0 d0 b d m : Nat} : OddCone b0 d0 b d m → List Nat
  | .root => []
  | .parent _ _ _ t _ _ hpre _ _ _ _ _ _ => oddConeDepths hpre ++ [t]

def NoDeep (xs : List Nat) : Prop := ∀ t, t ∈ xs → t < 3

def HasDeep (xs : List Nat) : Prop :=
  ∃ pre deep post, xs = pre ++ [deep] ++ post ∧ 3 ≤ deep

def HasDeepThenShallow (xs : List Nat) : Prop :=
  ∃ pre deep mid shallow post,
    xs = pre ++ [deep] ++ mid ++ [shallow] ++ post ∧ 3 ≤ deep ∧ shallow ≤ 1

theorem noDeep_append_singleton {xs : List Nat} {t : Nat}
    (h : NoDeep xs) (ht : t < 3) : NoDeep (xs ++ [t]) := by
  intro u hu
  rcases List.mem_append.mp hu with hxs | hlast
  · exact h u hxs
  · simp at hlast
    subst u
    exact ht

theorem hasDeep_append_singleton {xs : List Nat} {t : Nat}
    (h : HasDeep xs) : HasDeep (xs ++ [t]) := by
  rcases h with ⟨pre,deep,post,hEq,hdeep⟩
  refine ⟨pre,deep,post ++ [t],?_,hdeep⟩
  rw [hEq, List.append_assoc]

theorem hasDeep_append_last {xs : List Nat} {t : Nat}
    (ht : 3 ≤ t) : HasDeep (xs ++ [t]) := by
  refine ⟨xs,t,[],?_,ht⟩
  simp

theorem hasDeepThenShallow_append {xs : List Nat} {ys : List Nat}
    (h : HasDeepThenShallow xs) : HasDeepThenShallow (xs ++ ys) := by
  rcases h with ⟨pre,deep,mid,shallow,post,hEq,hdeep,hshallow⟩
  refine ⟨pre,deep,mid,shallow,post ++ ys,?_,hdeep,hshallow⟩
  rw [hEq, List.append_assoc]

theorem hasDeep_then_shallow_append_singleton {xs : List Nat} {t : Nat}
    (h : HasDeep xs) (ht : t ≤ 1) : HasDeepThenShallow (xs ++ [t]) := by
  rcases h with ⟨pre,deep,post,hEq,hdeep⟩
  refine ⟨pre,deep,post,t,[],?_,hdeep,ht⟩
  rw [hEq]
  simp [List.append_assoc]

theorem hasDeep_not_noDeep {xs : List Nat}
    (hd : HasDeep xs) (hn : NoDeep xs) : False := by
  rcases hd with ⟨pre,deep,post,hEq,hdeep⟩
  have hmem : deep ∈ xs := by
    rw [hEq]
    simp
  have hsmall := hn deep hmem
  omega

/-- The path classifier has three states: no high-depth reset yet; a high-depth
    reset whose defect remains positive and has not yet been discharged by a
    later shallow edge; or a history already containing a shallow edge after
    a high-depth edge. -/
inductive RestartStatus (n : Nat) (xs : List Nat) (b m : Nat) : Type
  | noDeep (hNo : NoDeep xs) : RestartStatus n xs b m
  | awaiting (hDeep : HasDeep xs) (hF : 0 < wallDefect n b m)
      (hB : 24 ≤ wallBudget n m) : RestartStatus n xs b m
  | discharged (hWitness : HasDeepThenShallow xs) : RestartStatus n xs b m

/-- Every authentic critical OddCone history has one of the three restart
    statuses. The awaiting state is protected by the defect barrier. -/
theorem classify_restart_status (n b d m : Nat) (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m) :
    RestartStatus n (oddConeDepths h) b m := by
  induction h with
  | root =>
      exact RestartStatus.noDeep (by intro t ht; simp [oddConeDepths] at ht)
  | parent bp dp mp t k c hpre hb hb4 hd hi hk hc ih =>
      have hmass0 := odd_cone_mass (14*2^n-2*n-16) 3 bp dp mp hpre
      have hmass : bp+dp+2*mp+2*n+13=14*2^n := by omega
      have hsource := (inverseAt_iff_power_mass bp dp t k c (by omega) hb4 hd).mp hi
      have hpower := hsource.1
      have hinvMass : 2*k+c+2*t+2=bp+dp := by
        simpa [hc] using hsource.2
      cases ih with
      | noDeep hNo =>
          by_cases hdeep : 3≤t
          · have hFdeep : 0 < wallDefect n (2*k-4) (mp+t+1) :=
              defect_deep_positive n bp dp mp t k c hn hmass hb4 hpower hinvMass hk hdeep
            have hBdeep : 24 ≤ wallBudget n (mp+t+1) := by
              unfold wallBudget
              omega
            exact RestartStatus.awaiting
              (hasDeep_append_last (oddConeDepths hpre) t hdeep) hFdeep hBdeep
          · exact RestartStatus.noDeep
              (noDeep_append_singleton hNo (by omega))
      | awaiting hDeep hF hB =>
          by_cases hdeep : 3≤t
          · have hFdeep : 0 < wallDefect n (2*k-4) (mp+t+1) :=
              defect_deep_positive n bp dp mp t k c hn hmass hb4 hpower hinvMass hk hdeep
            have hBdeep : 24 ≤ wallBudget n (mp+t+1) := by
              unfold wallBudget
              omega
            exact RestartStatus.awaiting
              (hasDeep_append_last (oddConeDepths hpre) t hdeep) hFdeep hBdeep
          · by_cases htwo : t=2
            · have hpower2 : dp+bp/2+3=2^2*(c+3) := by simpa [htwo] using hpower
              have hinv2 : 2*k+c+2*2+2=bp+dp := by simpa [htwo] using hinvMass
              have hFtwo : 0 < wallDefect n (2*k-4) (mp+3) :=
                defect_two_positive n bp dp mp k c hmass hb4 hpower2 hinv2 hk hF hB
              have hFtwo' : 0 < wallDefect n (2*k-4) (mp+t+1) := by simpa [htwo] using hFtwo
              exact RestartStatus.awaiting
                (hasDeep_append_singleton (oddConeDepths hpre) hDeep) hFtwo' (by
                  unfold wallBudget at *
                  omega)
            · exact RestartStatus.discharged
                (hasDeep_then_shallow_append_singleton
                  (oddConeDepths hpre) hDeep (by omega))
      | discharged hWitness =>
          exact RestartStatus.discharged
            (hasDeepThenShallow_append hWitness [t])

/-- Any critical source wall history containing a depth>=3 edge must contain
    a later depth-0 or depth-1 edge. This is an unrestricted-depth theorem. -/
theorem source_wall_deep_requires_shallow (n b d m : Nat)
    (hn : 14 ≤ n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b+4*m+4*n+20=12*2^n)
    (hdeep : HasDeep (oddConeDepths h)) :
    HasDeepThenShallow (oddConeDepths h) := by
  have hstatus := classify_restart_status n b d m hn h
  cases hstatus with
  | noDeep hNo =>
      exact False.elim (hasDeep_not_noDeep hdeep hNo)
  | awaiting hDeep hF hB =>
      have hnegative := wallDefect_negative_at_wall n b m hwall
      omega
  | discharged hWitness => exact hWitness

/-- Counted histories inherit the same restart barrier through the authentic
    CountCone-to-OddCone source map. -/
theorem counted_source_wall_deep_requires_shallow
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall : b+4*m+4*n+20=12*2^n)
    (hdeep : HasDeep (oddConeDepths
      (counted_to_odd_cone (14*2^n-2*n-16) 3 b d m z h))) :
    HasDeepThenShallow (oddConeDepths
      (counted_to_odd_cone (14*2^n-2*n-16) 3 b d m z h)) := by
  exact source_wall_deep_requires_shallow n b d m hn
    (counted_to_odd_cone (14*2^n-2*n-16) 3 b d m z h) hwall hdeep

#print axioms BB6.Agent43HighDepthRestart.defect_step_exact
#print axioms BB6.Agent43HighDepthRestart.defect_deep_positive
#print axioms BB6.Agent43HighDepthRestart.defect_two_positive
#print axioms BB6.Agent43HighDepthRestart.classify_restart_status
#print axioms BB6.Agent43HighDepthRestart.source_wall_deep_requires_shallow
#print axioms BB6.Agent43HighDepthRestart.counted_source_wall_deep_requires_shallow

end BB6.Agent43HighDepthRestart
