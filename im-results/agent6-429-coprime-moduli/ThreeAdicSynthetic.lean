import BB429Rank
import BB429Burst
import BB429DyadicStarts
import Agent6TwoBurstOne
import Agent6TwoBurstZero
import ThreeAdicLifting
import ThreeAdicG2
import ThreeAdicH0
import Lean.Elab.Tactic.Omega

/-!
Uniform 3-adic coverage by genuine full-source-map *synthetic* halting starts
for the accelerated #429 machine.  The starts are not claimed blank-reachable.
The final theorem is a method obstruction for fixed 3-power residue invariants,
not a decision of #429 or BB(6).
-/

namespace Agent6ThreeAdic

open ThreeAdic

private theorem mul_three_mod (m x y : Nat) (h : x % m = y % m) :
    (3*x) % (3*m) = (3*y) % (3*m) := by
  rw [Nat.mul_mod_mul_left 3 x m, Nat.mul_mod_mul_left 3 y m, h]

/-- The scaled G1 sequence has the exact three-lift shift needed by the
generic residue-lifting theorem.  Restricting G1 to even parameters makes
the parameter step compatible with the coefficient 8. -/
private theorem G1_scaled_shift (e q : Nat) :
    (8*G1 (q+4*3^e)+2*3^e) % (3^(e+1)) =
      (8*G1 q) % (3^(e+1)) := by
  let p := 2*3^e
  let M := 3^(e+1)
  have hs1 : (G1 (q+p)+p) % M = G1 q % M := by
    simpa [p, M] using G1_shift e q
  have hs2 : (G1 (q+p+p)+p) % M = G1 (q+p) % M := by
    simpa [p, M, Nat.add_assoc] using G1_shift e (q+p)
  have hdouble : (G1 (q+p+p)+p+p) % M = G1 q % M := by
    calc
      (G1 (q+p+p)+p+p) % M =
          ((G1 (q+p+p)+p) % M + p % M) % M := by rw [Nat.add_mod]
      _ = (G1 (q+p) % M + p % M) % M := by rw [hs2]
      _ = (G1 (q+p)+p) % M := (Nat.add_mod _ _ _).symm
      _ = G1 q % M := hs1
  have hmul : (8*(G1 (q+p+p)+p+p)) % M = (8*G1 q) % M := by
    calc
      _ = (8 % M * ((G1 (q+p+p)+p+p) % M)) % M := Nat.mul_mod _ _ _
      _ = (8 % M * (G1 q % M)) % M := by rw [hdouble]
      _ = (8*G1 q) % M := (Nat.mul_mod _ _ _).symm
  have hM : M = 3*3^e := by
    dsimp [M]
    rw [Nat.pow_succ]
    omega
  have hperiod : 15*p = 10*M := by
    dsimp [p]
    rw [hM]
    omega
  have hsum :
      (8*G1 (q+p+p)+p) % M =
        (8*G1 (q+p+p)+p+15*p) % M := by
    have hz : (15*p) % M = 0 := by rw [hperiod]; simp
    calc
      (8*G1 (q+p+p)+p) % M =
          ((8*G1 (q+p+p)+p) % M + 0) % M := by simp
      _ = ((8*G1 (q+p+p)+p) % M + (15*p) % M) % M := by rw [hz]
      _ = (8*G1 (q+p+p)+p+15*p) % M := (Nat.add_mod _ _ _).symm
  have hEq :
      8*G1 (q+p+p)+p+15*p =
        8*(G1 (q+p+p)+p+p) := by omega
  have hq : q+4*3^e = q+p+p := by dsimp [p]; omega
  change (8*G1 (q+4*3^e)+2*3^e) % M = (8*G1 q) % M
  rw [hq]
  calc
    (8*G1 (q+p+p)+p) % M =
        (8*(G1 (q+p+p)+p+p)) % M := by rw [←hEq, hsum]
    _ = (8*G1 q) % M := hmul

private theorem G1_scaled_all_residues (E r : Nat) :
    ∃ n, 1 ≤ n ∧ n ≤ 1+2*(3^E-1) ∧
      (8*G1 (2*n)) % (3^E) = r % (3^E) := by
  exact all_residues (fun n => 8*G1 (2*n)) 1
    (by
      intro e n
      have harg : 2*(n+2*3^e) = 2*n+4*3^e := by omega
      rw [harg]
      exact G1_scaled_shift e (2*n)) E r

/-- The residue-2 family is the direct first-burst family. -/
private theorem family_two (t : Nat) (ht : 1 ≤ t) :
    ∃ n a b, BB429.run n (0,3*G2 t-13) = some (a,b) ∧
      BB429.next (a,b) = none := by
  let W := 3*G2 t-13
  have hpow := pow_two_growth t
  have hbase : t ≤ 4*2^t := by omega
  have hG : G2 t+t = 4*2^t := by
    dsimp [G2]
    exact Nat.sub_add_cancel hbase
  have hGlo : 7 ≤ G2 t := by dsimp [G2]; omega
  have hpos : 13 ≤ 3*G2 t := by omega
  have hW : W+13 = 3*G2 t := by
    dsimp [W]
    exact Nat.sub_add_cancel hpos
  have hgate :
      2*0+W+3*t+13 = 4*((0+3)*2^t) := by
    calc
      2*0+W+3*t+13 = (W+13)+3*t := by omega
      _ = 3*G2 t+3*t := by rw [hW]
      _ = 3*(G2 t+t) := by omega
      _ = 3*(4*2^t) := by rw [hG]
      _ = 4*((0+3)*2^t) := by omega
  obtain ⟨n,a,b,hfirst,hline⟩ :=
    (BB429Burst.burst_gateway_iff 0 W).mpr ⟨t,hgate⟩
  exact ⟨n,a,b,BB429DyadicStarts.first_prefix_is_source _ _ _ hfirst,
    (BB429.next_none_iff_halt_line a b).mpr hline⟩

/-- Agent 1's G1 parameter is one greater than Agent 6's source-family index. -/
private theorem demand_one_relation (q : Nat) (hq : 1 ≤ q) :
    Agent6TwoBurstOne.demand (q-1)+29 = 24*G1 q := by
  have hdepth : Agent6TwoBurstOne.depth (q-1) = 4*q+1 := by
    simp [Agent6TwoBurstOne.depth]
    omega
  have hpower : Agent6TwoBurstOne.power (q-1) = 2^(4*q+1) := by
    simp [Agent6TwoBurstOne.power, hdepth]
  have hlin : 24*(q-1)+53 = 24*q+29 := by omega
  have hpos : 24*q+53 ≤ 12*2^(4*q+1) := by
    by_cases hq1 : q=1
    · subst q
      decide
    · have hq2 : 2 ≤ q := by omega
      have hp := pow_two_growth (4*q+1)
      omega
  have h16 : 16^q = 2^(4*q) := by
    calc
      16^q = (2^4)^q := by rw [show (16:Nat)=2^4 by decide]
      _ = 2^(4*q) := (Nat.pow_mul 2 4 q).symm
  have hpowid : 12*2^(4*q+1) = 24*16^q := by
    rw [Nat.pow_succ, h16]
    omega
  have hd : Agent6TwoBurstOne.demand (q-1)+(24*q+29) = 24*16^q := by
    simp only [Agent6TwoBurstOne.demand, Agent6TwoBurstOne.power,
      Agent6TwoBurstOne.depth]
    rw [show 4*(q-1)+5=4*q+1 by omega, hlin, hpowid]
    exact Nat.sub_add_cancel (by omega)
  have hqpow : q ≤ 16^q := by
    have h2 := pow_two_growth q
    have hh : 2^q ≤ 16^q := Nat.pow_le_pow_left (by decide) q
    omega
  have hG : G1 q+q = 16^q := by
    dsimp [G1]
    exact Nat.sub_add_cancel hqpow
  have hGscaled : 24*G1 q+24*q = 24*16^q := by
    calc
      _ = 24*(G1 q+q) := by omega
      _ = 24*16^q := by rw [hG]
  omega

/-- Agent 6's class-zero source demand is exactly three times Agent 1's H0. -/
private theorem demand_zero_relation (c : Nat) (hc : 2 ≤ c) :
    Agent6TwoBurstZero.demand (c-2) = 3*H0 c := by
  have hp : 4 ≤ 2^c := by
    have hh : 2^2 ≤ 2^c := Nat.pow_le_pow_right (by decide) hc
    simpa using hh
  have hC : Agent6TwoBurstZero.c (c-2) = c := by
    simp [Agent6TwoBurstZero.c, Nat.sub_add_cancel (by omega : 2≤c)]
  have hP : Agent6TwoBurstZero.p (c-2) = 2^c := by
    simp [Agent6TwoBurstZero.p, hC]
  have hK : Agent6TwoBurstZero.k (c-2) = 4*2^c-11 := by
    simp [Agent6TwoBurstZero.k, hP]
  have hN : Agent6TwoBurstZero.n (c-2) = N c := by
    simp [Agent6TwoBurstZero.n, hK, hC, N]
    omega
  have hQ : Agent6TwoBurstZero.Q (c-2) = 2^(N c) := by
    simp [Agent6TwoBurstZero.Q, hN]
  have hNlower : c+2 ≤ N c := by
    dsimp [N]
    have hh := pow_two_growth c
    omega
  have hpowle : 4*2^c ≤ 2^(N c) := by
    have hh : 2^(c+2) ≤ 2^(N c) := Nat.pow_le_pow_right (by decide) hNlower
    have heq : 2^(c+2) = 4*2^c := by
      rw [Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      exact Nat.mul_comm _ _
    omega
  have hbig : 48*2^c ≤ 12*2^(N c) := by omega
  have hlin : 3*c ≤ 24*2^c := by
    have hh := pow_two_growth c
    omega
  have hsub1 : 24*2^c ≤ 12*2^(N c) := by omega
  have hsub2 : 3*c ≤ 12*2^(N c)-24*2^c+39 := by omega
  calc
    Agent6TwoBurstZero.demand (c-2)
      = 12*2^(N c)-24*2^c+39-3*c := by
          simp only [Agent6TwoBurstZero.demand, hQ, hP, hC]
    _ = 3*(4*2^(N c)-8*2^c+13-c) := by omega
    _ = 3*H0 c := by rw [H0_eq_paper c hc]

private theorem mod_three_power (E : Nat) (hE : 1 ≤ E) :
    3*(3^(E-1)) = 3^E := by
  calc
    3*3^(E-1) = 3^(E-1)*3 := Nat.mul_comm _ _
    _ = 3^(E-1+1) := (Nat.pow_succ 3 (E-1)).symm
    _ = 3^E := by rw [Nat.sub_add_cancel hE]

/-- For every E≥1 and every residue, some synthetic u=0 start in that
3-adic cylinder halts under the complete twelve-branch BB429 source map. -/
theorem synthetic_halt_every_three_power (E r : Nat) (hE : 1 ≤ E) :
    ∃ W n a b, W%3^E = r%3^E ∧
      BB429.run n (0,W) = some (a,b) ∧ BB429.next (a,b) = none := by
  let M := 3^(E-1)
  let R := r%(3^E)
  have hM : 3*M=3^E := by simpa [M] using mod_three_power E hE
  have hMpos : 0<M := by dsimp [M]; exact Nat.pow_pos (by omega)
  have hR3lt : R%3<3 := Nat.mod_lt _ (by omega)
  by_cases h0 : R%3=0
  · let s := R/3
    obtain ⟨c,hc,_,hres⟩ := H0_all_residues (E-1) s
    have hRdiv : R=3*s := by
      dsimp [s]
      have hh := (Nat.mod_add_div R 3).symm
      rw [h0] at hh
      omega
    let W := Agent6TwoBurstZero.demand (c-2)
    have hW : W=3*H0 c := by dsimp [W]; exact demand_zero_relation c hc
    have hsum : W%(3*M)=R%(3*M) := by
      calc
        W%(3*M)=(3*H0 c)%(3*M) := by rw [hW]
        _=(3*s)%(3*M) :=
          mul_three_mod M (H0 c) s (by simpa [M] using hres)
        _=R%(3*M) := by rw [hRdiv]
    have hcong : W%3^E=R%3^E := by simpa [hM] using hsum
    obtain ⟨n,a,b,hr,hh⟩ :=
      Agent6TwoBurstZero.full_source_synthetic_halt (c-2)
    exact ⟨W,n,a,b,by simpa [R] using hcong,hr,hh⟩
  · by_cases h1 : R%3=1
    · let s := R/3+10
      obtain ⟨n,hn,_,hres⟩ := G1_scaled_all_residues (E-1) s
      let q := 2*n
      have hq : 1≤q := by dsimp [q]; omega
      have hRdiv : R+29=3*s := by
        dsimp [s]
        have hh := (Nat.mod_add_div R 3).symm
        rw [h1] at hh
        omega
      let W := Agent6TwoBurstOne.demand (q-1)
      have hW : W+29=3*(8*G1 q) := by
        calc
          W+29=24*G1 q := demand_one_relation q hq
          _=3*(8*G1 q) := by omega
      have hsum : (W+29)%(3*M)=(R+29)%(3*M) := by
        calc
          (W+29)%(3*M)=(3*(8*G1 q))%(3*M) := by rw [hW]
          _=(3*s)%(3*M) :=
            mul_three_mod M (8*G1 q) s (by simpa [M,q] using hres)
          _=(R+29)%(3*M) := by rw [hRdiv]
      have hcancel := mod_add_cancel (3*M) W R 29 (by omega) hsum
      have hcong : W%3^E=R%3^E := by simpa [hM] using hcancel
      obtain ⟨n,a,b,hr,hh⟩ :=
        Agent6TwoBurstOne.full_source_synthetic_halt (q-1)
      exact ⟨W,n,a,b,by simpa [R] using hcong,hr,hh⟩
    · have h2 : R%3=2 := by omega
      let s := R/3+5
      obtain ⟨t,ht,_,hres⟩ := G2_all_residues (E-1) s
      have hRdiv : R+13=3*s := by
        dsimp [s]
        have hh := (Nat.mod_add_div R 3).symm
        rw [h2] at hh
        omega
      let W := 3*G2 t-13
      have hpow := pow_two_growth t
      have hbase : t≤4*2^t := by omega
      have hG : G2 t+t=4*2^t := by
        dsimp [G2]
        exact Nat.sub_add_cancel hbase
      have hGlo : 7≤G2 t := by dsimp [G2]; omega
      have hpos : 13≤3*G2 t := by omega
      have hW : W+13=3*G2 t := by dsimp [W]; exact Nat.sub_add_cancel hpos
      have hsum : (W+13)%(3*M)=(R+13)%(3*M) := by
        calc
          (W+13)%(3*M)=(3*G2 t)%(3*M) := by rw [hW]
          _=(3*s)%(3*M) :=
            mul_three_mod M (G2 t) s (by simpa [M] using hres)
          _=(R+13)%(3*M) := by rw [hRdiv]
      have hcancel := mod_add_cancel (3*M) W R 13 (by omega) hsum
      have hcong : W%3^E=R%3^E := by simpa [hM] using hcancel
      obtain ⟨n,a,b,hfirst,hline⟩ :=
        (BB429Burst.burst_gateway_iff 0 W).mpr ⟨t,by
          calc
            2*0+W+3*t+13=(W+13)+3*t := by omega
            _=3*G2 t+3*t := by rw [hW]
            _=3*(G2 t+t) := by omega
            _=3*(4*2^t) := by rw [hG]
            _=4*((0+3)*2^t) := by omega⟩
      have hrun := BB429DyadicStarts.first_prefix_is_source _ _ _ hfirst
      have hhalt := (BB429.next_none_iff_halt_line a b).mpr hline
      exact ⟨W,n,a,b,by simpa [R] using hcong,hrun,hhalt⟩

private theorem invariant_of_run (P : BB429.State → Prop)
    (hstep : ∀ s t, P s → BB429.next s=some t → P t)
    (n : Nat) (s t : BB429.State)
    (h : BB429.run n s=some t) (hs : P s) : P t := by
  induction n generalizing t with
  | zero =>
    simp [BB429.run] at h
    cases h
    exact hs
  | succ n ih =>
    simp only [BB429.run] at h
    cases hp : BB429.run n s with
    | none => simp [hp] at h
    | some mid =>
      simp only [hp, Option.bind_some] at h
      exact hstep mid t (ih mid hp) h

/-- No forward-invariant, halt-free predicate on the accelerated counters can
contain blank and be saturated under the second counter modulo any fixed
3-power at exact first counter zero.  The witness is synthetic. -/
theorem no_three_power_periodic_invariant (E : Nat) (hE : 1≤E)
    (P : BB429.State → Prop)
    (hroot : P (0,0))
    (hsat : ∀ x y, x%3^E=y%3^E → P (0,x) → P (0,y))
    (hstep : ∀ s t, P s → BB429.next s=some t → P t)
    (hhalt : ∀ s, BB429.next s=none → ¬P s) : False := by
  obtain ⟨W,n,a,b,hmod,hrun,hh⟩ :=
    synthetic_halt_every_three_power E 0 hE
  have hzero : 0%3^E=W%3^E := by simpa using hmod.symm
  have hstart : P (0,W) := hsat 0 W hzero hroot
  have hend : P (a,b) :=
    invariant_of_run P hstep n (0,W) (a,b) hrun hstart
  exact hhalt (a,b) hh hend

/-- The authentic blank run reaches (0,44), whose second counter is
2 modulo 3. -/
theorem blank_reaches_two_residue_zero_row :
    BB429.run 7 (0,0) = some (0,44) := by decide

/-- Even a single 3^E cylinder around the root-reachable state (0,44)
cannot be included in a forward-invariant halt-free predicate. -/
theorem no_three_power_cylinder_invariant (E : Nat) (hE : 1≤E)
    (P : BB429.State → Prop)
    (hroot : P (0,0))
    (hsat : ∀ y, 44%3^E=y%3^E → P (0,44) → P (0,y))
    (hstep : ∀ s t, P s → BB429.next s=some t → P t)
    (hhalt : ∀ s, BB429.next s=none → ¬P s) : False := by
  obtain ⟨W,n,a,b,hmod,hrun,hh⟩ :=
    synthetic_halt_every_three_power E 44 hE
  have hmod44 : 44%3^E=W%3^E := by simpa using hmod.symm
  have hroot44 : P (0,44) :=
    invariant_of_run P hstep 7 (0,0) (0,44)
      blank_reaches_two_residue_zero_row hroot
  have hstart : P (0,W) := hsat W hmod44 hroot44
  have hend : P (a,b) :=
    invariant_of_run P hstep n (0,W) (a,b) hrun hstart
  exact hhalt (a,b) hh hend

/-- Every transition whose destination has first counter zero gives an
even second counter. -/
private theorem next_zero_even (s : BB429.State) (w : Nat)
    (h : BB429.next s=some (0,w)) : w%2=0 := by
  rcases s with ⟨u,v⟩
  simp only [BB429.next] at h
  split at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              omega
            · split at h
              · simp at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                omega
          · split at h
            · simp at h
            · split at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                omega
              · split at h
                · split at h
                  · simp at h
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    omega
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  omega

/-- Blank-root runs can only visit even second counters at exact first
counter zero. -/
private theorem blank_zero_row_even (n w : Nat)
    (h : BB429.run n (0,0)=some (0,w)) : w%2=0 := by
  let P : BB429.State → Prop := fun s => s.1=0 → s.2%2=0
  have hroot : P (0,0) := by simp [P]
  have hstep : ∀ s t, P s → BB429.next s=some t → P t := by
    intro s t _ ht
    intro hzero
    cases t with
    | mk u' w' =>
      simp at hzero
      subst u'
      exact next_zero_even s w' ht
  have hp := invariant_of_run P hstep n (0,0) (0,w) h hroot
  exact hp rfl

/-- The first two-burst synthetic family always starts at an odd counter. -/
theorem demand_one_is_odd (q : Nat) (hq : 1≤q) :
    Agent6TwoBurstOne.demand (q-1)%2=1 := by
  have h := demand_one_relation q hq
  omega

/-- Consequently no member of the odd W1 source family is a blank-root
reachable state with first counter zero. -/
theorem no_blank_root_reaches_family_one (q : Nat) (hq : 1≤q) (n : Nat) :
    BB429.run n (0,0) ≠ some (0,Agent6TwoBurstOne.demand (q-1)) := by
  intro h
  have heven := blank_zero_row_even n (Agent6TwoBurstOne.demand (q-1)) h
  have hodd := demand_one_is_odd q hq
  omega

#print axioms synthetic_halt_every_three_power
#print axioms no_three_power_periodic_invariant
#print axioms no_three_power_cylinder_invariant
#print axioms no_blank_root_reaches_family_one

end Agent6ThreeAdic
