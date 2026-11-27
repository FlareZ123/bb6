import BB429CoarseExitExtended

namespace BB429.CoarseExit

/-- Exact base-four encoding of the ordinary two-step word. -/
def word4 (e : Nat → Bool) : Nat → Int
  | 0 => 0
  | i+1 => 4*word4 e i+(if e i then 1 else 0)

theorem lead_word4 (r a : Int) (e : Nat → Bool) (i : Nat) :
    lead r a e i=4^i*a-2*r*word4 e i := by
  induction i with
  | zero => simp [lead,word4]
  | succ i ih =>
    simp only [lead,word4,ih,Int.pow_succ]
    cases h : e i <;> simp [h] <;> grind +ring

theorem word4_bound (e : Nat → Bool) (i : Nat) :
    0≤word4 e i ∧ 3*word4 e i+1≤4^i := by
  induction i with
  | zero => simp [word4]
  | succ i ih =>
    simp only [word4,Int.pow_succ]
    cases h : e i <;> simp [h] <;> omega

theorem word4_last (e : Nat → Bool) (i : Nat) : word4 e i%4=0 ∨ word4 e i%4=1 := by
  cases i with
  | zero => simp [word4]
  | succ i => simp only [word4]; cases h : e i <;> simp [h] <;> omega

theorem word4_complement (e : Nat → Bool) (i : Nat) :
    3*(word4 e i+word4 (fun k=> !e k) i)+1=4^i := by
  induction i with
  | zero => simp [word4]
  | succ i ih => simp only [word4,Int.pow_succ]; by_cases h : e i=true <;> simp [h] <;> omega

/-- A surviving low-side prefix can land on leading zero only for the
    sparse Cantor-type deviations 18+216*C, C a base-four 0/1 integer. -/
theorem lead_zero_resonance (s : Nat) (d : Int) (e : Nat → Bool) (hd : d%4=2)
    (hz : lead (lowR s) (lowA s d) e (2*s+2)=0) :
    e (2*s)=true ∧ e (2*s+1)=false ∧ d=18+216*word4 (fun k=> !e k) (2*s) := by
  have hpow : (4:Int)^(2*s+2)=16*(16:Int)^s := by
    rw [Int.pow_add,Int.pow_mul]
    change (16:Int)^s*16=16*(16:Int)^s
    exact Int.mul_comm _ _
  have h := lead_word4 (lowR s) (lowA s d) e (2*s+2)
  rw [hz,hpow] at h
  have hfact : 0=(16:Int)^s*(16*lowA s d-432*word4 e (2*s+2)) := by
    unfold lowR at h
    grind +ring
  have hpos : 0<(16:Int)^s := Int.pow_pos (by decide)
  have h0 : 16*lowA s d=432*word4 e (2*s+2) := by
    have hh : 16*lowA s d-432*word4 e (2*s+2)=0 := (Int.mul_eq_zero.mp hfact.symm).resolve_left (by omega)
    omega
  have hA : lowA s d%8=4 := by unfold lowA; omega
  have hf : e (2*s+1)=false := by
    by_cases he : e (2*s+1)=true
    · have hw : word4 e (2*s+2)=4*word4 e (2*s+1)+1 := by rw [show 2*s+2=(2*s+1)+1 by omega,word4,he]; simp
      omega
    · exact Bool.eq_false_iff.mpr he
  have ht : e (2*s)=true := by
    by_cases he : e (2*s)=false
    · have hw : word4 e (2*s+2)=16*word4 e (2*s) := by rw [show 2*s+2=(2*s+1)+1 by omega,word4,hf,word4,he]; simp; omega
      omega
    · cases h : e (2*s)
      · exact False.elim (he h)
      · rfl
  have hw : word4 e (2*s+2)=16*word4 e (2*s)+4 := by rw [show 2*s+2=(2*s+1)+1 by omega,word4,hf,word4,ht]; simp; omega
  have hc := word4_complement e (2*s)
  rw [Int.pow_mul] at hc
  change 3*(word4 e (2*s)+word4 (fun k=> !e k) (2*s))+1=(16:Int)^s at hc
  refine ⟨ht,hf,?_⟩
  unfold lowA at h0
  omega

theorem return_nonresonant (p : State) (s : Nat) (d P x y : Int)
    (hodd : p.2%2=1) (hph : phaseOf p=true) (hr : 360≤Vc p)
    (hd : 0<d) (hd4 : d%4=2) (hres : ∀ e : Nat → Bool, d≠18+216*word4 e (2*s)) (hx : 0≤x) (hy : 153<y)
    (hdef : defect x y=-18)
    (hU : Uc p=lowA s d*P+x) (hV : Vc p=lowR s*P+y)
    (hsep : 3*cap (budget x y (lowL s)) (lowL s)+39<P)
    (n : Nat) (hbound : (4:Int)^n>lowR s*P+y+42*(lowL s+n)+72) :
    ∃ k t, 0<k ∧ k≤2*(lowL s+n) ∧ run k p=some t ∧ isSection t := by
  classical
  by_cases hex : ∃ k t, 0<k ∧ k≤2*lowL s ∧ run k p=some t ∧ isSection t
  · obtain ⟨k,t,hk,hkn,hrun,hs⟩ := hex
    exact ⟨k,t,hk,by omega,hrun,hs⟩
  · let N := 2*lowL s
    have hg : good p N := by
      rcases positive_prefix_or_return p P (lowR s) (lowA s d) x y (lowL s) hodd hx hy hU hV hph hdef hsep with h|h
      · exact False.elim (hex h)
      · exact h
    have hav : avoid p N := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,hkN,hg k hkN,hs⟩
    obtain ⟨ho,e,hb⟩ := tracePhasePrefix p (lowL s) N hodd hg hav (by omega)
    let U := fun i => Uc (trace p (2*i))
    let V := fun i => Vc (trace p (2*i))
    let ph := fun i => phaseOf (trace p (2*i))
    let i := 2*s+2
    have hU' : U 0=lowA s d*P+x := by simpa [U,trace,run] using hU
    have hV' : V 0=lowR s*P+y := by simpa [V,trace,run] using hV
    have hph' : ph 0=true := by simpa [ph,trace,run] using hph
    have hphys : Physical U V (lowL s) := by intro j hj; simp [U,V,Uc,Vc]; omega
    have hmid := lead_middle s d P x y U V e hx (by omega) hU' hV' (phase_blocks_weaken U V e ph _ hb) hphys hsep
    have hlead : 3*lead (lowR s) (lowA s d) e i=2*lowR s := by
      rcases hmid with h|h
      · have hreson := lead_zero_resonance s d e hd4 h.1
        exact False.elim (hres _ hreson.2.2)
      · exact h.1
    have hseen : ∃ j, j<i ∧ e j=false := by
      by_cases h : ∃ j, j<i ∧ e j=false
      · exact h
      · exfalso
        have hall : ∀ j, j<i → e j=true := by
          intro j hj
          cases he : e j
          · exact False.elim (h ⟨j,hj,he⟩)
          · rfl
        have ha : 3*lowA s d<2*lowR s := by simp [lowA,lowR]; omega
        have hh := lead_all_true_below (lowR s) (lowA s d) e i ha hall
        omega
    have he := error_strict_after_F P (lowR s) (lowA s d) x y (lowL s) U V e ph (by omega) hU' hV' hph' hdef hb i (by dsimp [i,lowL]; omega) hseen
    have hmul := congrArg (fun q : Int => q*P) hlead
    simp only [Int.mul_assoc] at hmul
    have hgap : 0<corridorGap (trace p (2*i)) := by
      unfold defect at he
      change phaseDefect (ph i)<3*(U i-lead (lowR s) (lowA s d) e i*P)-2*(V i-lowR s*P) at he
      unfold corridorGap defect
      change 0<3*U i-2*V i-phaseDefect (ph i)
      omega
    have hv := error_corridor P (lowR s) (lowA s d) x y (lowL s) U V e ph (by omega) hU' hV' hph' hdef hb i (by dsimp [i,lowL]; omega)
    have hr' : 360≤Vc (trace p (2*i)) := by change 360≤V i; omega
    have hoi := ho i (by dsimp [i,lowL]; omega)
    have herr := errors P (lowR s) (lowA s d) x y (lowL s) (lowL s) U V e hx (by omega) (by omega) hU' hV' (phase_blocks_weaken U V e ph _ hb) i (by dsimp [i,lowL]; omega)
    have hm : (4:Int)^n≤4^n*corridorGap (trace p (2*i)) := by
      have hh := Int.mul_le_mul_of_nonneg_left (show 1≤corridorGap (trace p (2*i)) by omega) (show 0≤(4:Int)^n from Int.pow_nonneg (by decide))
      simpa using hh
    have hbig : (4:Int)^n*corridorGap (trace p (2*i))>Vc (trace p (2*i))+42*n+72 := by
      change (4:Int)^n*corridorGap (trace p (2*i))>V i+42*n+72
      have hi : i≤lowL s := by dsimp [i,lowL]; omega
      push_cast at hbound
      omega
    obtain ⟨k,t,hk,hkn,hrun,hs⟩ := above_return (trace p (2*i)) hoi hr' hgap n hbig
    refine ⟨2*i+k,t,by omega,by dsimp [i,lowL]; omega,?_,hs⟩
    rw [run_add,hg (2*i) (by dsimp [N,i,lowL]; omega),Option.bind_some,hrun]

/-- Quantitative original prepared-section result: at most 12m+31
    accelerator steps for all separated deviations except 18 modulo 27. -/
theorem prepared_nonresonant (s j d u : Nat) (hd : 6≤d) (hp : d%4=2)
    (hres : ∀ e : Nat → Bool, (d:Int)≠18+216*word4 e (2*s)) (hj : 2≤j) (hdsmall : d≤16^s)
    (hc : 3*(24*16^(j+s)-3)+d+24*j=3*u+d*16^j)
    (hg : 5*(d*16^j)+7≤u)
    (hsep : 3*cap (budget (lowX d j) (lowY d j) (lowL s)) (lowL s)+39<(16:Int)^j) :
    ∃ k t, 0<k ∧ k≤12*(j+s)+31 ∧ run k (prepared (j+s) d)=some t ∧ isSection t := by
  obtain ⟨hr,ho,hu,hv⟩ := prepared_phase s j d u hd hp hc hg
  let p := LowReturnBand.phase u (d*16^j)
  have hph : phaseOf p=true := by
    simp [p,phaseOf,LowReturnBand.phase]
    have hX : 1≤16^(j+s) := Nat.pow_pos (by decide)
    omega
  have hD : d≤d*16^j := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  have hRank : 360≤Vc p := by
    have hW : 55≤u+12+d*16^j := by omega
    have hU : 37≤u := by omega
    change 360≤6*(u:Int)+3*((u+12+d*16^j:Nat):Int)
    omega
  have hx : 0≤lowX d j := by simp [lowX]; omega
  have hy : 153<lowY d j := by simp [lowY]; omega
  have hdef : defect (lowX d j) (lowY d j)=-18 := by simp [defect,lowX,lowY]; omega
  let n := 2*(j+s)+8
  have hX : (16:Int)^(j+s)=(16:Int)^j*(16:Int)^s := Int.pow_add _ _ _
  have hPow : (4:Int)^n=65536*(16:Int)^(j+s) := by
    dsimp [n]
    rw [Int.pow_add,Int.pow_mul]
    change (16:Int)^(j+s)*65536=65536*(16:Int)^(j+s)
    exact Int.mul_comm _ _
  have hScale : (16:Int)*(↑j+↑s)≤(16:Int)^(j+s) := by
    have h := scale_ge (j+s)
    exact_mod_cast h
  have hD' : (d:Int)≤(16:Int)^(j+s) := by
    have hh : (16:Int)^s≤(16:Int)^j*(16:Int)^s := by
      have hjp : (1:Int)≤(16:Int)^j := by have hh := Int.pow_pos (m:=j) (show (0:Int)<16 by decide); omega
      have hh := Int.mul_le_mul_of_nonneg_right hjp (show 0≤(16:Int)^s from Int.pow_nonneg (by decide))
      simpa using hh
    have hd' : (d:Int)≤(16:Int)^s := by exact_mod_cast hdsmall
    omega
  have hOne : (1:Int)≤(16:Int)^(j+s) := by have h := Int.pow_pos (m:=j+s) (show (0:Int)<16 by decide); omega
  have hRP : lowR s*(16:Int)^j=216*(16:Int)^(j+s) := by
    unfold lowR
    rw [hX]
    grind +ring
  have hbound : (4:Int)^n>lowR s*(16:Int)^j+lowY d j+42*(lowL s+n)+72 := by
    rw [hPow,hRP]
    simp [lowY,lowL,n]
    omega
  obtain ⟨k,t,hk,hkn,ht,hs⟩ := return_nonresonant p s d ((16:Int)^j) (lowX d j) (lowY d j) ho hph hRank (by omega) (by omega) hres hx hy hdef hu hv hsep n hbound
  refine ⟨4*(j+s)+3+4*j+k,t,by omega,by dsimp [lowL,n] at hkn; omega,?_,hs⟩
  rw [run_add,hr,Option.bind_some]
  exact ht



/-- When a new large F burst starts from exact U=aP, the low-order U
    correction is nonpositive throughout all subsequent ordinary blocks. -/
theorem negative_error (P r a y : Int) (n : Nat) (U V : Nat → Int) (e ph : Nat → Bool)
    (hy : 27≤y) (hU : U 0=a*P) (hV : V 0=r*P+y)
    (hs : PhaseBlocks U V e ph n) :
    ∀ i, i≤n → U i-lead r a e i*P≤0 ∧ y≤V i-r*P := by
  intro i hi
  induction i with
  | zero => simp [lead,hU,hV]; omega
  | succ i ih =>
    obtain ⟨he,hv⟩ := ih (by omega)
    obtain ⟨_,hu,hv'⟩ := hs i (by omega)
    simp only [lead,hu,hv']
    cases h : e i <;> cases hph : ph i <;> simp [h,hph,Int.sub_mul,Int.mul_assoc] <;> omega

theorem negative_no_halt (P r a y : Int) (L n : Nat) (U V : Nat → Int) (e ph : Nat → Bool)
    (hy : 27≤y) (hn : n≤L) (hU : U 0=a*P) (hV : V 0=r*P+y)
    (hs : PhaseBlocks U V e ph n) (hsep : 3*cap (budget 0 y L) L+39<P) : 2*U n≠V n+39 := by
  intro hh
  have h := leading_halt P r a 0 y L n U V e (by decide) (by omega) hn (by simpa using hU) hV
    (phase_blocks_weaken U V e ph n hs) hsep hh
  have he := negative_error P r a y n U V e ph hy hU hV hs n (by omega)
  have hm := congrArg (fun z : Int=>z*P) h
  simp only [Int.mul_assoc] at hm
  omega
theorem negative_prefix_or_return (p : State) (P r a y : Int) (L : Nat)
    (hodd : p.2%2=1) (hy : 27≤y)
    (hU : Uc p=a*P) (hV : Vc p=r*P+y)
    (hsep : 3*cap (budget 0 y L) L+39<P) :
    (∃ k t, 0<k ∧ k≤2*L ∧ run k p=some t ∧ isSection t) ∨ good p (2*L) := by
  classical
  by_cases hex : ∃ k t, 0<k ∧ k≤2*L ∧ run k p=some t ∧ isSection t
  · exact Or.inl hex
  · right
    have avoidGood (N : Nat) (hN : N≤2*L) (hg : good p N) : avoid p N := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,by omega,hg k hkN,hs⟩
    have full (n : Nat) (hn : n≤L) : good p (2*n) := by
      induction n with
      | zero => exact good_zero p
      | succ n ih =>
        have hg := ih (by omega)
        have ⟨ho,e,hb⟩ := tracePhasePrefix p n (2*n) hodd hg (avoidGood _ (by omega) hg) (by omega)
        have hno := negative_no_halt P r a y L n (fun i => Uc (trace p (2*i))) (fun i => Vc (trace p (2*i))) e (fun i => phaseOf (trace p (2*i))) hy (by omega)
          (by simpa [trace,run] using hU) (by simpa [trace,run] using hV) hb hsep
        have hnext : next (trace p (2*n))≠none := fun h => hno (halt_equation _ h)
        have hg1 := good_next p (2*n) hg hnext
        have hev := next_odd_to_even _ _ (good_step p (2*n+1) (2*n) hg1 (by omega)) (ho n (by omega)) (avoidGood _ (by omega) hg1 _ (by omega) (by omega))
        have hnext1 : next (trace p (2*n+1))≠none := by
          intro h
          have hh := halt_equation _ h
          simp only [Uc,Vc] at hh
          omega
        have hg2 := good_next p (2*n+1) hg1 hnext1
        simpa only [show 2*n+1+1=2*(n+1) by omega] using hg2
    exact full L (by omega)


/-- A second separated burst from exact U=aP cannot survive the short
    prefix if its coefficient avoids the exact base-four resonance. -/
theorem return_from_exact_burst (p : State) (I : Nat) (a P y : Int)
    (hodd : p.2%2=1) (hy : 27≤y) (hU : Uc p=a*P)
    (hV : Vc p=(27*4^I)*P+y)
    (hsep : 3*cap (budget 0 y (I+4)) (I+4)+39<P)
    (hres : ∀ e : Nat → Bool, a≠18+54*word4 e I) :
    ∃ k t, 0<k ∧ k≤2*(I+4) ∧ run k p=some t ∧ isSection t := by
  classical
  let L := I+4
  let r : Int := 27*4^I
  by_cases hex : ∃ k t, 0<k ∧ k≤2*L ∧ run k p=some t ∧ isSection t
  · exact hex
  · exfalso
    have hg : good p (2*L) := by
      rcases negative_prefix_or_return p P r a y L hodd hy hU hV hsep with h|h
      · exact False.elim (hex h)
      · exact h
    have hav : avoid p (2*L) := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,hkN,hg k hkN,hs⟩
    obtain ⟨_,e,hb⟩ := tracePhasePrefix p L (2*L) hodd hg hav (by omega)
    let U := fun i => Uc (trace p (2*i))
    let V := fun i => Vc (trace p (2*i))
    let ph := fun i => phaseOf (trace p (2*i))
    have hU' : U 0=a*P := by simpa [U,trace,run] using hU
    have hV' : V 0=r*P+y := by simpa [V,trace,run] using hV
    have hphys : Physical U V L := by intro j hj; simp [U,V,Uc,Vc]; omega
    have hB := leading_bounds P r a 0 y L L U V e (by decide) (by omega) (by omega) (by simpa using hU') hV'
      (phase_blocks_weaken U V e ph L hb) hphys hsep
    have hH : 0<(4:Int)^I := Int.pow_pos (by decide)
    have hZ : lead r a e I=(4:Int)^I*(a-54*word4 e I) := by
      rw [lead_word4]; dsimp [r]; grind +ring
    have h := four_scaled ((4:Int)^I) r a e I (a-54*word4 e I) hH rfl hZ hB
    rcases h with h|h
    · rw [h,Int.mul_zero] at hZ
      have he := negative_error P r a y L U V e ph hy hU' hV' hb I (by dsimp [L]; omega)
      have hp := hphys I (by dsimp [L]; omega)
      rw [hZ,Int.zero_mul,Int.sub_zero] at he
      omega
    · exact hres e (by omega)

theorem exact_burst_mod24 (a : Int) (I : Nat) (ha : a%24=12) : ∀ e : Nat → Bool, a≠18+54*word4 e I := by
  intro e h
  have hw := word4_last e I
  omega


/-- The first Cantor resonance d=18 reaches an exact small-U state. -/
theorem d18_small (m : Nat) (hm : 2≤m) :
    run (8*m+4) (prepared m 18)=some (4*m+3,72*16^m+16*m+26) := by
  obtain ⟨n,rfl⟩ : ∃ n : Nat, m=n+1 := ⟨m-1,by omega⟩
  let P := 16^n
  let u := 378*P+8*n+3
  have hP : 1≤P := Nat.pow_pos (by decide)
  have hX : 16^(n+1)=16*P := by rw [Nat.pow_succ,Nat.mul_comm]
  have hcoord : 3*(24*16^(n+1)-3)+18+24*n=3*u+18*16^n := by rw [hX]; dsimp [u,P]; omega
  have hguard : 5*(18*16^n)+7≤u := by dsimp [u,P]; omega
  have hphase : (24*16^(n+1)-3+1)%4=18%4 := by omega
  obtain ⟨hc,hmod,heven⟩ := LowReturnBand.cycles n (24*16^(n+1)-3) 18 u (by decide) (by decide) hphase hcoord hguard
  have hfirst : run (4*(n+1)+3+4*n) (prepared (n+1) 18)=some (LowReturnBand.phase u (18*16^n)) := by
    rw [run_add,prepared_burst,Option.bind_some,hc]
  have hD : 6≤18*16^n := by change 6≤18*P; omega
  have hcycle := LowReturnBand.cycle u (18*16^n) hD heven hmod hguard
  have hu : u+8-5*(18*16^n)=18*16^(n+1)+8*(n+1)+3 := by rw [hX]; dsimp [u,P]; omega
  rw [hu] at hcycle
  have hD' : 16*(18*16^n)=18*16^(n+1) := by rw [hX]; dsimp [P]; omega
  rw [hD'] at hcycle
  let v := 18*16^(n+1)+8*(n+1)+3
  let w := 36*16^(n+1)+8*(n+1)+15
  have hs : LowReturnBand.phase v (18*16^(n+1))=(v,w) := by simp [LowReturnBand.phase,v,w]; omega
  change run 4 (LowReturnBand.phase u (18*16^n))=some (LowReturnBand.phase v (18*16^(n+1))) at hcycle
  rw [hs] at hcycle
  have hnext : next (v,w)=some (4*(n+1)+3,72*16^(n+1)+16*(n+1)+26) := by
    simp only [next]
    repeat' split
    all_goals simp_all [v,w]
    all_goals omega
  rw [show 8*(n+1)+4=(4*(n+1)+3+4*n)+4+1 by omega,run_add,run_add,hfirst,Option.bind_some,hcycle,Option.bind_some]
  simp [run,hnext]

/-- For d=18 the second F-burst leading coefficient is 24m+36,
    excluded from the base-four resonance by its residue 12 modulo 24. -/
theorem d18_second_return (s j : Nat) (hm : 2≤j+s)
    (hbudget : 2*((4*(j+s)+6)*2^(4*j+1)-3)≤72*16^(j+s)+24*(j+s)+32+3*(4*j+1))
    (hsep : 3*cap (budget 0 (72*((j+s:Nat):Int)+96+9*((4*j+1:Nat):Int)) (2*s+5)) (2*s+5)+39<(2:Int)^(4*j+1)) :
    ∃ k t, 0<k ∧ k≤12*(j+s)+15 ∧ run k (prepared (j+s) 18)=some t ∧ isSection t := by
  let m := j+s
  let K := 4*j+1
  let I := 2*s+1
  let P := 2^K
  let u := (4*m+6)*P-3
  let w := 72*16^m+24*m+32+3*K-2*u
  let a : Int := 24*(m:Int)+36
  let y : Int := 72*(m:Int)+96+9*(K:Int)
  have hP : 1≤P := Nat.pow_pos (by decide)
  have hU : u+3=(4*m+6)*P := by
    have h := Nat.le_mul_of_pos_right (4*m+6) (by omega : 0<P)
    dsimp [u]; omega
  have hr : 2*u+w=72*16^m+24*m+32+3*K := by dsimp [w]; dsimp [m,K,u,P] at *; omega
  have hfirst := d18_small m hm
  have hburst : run K (4*m+3,72*16^m+16*m+26)=some (u,w) := by
    apply LowReturnBand.section_burst
    · simpa [P] using hU
    · omega
  have hp : w%2=1 := by dsimp [K] at hr; omega
  have hUc : Uc (u,w)=a*(P:Int) := by
    have h := congrArg (fun z : Nat => (z:Int)) hU
    simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at h
    simp [Uc,a]; grind +ring
  have hV : Vc (u,w)=(27*4^I)*(P:Int)+y := by
    have h := congrArg (fun z : Nat => (z:Int)) hr
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int] at h
    have hpow : (27:Int)*4^I*(P:Int)=216*16^m := by
      dsimp [I,P,K,m]
      push_cast
      rw [Int.pow_add (4:Int) (2*s) 1,Int.pow_mul,Int.pow_add (2:Int) (4*j) 1,Int.pow_mul,Int.pow_add]
      change 27*((16:Int)^s*4)*((16:Int)^j*2)=216*((16:Int)^j*(16:Int)^s)
      grind +ring
    rw [hpow]
    simp [Vc,y]; omega
  have ha : a%24=12 := by simp [a]
  have hsep' : 3*cap (budget 0 y (I+4)) (I+4)+39<(P:Int) := by
    dsimp [I,P,K,y,m]; push_cast; exact hsep
  obtain ⟨k,t,hk,hkn,ht,hs⟩ := return_from_exact_burst (u,w) I a P y hp (by simp [y]; omega) hUc hV hsep' (exact_burst_mod24 a I ha)
  refine ⟨8*m+4+K+k,t,by omega,by dsimp [m,K,I] at *; omega,?_,hs⟩
  rw [run_add,run_add,hfirst,Option.bind_some,hburst,Option.bind_some,ht]


theorem cap_eq (B : Int) (n : Nat) : cap B n=5^n*B := by
  induction n with
  | zero => simp [cap]
  | succ n ih => rw [cap,ih,Int.pow_succ]; grind +ring

theorem d18_growth (s : Nat) (hs : 4≤s) : (9375:Int)*(1000*s+3000)+40≤128^s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases h : 4≤s
    · have hh := ih h
      rw [Int.pow_succ,Int.natCast_succ]
      omega
    · have he : s=3 := by omega
      subst s
      decide

private theorem pow_compare (s : Nat) : (3200:Int)^s≤4096^s := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [Int.pow_succ,Int.pow_succ]
    have hp : 0≤(4096:Int)^s := Int.pow_nonneg (by decide)
    omega

theorem d18_large (s t : Nat) (hs : 4≤s) (ht : t<4) :
    ∃ k p, 0<k ∧ k≤12*(4*s+t)+15 ∧ run k (prepared (4*s+t) 18)=some p ∧ isSection p := by
  let j := 3*s+t
  have hX : 16^(j+s)=16^j*16^s := Nat.pow_add ..
  have hP : 2^(4*j+1)=16^j*2 := by rw [Nat.pow_add,Nat.pow_mul]
  have hbound : 4*(4*(j+s)+6)≤72*16^s := by
    have hh := scale_ge s
    dsimp [j]; omega
  have hb : 2*((4*(j+s)+6)*2^(4*j+1)-3)≤72*16^(j+s)+24*(j+s)+32+3*(4*j+1) := by
    have hh := Nat.mul_le_mul_right (16^j) hbound
    rw [hP,hX]
    calc
      2*((4*(j+s)+6)*(16^j*2)-3) ≤ 4*(4*(j+s)+6)*16^j := by
        have hh' : 2*((4*(j+s)+6)*(16^j*2))=4*(4*(j+s)+6)*16^j := by grind +ring
        omega
      _ ≤ 72*16^(j+s) := by rw [hX]; simpa [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hh
      _ ≤ 72*(16^j*16^s)+24*(j+s)+32+3*(4*j+1) := by rw [hX]; omega
  let L := 2*s+5
  let y : Int := 72*((j+s:Nat):Int)+96+9*((4*j+1:Nat):Int)
  have hB : budget 0 y L≤1000*(s:Int)+3000 := by
    simp [budget,y,L,j]; omega
  have h25 : 1≤(25:Int)^s := by have hh := Int.pow_pos (m:=s) (show (0:Int)<25 by decide); omega
  have h5 : (5:Int)^L=3125*25^s := by
    dsimp [L]; rw [Int.pow_add,Int.pow_mul]; change (25:Int)^s*3125=3125*25^s; exact Int.mul_comm ..
  have hcap : 3*cap (budget 0 y L) L+39≤128^s*25^s := by
    rw [cap_eq,h5]
    have hh := Int.mul_le_mul_of_nonneg_right hB (show 0≤(25:Int)^s by omega)
    have hh' := Int.mul_le_mul_of_nonneg_right (d18_growth s hs) (show 0≤(25:Int)^s by omega)
    have hmul : (25:Int)^s*budget 0 y L=budget 0 y L*25^s := Int.mul_comm ..
    have hdist : ((9375:Int)*(1000*s+3000)+40)*25^s=9375*((1000*s+3000)*25^s)+40*25^s := by grind +ring
    have hgoal : 3*(3125*25^s*budget 0 y L)=9375*((25:Int)^s*budget 0 y L) := by grind +ring
    rw [hdist] at hh'
    rw [hgoal,hmul]
    have haux : (40:Int)≤40*25^s := by omega
    omega
  have hbig : (128:Int)^s*25^s≤16^j := by
    rw [←Int.mul_pow]
    change (3200:Int)^s≤16^j
    have h1 := pow_compare s
    have h2 : (4096:Int)^s≤16^j := by
      dsimp [j]; rw [Int.pow_add,Int.pow_mul]
      change (4096:Int)^s≤4096^s*16^t
      have hp : 1≤(16:Int)^t := by have hh := Int.pow_pos (m:=t) (show (0:Int)<16 by decide); omega
      have hh := Int.mul_le_mul_of_nonneg_left hp (show 0≤(4096:Int)^s from Int.pow_nonneg (by decide))
      rw [Int.mul_one] at hh
      exact hh
    omega
  have hsep : 3*cap (budget 0 y L) L+39<(2:Int)^(4*j+1) := by
    rw [Int.pow_add,Int.pow_mul]
    change 3*cap (budget 0 y L) L+39<(16:Int)^j*2
    have hp : 0<(16:Int)^j := Int.pow_pos (by decide)
    omega
  obtain ⟨k,p,hk,hkn,hr,hs'⟩ := d18_second_return s j (by dsimp [j]; omega) hb hsep
  have hm : j+s=4*s+t := by dsimp [j]; omega
  rw [hm] at hkn hr
  exact ⟨k,p,hk,hkn,hr,hs'⟩


set_option maxRecDepth 20000 in
/-- Every scale of the smallest resonance d=18 is safe until section return.
    The uniform large-scale proof uses no search. Sixteen small cases use
    explicit witnesses checked by kernel reduction of the source map. -/
theorem d18_all (m : Nat) :
    ∃ k p, 0<k ∧ k≤12*m+15 ∧ run k (prepared m 18)=some p ∧ isSection p := by
  by_cases hm : 16≤m
  · have h := d18_large (m/4) (m%4) (by omega) (by omega)
    have he : 4*(m/4)+m%4=m := by omega
    simpa only [he] using h
  · have cases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6 ∨ m=7 ∨ m=8 ∨ m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨5,(11,94),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨12,(11,1198),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨20,(11,18490),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨43,(0,295072),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨53,(11,4718766),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨65,(11,75497682),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨77,(11,1207959798),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨89,(11,19327353114),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨105,(11,309237645650),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨115,(0,4947802325372),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨131,(0,79164837200308),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨139,(0,1266637395198408),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨151,(0,20266198323167724),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨161,(11,324259173170676218),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨173,(11,5188146770730811934),by decide,by decide,by decide,by simp [isSection]⟩
    · exact ⟨185,(11,83010348331692982850),by decide,by decide,by decide,by simp [isSection]⟩

#print axioms lead_zero_resonance
#print axioms prepared_nonresonant
#print axioms return_from_exact_burst
#print axioms d18_all
end BB429.CoarseExit
