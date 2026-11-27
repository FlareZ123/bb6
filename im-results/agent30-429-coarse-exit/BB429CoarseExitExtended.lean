import BB429CoarseExitSource
import BB429LowReturnBand

namespace BB429.CoarseExit

open BB429.LowReturnBand

def prepared (m d : Nat) : State := (0,72*16^m+d-(12*m+6))
def lowX (d j : Nat) : Int := 2*(d:Int)+48*j
def lowY (d j : Nat) : Int := 3*(d:Int)+9+72*j

theorem scale_ge (m : Nat) : 16*m≤16^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.pow_succ]
    have h : 0<16^m := Nat.pow_pos (by decide)
    omega

theorem prepared_burst (m d : Nat) : run (4*m+3) (prepared m d)=some (phase (24*16^m-3) d) := by
  have hX := scale_ge m
  have hx : 1≤16^m := Nat.pow_pos (by decide)
  apply zero_burst
  · rw [show 4*m+3=4*m+3 by rfl,Nat.pow_add,Nat.pow_mul]
    change 24*16^m-3+3=3*(16^m*8)
    omega
  · omega

theorem prepared_phase (s j d u : Nat) (hd : 6≤d) (hp : d%4=2)
    (hc : 3*(24*16^(j+s)-3)+d+24*j=3*u+d*16^j)
    (hg : 5*(d*16^j)+7≤u) :
    run (4*(j+s)+3+4*j) (prepared (j+s) d)=some (phase u (d*16^j)) ∧
    (phase u (d*16^j)).2%2=1 ∧
    Uc (phase u (d*16^j))=lowA s d*(16:Int)^j+lowX d j ∧
    Vc (phase u (d*16^j))=lowR s*(16:Int)^j+lowY d j := by
  have hX : 1≤16^(j+s) := Nat.pow_pos (by decide)
  have hm : (24*16^(j+s)-3+1)%4=d%4 := by omega
  obtain ⟨hr,hm',he'⟩ := cycles j (24*16^(j+s)-3) d u hd (by omega) hm hc hg
  have hcast : (3:Int)*(24*(16:Int)^(j+s)-3)+d+24*j=3*(u:Int)+d*(16:Int)^j := by
    have hh : 3*(24*16^(j+s)-3)+d+24*j=3*u+d*16^j := hc
    have hh' := congrArg (fun k : Nat => (k:Int)) hh
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.natCast_sub (show 3≤24*16^(j+s) by omega),Int.cast_ofNat_Int] at hh'
    exact hh'
  rw [Int.pow_add] at hcast
  refine ⟨?_,?_,?_,?_⟩
  · rw [run_add,prepared_burst,Option.bind_some,hr]
  · simp [phase]; omega
  · simp [Uc,phase,lowA,lowX,Int.mul_sub,Int.mul_add,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] at hcast ⊢
    grind +ring
  · simp [Vc,phase,lowR,lowY,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm,Int.mul_add] at hcast ⊢
    grind +ring

theorem prepared_safe_return (s j d u : Nat) (hd : 6≤d) (hp : d%4=2)
    (hd0 : d%27≠0) (hd18 : d%27≠18)
    (hc : 3*(24*16^(j+s)-3)+d+24*j=3*u+d*16^j)
    (hg : 5*(d*16^j)+7≤u)
    (hsep : 3*cap (budget (lowX d j) (lowY d j) (lowL s)) (lowL s)+39<(16:Int)^j) :
    ∃ k t, 0<k ∧ k≤8*(j+s)+15 ∧ run k (prepared (j+s) d)=some t ∧ isSection t := by
  obtain ⟨hr,ho,hu,hv⟩ := prepared_phase s j d u hd hp hc hg
  obtain ⟨k,t,hk,hk',ht,hs⟩ := return_from_separated (phase u (d*16^j)) s d ((16:Int)^j) (lowX d j) (lowY d j) ho (by omega) (by omega) (by simp [lowX]; omega) (by simp [lowY]; omega) hu hv hsep
  refine ⟨4*(j+s)+3+4*j+k,t,by omega,by unfold lowL at hk'; omega,?_,hs⟩
  rw [run_add,hr,Option.bind_some,ht]

#print axioms prepared_safe_return

def PhaseBlocks (U V : Nat → Int) (e : Nat → Bool) (phase : Nat → Bool) (n : Nat) : Prop :=
  ∀ i, i<n → phase (i+1)= !phase i ∧
    U (i+1)=4*U i-(if e i then 2*V i else 0)+(if e i then if phase i then 54 else 6 else 0) ∧
    V (i+1)=V i+(if e i then if phase i then 42 else 30 else 18)

theorem phase_blocks_weaken (U V : Nat → Int) (e phase : Nat → Bool) (n : Nat)
    (hs : PhaseBlocks U V e phase n) : Blocks U V e n := by
  intro i hi
  obtain ⟨_,hu,hv⟩ := hs i hi
  refine ⟨(if e i then if phase i then 54 else 6 else 0), (if e i then if phase i then 42 else 30 else 18),?_,?_,?_,?_,hu,hv⟩
  all_goals cases e i <;> cases phase i <;> decide

def defect (U V : Int) : Int := 3*U-2*V
def phaseDefect (b : Bool) : Int := if b then -18 else 6

/-- The exact low-order error starts on the alternating escape corridor and can
    only move to its positive side under any sequence of ordinary blocks. -/
theorem error_corridor (P r a x y : Int) (n : Nat) (U V : Nat → Int) (e phase : Nat → Bool)
    (hy : 27≤y) (hU : U 0=a*P+x) (hV : V 0=r*P+y)
    (hstart : phase 0=true) (hdef : defect x y=-18) (hs : PhaseBlocks U V e phase n) :
    ∀ i, i≤n → y≤V i-r*P ∧ phaseDefect (phase i)≤defect (U i-lead r a e i*P) (V i-r*P) := by
  intro i hi
  induction i with
  | zero => simp [hU,hV,lead,hstart,phaseDefect,defect] at *; omega
  | succ i ih =>
    have hprev := ih (by omega)
    obtain ⟨hp,hu,hv⟩ := hs i (by omega)
    simp only [lead,hu,hv,hp,defect,Int.sub_mul,Int.mul_assoc]
    unfold defect at hprev
    unfold phaseDefect at hprev ⊢
    cases he : e i <;> cases hph : phase i <;> simp [he,hph,Int.mul_assoc] at hu hv hprev ⊢ <;> omega

theorem no_halt_on_positive_error (P r a x y : Int) (L n : Nat) (U V : Nat → Int) (e phase : Nat → Bool)
    (hx : 0≤x) (hy : 153<y) (hn : n≤L)
    (hU : U 0=a*P+x) (hV : V 0=r*P+y)
    (hstart : phase 0=true) (hdef : defect x y=-18) (hs : PhaseBlocks U V e phase n)
    (hsep : 3*cap (budget x y L) L+39<P) : 2*U n≠V n+39 := by
  intro hh
  have hlead := leading_halt P r a x y L n U V e hx (by omega) hn hU hV (phase_blocks_weaken U V e phase n hs) hsep hh
  have herr := error_corridor P r a x y n U V e phase (by omega) hU hV hstart hdef hs n (by omega)
  have hm := congrArg (fun k : Int => k*P) hlead
  simp only [Int.mul_assoc] at hm
  unfold defect phaseDefect at herr
  cases hph : phase n <;> simp [hph] at herr <;> omega

#print axioms error_corridor
#print axioms no_halt_on_positive_error

def phaseOf (p : State) : Bool := decide ((2*p.1+p.2)%4=1)

theorem ordinary_odd_phase (p q : State) (h : next p=some q) (hp : p.2%2=1) (hq : ¬isSection q) :
    q.2%2=0 ∧ ((Uc q=2*Uc p ∧ Vc q=Vc p+9) ∨
      (phaseOf p=true ∧ Uc q=2*Uc p-Vc p+27 ∧ Vc q=Vc p+33) ∨
      (phaseOf p=false ∧ Uc q=2*Uc p-Vc p+3 ∧ Vc q=Vc p+21)) := by
  obtain ⟨u,w⟩ := p
  obtain ⟨v,z⟩ := q
  simp only [next] at h
  simp only [isSection] at hq
  repeat' split at h
  all_goals simp_all [Uc,Vc,phaseOf]
  all_goals omega

theorem phase_flip (p t : State) (hodd : p.2%2=1)
    (hr : Vc t=Vc p+18 ∨ Vc t=Vc p+42 ∨ Vc t=Vc p+30) : phaseOf t= !phaseOf p := by
  unfold phaseOf
  simp only [Vc] at hr
  rcases hr with h|h|h <;> by_cases hp : (2*p.1+p.2)%4=1 <;> simp [hp] <;> omega

theorem odd_block_phase (p q t : State) (h : next p=some q) (g : next q=some t)
    (hp : p.2%2=1) (hq : ¬isSection q) (ht : ¬isSection t) :
    t.2%2=1 ∧ phaseOf t= !phaseOf p ∧ ∃ e : Bool,
    Uc t=4*Uc p-(if e then 2*Vc p else 0)+(if e then if phaseOf p then 54 else 6 else 0) ∧
    Vc t=Vc p+(if e then if phaseOf p then 42 else 30 else 18) := by
  obtain ⟨he,hh⟩ := ordinary_odd_phase p q h hp hq
  obtain ⟨ho,hu,hv⟩ := ordinary_even q t g he ht
  refine ⟨ho,phase_flip p t hp (by rcases hh with h|h|h <;> omega),?_⟩
  rcases hh with h|h|h
  · exact ⟨false,by simp; omega,by simp; omega⟩
  · exact ⟨true,by simp [h.1]; omega,by simp [h.1]; omega⟩
  · exact ⟨true,by simp [h.1]; omega,by simp [h.1]; omega⟩

theorem tracePhasePrefix (p : State) (n N : Nat) (hodd : p.2%2=1) (hgood : good p (2*n))
    (hav : avoid p N) (hN : 2*n≤N) :
    (∀ i, i≤n → (trace p (2*i)).2%2=1) ∧
    ∃ e : Nat → Bool, PhaseBlocks (fun i => Uc (trace p (2*i))) (fun i => Vc (trace p (2*i))) e (fun i => phaseOf (trace p (2*i))) n := by
  obtain ⟨ho,_⟩ := tracePrefix p n N hodd hgood hav hN
  have pair (i : Nat) (hi : i<n) :=
    odd_block_phase (trace p (2*i)) (trace p (2*i+1)) (trace p (2*(i+1)))
      (good_step p (2*n) (2*i) hgood (by omega))
      (by have hh := good_step p (2*n) (2*i+1) hgood (by omega); simpa only [show 2*i+1+1=2*(i+1) by omega] using hh)
      (ho i (by omega)) (hav _ (by omega) (by omega)) (hav _ (by omega) (by omega))
  refine ⟨ho,?_⟩
  classical
  let e (i : Nat) : Bool := if hi : i<n then Classical.choose (pair i hi).2.2 else false
  refine ⟨e,?_⟩
  intro i hi
  exact ⟨(pair i hi).2.1,by simpa [e,hi] using Classical.choose_spec (pair i hi).2.2⟩

theorem positive_prefix_or_return (p : State) (P r a x y : Int) (L : Nat)
    (hodd : p.2%2=1) (hx : 0≤x) (hy : 153<y)
    (hU : Uc p=a*P+x) (hV : Vc p=r*P+y)
    (hstart : phaseOf p=true) (hdef : defect x y=-18)
    (hsep : 3*cap (budget x y L) L+39<P) :
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
        have hno := no_halt_on_positive_error P r a x y L n (fun i => Uc (trace p (2*i))) (fun i => Vc (trace p (2*i))) e (fun i => phaseOf (trace p (2*i))) hx hy (by omega)
          (by simpa [trace,run] using hU) (by simpa [trace,run] using hV) (by simpa [trace,run] using hstart) hdef hb hsep
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

def corridorGap (p : State) : Int := defect (Uc p) (Vc p)-phaseDefect (phaseOf p)

theorem above_no_halt (p : State) (h : 360≤Vc p) (hg : 0<corridorGap p) : next p≠none := by
  intro hh
  have he := halt_equation _ hh
  unfold corridorGap defect phaseDefect at hg
  cases hph : phaseOf p <;> simp [hph] at hg <;> omega

theorem above_block (p q t : State) (h : next p=some q) (g : next q=some t)
    (hp : p.2%2=1) (hq : ¬isSection q) (ht : ¬isSection t) (hr : 360≤Vc p) (hd : 0<corridorGap p) :
    t.2%2=1 ∧ corridorGap t=4*corridorGap p ∧ Vc p≤Vc t ∧ Vc t≤Vc p+42 := by
  obtain ⟨ho,hph,e,hu,hv⟩ := odd_block_phase p q t h g hp hq ht
  have hne : e=true := by
    cases e
    · simp at hu hv
      have hphys : Uc t≤Vc t+18 := by simp [Uc,Vc]; omega
      unfold corridorGap defect phaseDefect at hd
      cases h : phaseOf p <;> simp [h] at hd <;> omega
    · rfl
  refine ⟨ho,?_,?_,?_⟩
  · unfold corridorGap defect phaseDefect
    rw [hph]
    simp [hne] at hu hv
    cases h : phaseOf p <;> simp [h] at hu hv ⊢ <;> omega
  · cases h : phaseOf p <;> simp [hne,h] at hv <;> omega
  · cases h : phaseOf p <;> simp [hne,h] at hv <;> omega

theorem above_return (p : State) (hodd : p.2%2=1) (hr : 360≤Vc p) (hd : 0<corridorGap p)
    (n : Nat) (hbig : (4:Int)^n*corridorGap p>Vc p+42*n+72) :
    ∃ k t, 0<k ∧ k≤2*n ∧ run k p=some t ∧ isSection t := by
  classical
  by_cases hex : ∃ k t, 0<k ∧ k≤2*n ∧ run k p=some t ∧ isSection t
  · exact hex
  · exfalso
    have avoidGood (N : Nat) (hN : N≤2*n) (hg : good p N) : avoid p N := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,by omega,hg k hkN,hs⟩
    have full (i : Nat) (hi : i≤n) : good p (2*i) ∧ (trace p (2*i)).2%2=1 ∧
        Vc p≤Vc (trace p (2*i)) ∧ Vc (trace p (2*i))≤Vc p+42*i ∧ corridorGap (trace p (2*i))=4^i*corridorGap p := by
      induction i with
      | zero => simp [trace,run]; exact ⟨good_zero p,hodd⟩
      | succ i ih =>
        obtain ⟨hg,ho,hlo,hhi,heq⟩ := ih (by omega)
        have hpos : 0<corridorGap (trace p (2*i)) := by rw [heq]; exact Int.mul_pos (Int.pow_pos (by decide)) hd
        have hg1 := good_next p (2*i) hg (above_no_halt _ (by omega) hpos)
        have hev := next_odd_to_even _ _ (good_step p (2*i+1) (2*i) hg1 (by omega)) ho (avoidGood _ (by omega) hg1 _ (by omega) (by omega))
        have hnext1 : next (trace p (2*i+1))≠none := by
          intro h
          have hh := halt_equation _ h
          simp only [Uc,Vc] at hh
          omega
        have hg2 := good_next p (2*i+1) hg1 hnext1
        have hs := above_block (trace p (2*i)) (trace p (2*i+1)) (trace p (2*(i+1)))
          (good_step p _ _ hg2 (by omega))
          (by simpa only [show 2*i+1+1=2*(i+1) by omega] using good_step p _ (2*i+1) hg2 (by omega))
          ho (avoidGood _ (by omega) hg2 _ (by omega) (by omega)) (avoidGood _ (by omega) hg2 _ (by omega) (by omega)) (by omega) hpos
        refine ⟨by simpa only [show 2*i+1+1=2*(i+1) by omega] using hg2,hs.1,by omega,by omega,?_⟩
        rw [hs.2.1,heq,Int.pow_succ,Int.mul_assoc,Int.mul_left_comm 4]
    obtain ⟨_,_,_,hV,hD⟩ := full n (by omega)
    have hphys : Uc (trace p (2*n))≤Vc (trace p (2*n))+18 := by simp [Uc,Vc]; omega
    have hbound : corridorGap (trace p (2*n))≤Vc (trace p (2*n))+72 := by
      unfold corridorGap defect phaseDefect
      cases h : phaseOf (trace p (2*n)) <;> simp [h] <;> omega
    omega

#print axioms positive_prefix_or_return
#print axioms above_return

/-- Once the low-order error experiences an F,F block it is strictly on the
    high side of the alternating corridor, and stays there. -/
theorem error_strict_after_F (P r a x y : Int) (n : Nat) (U V : Nat → Int) (e phase : Nat → Bool)
    (hy : 27≤y) (hU : U 0=a*P+x) (hV : V 0=r*P+y)
    (hstart : phase 0=true) (hdef : defect x y=-18) (hs : PhaseBlocks U V e phase n) :
    ∀ i, i≤n → (∃ k, k<i ∧ e k=false) →
      phaseDefect (phase i)<defect (U i-lead r a e i*P) (V i-r*P) := by
  intro i hi hseen
  induction i with
  | zero => obtain ⟨k,hk,_⟩ := hseen; omega
  | succ i ih =>
    have hprev := error_corridor P r a x y n U V e phase hy hU hV hstart hdef hs i (by omega)
    obtain ⟨hp,hu,hv⟩ := hs i (by omega)
    by_cases he : e i=false
    · simp only [lead,hu,hv,hp,defect,Int.sub_mul,Int.mul_assoc]
      unfold defect at hprev
      unfold phaseDefect at hprev ⊢
      cases hph : phase i <;> simp [he,hph,Int.mul_assoc] at hu hv hprev ⊢ <;> omega
    · have he' : e i=true := by cases h : e i <;> simp_all
      have hseen' : ∃ k, k<i ∧ e k=false := by
        obtain ⟨k,hk,hf⟩ := hseen
        have hne : k≠i := by intro heq; subst k; exact he hf
        exact ⟨k,by omega,hf⟩
      have hstrict := ih (by omega) hseen'
      simp only [lead,hu,hv,hp,defect,Int.sub_mul,Int.mul_assoc]
      unfold defect at hstrict
      unfold phaseDefect at hstrict ⊢
      cases hph : phase i <;> simp [he',hph,Int.mul_assoc] at hu hv hstrict ⊢ <;> omega

theorem lead_all_true_below (r a : Int) (e : Nat → Bool) (i : Nat)
    (ha : 3*a<2*r) (hs : ∀ j, j<i → e j=true) : 3*lead r a e i<2*r := by
  induction i with
  | zero => exact ha
  | succ i ih =>
    have h := ih (fun j hj => hs j (by omega))
    simp [lead,hs i (by omega)]
    omega

theorem lead_middle (s : Nat) (d P x y : Int) (U V : Nat → Int) (e : Nat → Bool)
    (hx : 0≤x) (hy : 0≤y) (hU : U 0=lowA s d*P+x) (hV : V 0=lowR s*P+y)
    (hs : Blocks U V e (lowL s)) (hp : Physical U V (lowL s))
    (hsep : 3*cap (budget x y (lowL s)) (lowL s)+39<P) :
    (lead (lowR s) (lowA s d) e (2*s+2)=0 ∧ d%27=18) ∨
    (3*lead (lowR s) (lowA s d) e (2*s+2)=2*lowR s ∧ d%27=0) := by
  let H : Int := 8*16^s
  let i : Nat := 2*s+2
  have hH : 0<H := Int.mul_pos (by decide) (Int.pow_pos (by decide))
  have hr : lowR s=27*H := by simp [lowR,H]; omega
  have hpow : (4:Int)^i=2*H := by
    dsimp [i,H]
    rw [Int.pow_add,Int.pow_mul]
    change (16:Int)^s*16=2*(8*16^s)
    omega
  obtain ⟨q,hq⟩ := lead_form (lowR s) (lowA s d) e i
  rw [hpow] at hq
  have hz : lead (lowR s) (lowA s d) e i=H*(2*lowA s d+27*q) := by
    rw [hq,hr,Int.mul_add,Int.mul_left_comm H 2,Int.mul_assoc,Int.mul_left_comm H 27,Int.mul_assoc 27 H q]
  have hb := leading_bounds P (lowR s) (lowA s d) x y (lowL s) (lowL s) U V e hx hy (by omega) hU hV hs hp hsep
  have h := four_scaled H (lowR s) (lowA s d) e i (2*lowA s d+27*q) hH hr hz (by simpa [i,lowL] using hb)
  have hm : lowA s d%27=(9-2*d)%27 := low_coeff_mod s d
  change (lead (lowR s) (lowA s d) e i=0 ∧ d%27=18) ∨ (3*lead (lowR s) (lowA s d) e i=2*lowR s ∧ d%27=0)
  rcases h with h|h <;> rw [h] at hz <;> omega

theorem power4_linear (n : Nat) (hn : 5≤n) : (43:Int)*n+73≤4^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 5≤n
    · have hh := ih h
      rw [Int.pow_succ,Int.natCast_succ]
      omega
    · have he : n=4 := by omega
      subst n
      decide

theorem above_eventual_return (p : State) (hodd : p.2%2=1) (hr : 360≤Vc p) (hd : 0<corridorGap p) :
    ∃ k t, 0<k ∧ run k p=some t ∧ isSection t := by
  let n := (Vc p).toNat+5
  have hn : (Vc p:Int)≤n := by dsimp [n]; omega
  have hp := power4_linear n (by dsimp [n]; omega)
  have hm := Int.mul_le_mul_of_nonneg_left (show 1≤corridorGap p by omega) (show 0≤(4:Int)^n from Int.pow_nonneg (by decide))
  simp at hm
  obtain ⟨k,t,hk,_,hrun,hs⟩ := above_return p hodd hr hd n (by omega)
  exact ⟨k,t,hk,hrun,hs⟩

/-- Every separated low-side prepared phase with d not 18 mod27 returns
    safely, including the previously exceptional zero-residue class. -/
theorem return_except18 (p : State) (s : Nat) (d P x y : Int)
    (hodd : p.2%2=1) (hph : phaseOf p=true) (hr : 360≤Vc p)
    (hd : 0<d) (hd18 : d%27≠18) (hx : 0≤x) (hy : 153<y)
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
      · exact False.elim (hd18 h.2)
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
theorem prepared_except18 (s j d u : Nat) (hd : 6≤d) (hp : d%4=2)
    (hd18 : d%27≠18) (hj : 2≤j) (hdsmall : d≤16^s)
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
  obtain ⟨k,t,hk,hkn,ht,hs⟩ := return_except18 p s d ((16:Int)^j) (lowX d j) (lowY d j) ho hph hRank (by omega) (by omega) hx hy hdef hu hv hsep n hbound
  refine ⟨4*(j+s)+3+4*j+k,t,by omega,by dsimp [lowL,n] at hkn; omega,?_,hs⟩
  rw [run_add,hr,Option.bind_some]
  exact ht

#print axioms return_except18
#print axioms prepared_except18

end BB429.CoarseExit
