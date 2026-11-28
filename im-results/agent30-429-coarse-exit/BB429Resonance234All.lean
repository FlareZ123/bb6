import BB429Resonance234Complete
import BB429ResonanceFinite

namespace BB429.CoarseExit

set_option maxRecDepth 20000
set_option maxHeartbeats 50000000

/-- Clean re-indexing of the exact d=234 post-resonance state, independent of
    the superseded modulo-9 large-scale module. -/
theorem d234_post_m_complete (m : Nat) (hm : 2≤m) :
    run (8*m+7) (prepared m 234) =
      some (416*m+3965,72*16^m-808*m-7677) := by
  obtain ⟨j,rfl⟩ : ∃ j : Nat, m=j+2 := ⟨m-2,by omega⟩
  have h := d234_post j
  have hp : 72*16^(j+2)=18432*16^j := by
    rw [Nat.pow_add,show 16^2=256 by decide]
    omega
  rw [show 8*(j+2)+7=8*j+23 by omega]
  convert h using 1 <;> simp only [Prod.mk.injEq,Option.some.injEq]
  · omega
  · rw [hp]
    have hpow : 1≤16^j := Nat.pow_pos (by decide)
    omega

theorem d234_post_counter_nonneg (m : Nat) (hm : 2≤m) :
    808*m+7677 ≤ 72*16^m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : 2≤m
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : m=1 := by omega
      subst m
      decide

theorem d234_burst_growth_complete (s : Nat) (hs : 3≤s) :
    832*(4*s+3)+7936 ≤ 72*16^s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases h : 3≤s
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : s=2 := by omega
      subst s
      decide

theorem d234_sep_growth_complete (s : Nat) (hs : 4≤s) :
    (9375:Int)*(1000*s+4000)+40≤128^s := by
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

/-- The exact doubled second burst for d=234 always returns when m≠35.
    The old m≡8 (mod 9) exceptional class disappears: if the bounded
    leading coefficient hits its only surviving value 36, the complete
    resonance theorem strips all leading false digits and evacuates the
    resulting minimal resonance geometrically. -/
theorem d234_even_second_return_complete
    (m s j : Nat) (hm : m=j+s) (hm2 : 2≤m) (hm35 : m≠35)
    (hbudget :
      2*((416*m+3968)*2^(4*j)-3) ≤
        72*16^m+24*m+253+12*j)
    (hsep :
      3*cap
        (budget 0 (72*(m:Int)+759+36*(j:Int)) (2*s+5))
        (2*s+5)+39 < (16:Int)^j) :
    ∃ k t, 0<k ∧ k≤16*m+17 ∧
      run k (prepared m 234)=some t ∧ isSection t := by
  let K := 4*j
  let I := 2*s+1
  let P := 2^K
  let u := (416*m+3968)*P-3
  let R := 72*16^m+24*m+253+3*K
  let w := R-2*u
  let a : Int := 2496*(m:Int)+23808
  let y : Int := 72*(m:Int)+759+9*(K:Int)
  have hu : u+3=(416*m+3968)*P := by
    have hp : 3≤(416*m+3968)*P :=
      Nat.le_mul_of_pos_right _ (Nat.pow_pos (a:=2) (n:=K) (by decide))
    dsimp [u]
    omega
  have hR : 2*u+w=R := by
    dsimp [w]
    dsimp [R,K,P] at hbudget ⊢
    omega
  have hfirst := d234_post_m_complete m hm2
  have hburst :
      run K (416*m+3965,72*16^m-808*m-7677)=some (u,w) := by
    apply LowReturnBand.section_burst
    · simpa [P] using hu
    · rw [hR]
      dsimp [R]
      have hW := d234_post_counter_nonneg m hm2
      omega
  have hp : w%2=1 := by
    have hRodd : R%2=1 := by
      dsimp [R,K]
      omega
    omega
  have hUc : Uc (u,w)=a*(P:Int) := by
    have h := congrArg (fun z : Nat => (z:Int)) hu
    simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at h
    simp [Uc,a]
    grind +ring
  have hV : Vc (u,w)=(54*(4:Int)^I)*(P:Int)+y := by
    have hr := congrArg (fun z : Nat => (z:Int)) hR
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int] at hr
    have hpow : (54:Int)*4^I*(P:Int)=216*16^m := by
      dsimp [I,P,K]
      push_cast
      rw [Int.pow_add (4:Int) (2*s) 1,Int.pow_mul,Int.pow_mul]
      rw [hm,Int.pow_add]
      change 54*((16:Int)^s*4)*(16:Int)^j =
        216*((16:Int)^j*(16:Int)^s)
      grind +ring
    rw [hpow]
    simp [Vc,y]
    dsimp [R] at hr
    omega
  have hsep' :
      3*cap (budget 0 y (I+4)) (I+4)+39<(P:Int) := by
    dsimp [I,P,K,y]
    push_cast
    simpa using hsep
  have hphase : phaseOf (u,w)=true := by
    unfold phaseOf
    simp only [Prod.fst,Prod.snd]
    have hh : (2*u+w)%4=1 := by
      rw [hR]
      dsimp [R,K]
      omega
    simp [hh]
  have hyform : y=108*(m:Int)+777-18*(I:Int) := by
    dsimp [y,I,K]
    push_cast
    have hmI : (m:Int)=(j:Int)+(s:Int) := by exact_mod_cast hm
    rw [hmI]
    omega
  have hscale : (4:Int)^I*(P:Int)=4*(16:Int)^m := by
    dsimp [I,P,K]
    push_cast
    rw [Int.pow_add (4:Int) (2*s) 1,Int.pow_mul,Int.pow_mul]
    rw [hm,Int.pow_add]
    change ((16:Int)^s*4)*(16:Int)^j =
      4*((16:Int)^j*(16:Int)^s)
    grind +ring
  obtain ⟨k,t,hk,hkn,ht,hs⟩ :=
    return_from_exact_burst_even_complete
      (u,w) I m a (P:Int) y hp
      (by simp [y,K]; omega) hUc hV hsep'
      (by dsimp [I]; omega) hphase hm35 rfl hyform hscale
  refine ⟨8*m+7+K+k,t,by omega,?_,?_,hs⟩
  · dsimp [K,I] at hkn
    omega
  · rw [run_add,run_add,hfirst,Option.bind_some,hburst,Option.bind_some,ht]

/-- Every large d=234 scale except the concrete m=35 short resonance returns
    to a section.  No congruence class modulo 9 remains exceptional. -/
theorem d234_large_complete (s t : Nat) (hs : 4≤s) (ht : t<4)
    (hm35 : 4*s+t≠35) :
    ∃ k p, 0<k ∧ k≤16*(4*s+t)+17 ∧
      run k (prepared (4*s+t) 234)=some p ∧ isSection p := by
  let j := 3*s+t
  let m := j+s
  have hm : m=4*s+t := by
    dsimp [m,j]
    omega
  have hX : 16^m=16^j*16^s := by
    dsimp [m]
    rw [Nat.pow_add]
  have hP : 2^(4*j)=16^j := by rw [Nat.pow_mul]
  have hg := d234_burst_growth_complete s (by omega)
  have hcoef : 2*(416*m+3968)≤72*16^s := by
    rw [hm]
    omega
  have hb :
      2*((416*m+3968)*2^(4*j)-3) ≤
        72*16^m+24*m+253+12*j := by
    have hh := Nat.mul_le_mul_right (16^j) hcoef
    rw [hP,hX]
    calc
      2*((416*m+3968)*16^j-3) ≤ 2*(416*m+3968)*16^j := by omega
      _ ≤ 72*(16^j*16^s) := by
        simpa [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hh
      _ ≤ 72*(16^j*16^s)+24*m+253+12*j := by omega
  let L := 2*s+5
  let y : Int := 72*(m:Int)+759+36*(j:Int)
  have hB : budget 0 y L≤1000*(s:Int)+4000 := by
    simp [budget,y,L,m,j]
    omega
  have h25 : 1≤(25:Int)^s := by
    have hh := Int.pow_pos (m:=s) (show (0:Int)<25 by decide)
    omega
  have h5 : (5:Int)^L=3125*25^s := by
    dsimp [L]
    rw [Int.pow_add,Int.pow_mul]
    change (25:Int)^s*3125=3125*25^s
    exact Int.mul_comm ..
  have hcap : 3*cap (budget 0 y L) L+39≤128^s*25^s := by
    rw [cap_eq,h5]
    have hh := Int.mul_le_mul_of_nonneg_right hB (show 0≤(25:Int)^s by omega)
    have hh' := Int.mul_le_mul_of_nonneg_right (d234_sep_growth_complete s hs)
      (show 0≤(25:Int)^s by omega)
    have hmul : (25:Int)^s*budget 0 y L=budget 0 y L*25^s := Int.mul_comm ..
    have hdist :
        ((9375:Int)*(1000*s+4000)+40)*25^s =
          9375*((1000*s+4000)*25^s)+40*25^s := by
      grind +ring
    have hgoal :
        3*(3125*25^s*budget 0 y L)=
          9375*((25:Int)^s*budget 0 y L) := by
      grind +ring
    rw [hdist] at hh'
    rw [hgoal,hmul]
    have haux : (40:Int)≤40*25^s := by omega
    omega
  have hbig : (128:Int)^s*25^s≤16^j := by
    rw [←Int.mul_pow]
    change (3200:Int)^s≤16^j
    have h1 : (3200:Int)^s≤4096^s := by
      induction s with
      | zero => decide
      | succ s ih =>
        rw [Int.pow_succ,Int.pow_succ]
        have hp : 0≤(4096:Int)^s := Int.pow_nonneg (by decide)
        omega
    have h2 : (4096:Int)^s≤16^j := by
      dsimp [j]
      rw [Int.pow_add,Int.pow_mul]
      change (4096:Int)^s≤4096^s*16^t
      have hp : 1≤(16:Int)^t := by
        have hh := Int.pow_pos (m:=t) (show (0:Int)<16 by decide)
        omega
      have hh := Int.mul_le_mul_of_nonneg_left hp
        (show 0≤(4096:Int)^s from Int.pow_nonneg (by decide))
      rw [Int.mul_one] at hh
      exact hh
    omega
  have hsep :
      3*cap (budget 0 y L) L+39<(16:Int)^j := by
    have hp : 0<(16:Int)^j := Int.pow_pos (by decide)
    omega
  obtain ⟨k,p,hk,hkn,hr,hs'⟩ :=
    d234_even_second_return_complete m s j rfl
      (by dsimp [m,j]; omega)
      (by rw [hm]; exact hm35) hb
      (by simpa [L,y] using hsep)
  rw [hm] at hkn hr
  exact ⟨k,p,hk,hkn,hr,hs'⟩

/-- The unique short resonance m=35 is already an exact finite source witness,
    so the large theorem has no exceptional scale at all. -/
theorem d234_large_all (s t : Nat) (hs : 4≤s) (ht : t<4) :
    ∃ k p, 0<k ∧ k≤16*(4*s+t)+17 ∧
      run k (prepared (4*s+t) 234)=some p ∧ isSection p := by
  by_cases hm : 4*s+t=35
  · rw [hm]
    exact ⟨559,
      (0,100353353393387804136910732226917626776914176),
      by decide,by decide,d234_m35,by simp [isSection]⟩
  · exact d234_large_complete s t hs ht hm

/-- All d=234 prepared scales return to a section.  Sixteen small scales are
    concrete kernel-reduced witnesses; every m≥16 is discharged uniformly by
    the complete resonance proof, including m=35. -/
theorem d234_all (m : Nat) :
    ∃ k p, 0<k ∧ k≤16*m+17 ∧
      run k (prepared m 234)=some p ∧ isSection p := by
  by_cases hm : 16≤m
  · let s := m/4
    let t := m%4
    have hs : 4≤s := by
      dsimp [s]
      omega
    have ht : t<4 := by
      dsimp [t]
      exact Nat.mod_lt _ (by decide)
    have h := d234_large_all s t hs ht
    have he : 4*s+t=m := by
      dsimp [s,t]
      omega
    simpa only [he] using h
  · have cases :
      m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6 ∨ m=7 ∨
      m=8 ∨ m=9 ∨ m=10 ∨ m=11 ∨ m=12 ∨ m=13 ∨ m=14 ∨ m=15 := by
      omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨9,(11,326),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨13,(11,1418),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨31,(0,18776),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨39,(0,295276),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨51,(0,4718992),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨65,(11,75497906),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨75,(0,1207960028),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨87,(0,19327353344),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨97,(11,309237645838),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨109,(11,4947802325554),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨121,(11,79164837200470),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨133,(11,1266637395198586),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨145,(11,20266198323167902),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨155,(0,324259173170676416),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨167,(0,5188146770730812132),by decide,by decide,by native_decide,by simp [isSection]⟩
    · exact ⟨179,(0,83010348331692983048),by decide,by decide,by native_decide,by simp [isSection]⟩

#print axioms d234_post_m_complete
#print axioms d234_post_counter_nonneg
#print axioms d234_burst_growth_complete
#print axioms d234_sep_growth_complete
#print axioms d234_even_second_return_complete
#print axioms d234_large_complete
#print axioms d234_large_all
#print axioms d234_all

end BB429.CoarseExit
