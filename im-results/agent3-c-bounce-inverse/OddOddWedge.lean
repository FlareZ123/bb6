import OddSevenSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem oddodd_bounce_succ_div8 (a n : Nat)
    (ha : 2≤a) (he : a%2=0) :
    8 ∣ 2^(n+1)*(2*(a-1)+6) := by
  have hbase : 2*(a-1)+6=4*(a/2+1) := by omega
  refine ⟨2^n*(a/2+1), ?_⟩
  calc
    2^(n+1)*(2*(a-1)+6) = (2^n*2)*(4*(a/2+1)) := by rw [hbase, Nat.pow_succ]
    _ = 8*(2^n*(a/2+1)) := by
      calc
        (2^n*2)*(4*(a/2+1)) = (2*4)*(2^n*(a/2+1)) := by ac_rfl
        _ = 8*(2^n*(a/2+1)) := by rfl

/-- The odd-odd output region x+y≡4 mod16 has a unique exact original
    source predecessor. The bound y≥5 removes the exceptional (5,1) output. -/
theorem oddodd_parent_equations (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=4)
    (h : secNext (a,k)=some (x,y)) :
    x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  have hp := (section_preimage_all_iff a k x y).mp h
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,ha0,hk0,hk1] at hp
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
        obtain ⟨_,n,hpow,_⟩ := hp
        have hd : 8 ∣ 2^n*8 := ⟨2^n,by omega⟩
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
              rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 16 ∣ 2^n*16 := ⟨2^n,by omega⟩
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        omega
      · by_cases hlow : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos heven] at hp
            obtain ⟨_,n,hpow,hcost⟩ := hp
            cases n with
            | zero => simp at hpow hcost; omega
            | succ n =>
                have hd := oddodd_bounce_succ_div8 a n ha2 heven
                omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg heven] at hp
            rcases hp with ⟨hy3,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2 ∣ 2^n*(2*(a-1)+8) := by
                refine ⟨2^n*((a-1)+4),?_⟩
                calc
                  2^n*(2*(a-1)+8) = 2^n*(2*((a-1)+4)) := by congr 1 <;> omega
                  _ = 2*(2^n*((a-1)+4)) := by ac_rfl
              omega

/-- Full if and only if: a necessary solution to the two linear source
    equations is automatically a genuine Machine C transition. -/
theorem oddodd_parent_iff (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=4) :
    secNext (a,k)=some (x,y) ↔
      x+y=2*a+4 ∧ x+3*y=4*k+10 := by
  constructor
  · exact oddodd_parent_equations a k x y hx hy hy5 hs
  · rintro ⟨hsum,hcost⟩
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow : ¬2*k≤a := by omega
    have heven : a%2=0 := by omega
    apply (section_preimage_all_iff a k x y).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
      if_neg hk0,if_neg hlow,if_pos heven]
    refine ⟨by omega,0,?_,?_⟩ <;> simp <;> omega

/-- A two-dimensional all-time forbidden wedge whose unique real parents
    are in the previously certified odd-seven forbidden family. -/
theorem oddodd_slope_blank_unreachable (p q time : Nat)
    (hlarge : 16*q+6≤p) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (8*p-128*q-45,8*p+128*q+49) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some s =>
          rcases s with ⟨a,k⟩
          have ht : secNext (a,k) = some (8*p-128*q-45,8*p+128*q+49) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := oddodd_parent_equations a k
            (8*p-128*q-45) (8*p+128*q+49)
            (by omega) (by omega) (by omega) (by omega) ht
          have haeq : a=8*p := by omega
          have hkeq : k=8*p+64*q+23 := by omega
          have hparent : BB6.Agent8Section.run secNext n (some (5,1)) =
              some (8*p,8*p+64*q+23) := by rwa [haeq,hkeq] at hp
          exact odd_seven_slope_blank_unreachable p q n hparent

/-- Growth of the halting-level power, uniform beyond the second level. -/
private theorem halting_power_linear (n : Nat) :
    16*(n+3) ≤ 2^(2*n+6) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hstep : 2^(2*(n+1)+6)=4*2^(2*n+6) := by
        calc
          2^(2*(n+1)+6)=2^((2*n+6)+2) := by congr 1 <;> omega
          _=2^(2*n+6)*2^2 := by rw [Nat.pow_add]
          _=4*2^(2*n+6) := by omega
      rw [hstep]
      omega

/-- A uniform genuinely blank-unreachable infinite family within the
    second (odd-first) authentic halting locus. These conditions guarantee
    that the unique incoming source is in the already proved odd-seven
    unreachable wedge. -/
theorem high_halt_oddodd_256_unreachable
    (j m k time : Nat)
    (hm : 6≤m) (hm4 : m%4=2)
    (hjm : (j+m)%256=222)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  let P : Nat := 2^(2*m+2)
  have hpow : 16*(m+1)≤P := by
    have hh := halting_power_linear (m-2)
    have he : 2*(m-2)+6=2*m+2 := by omega
    have hr : 16*((m-2)+3)=16*(m+1) := by omega
    dsimp [P]
    simpa only [he,hr] using hh
  have hPbig : m+34≤P := by omega
  have hPj : 3*j≤P*j := Nat.mul_le_mul_right j (by omega)
  have hP3 : 3*m+102≤3*P := by omega
  have hPdist : P*(j+3)=P*j+3*P := by
    rw [Nat.mul_add]
    omega
  have hlarge : (2*j+3)+94≤k := by
    change k+j+3*m+5=P*(j+3) at hgate
    rw [hPdist] at hgate
    omega
  have hpowDiv : 256 ∣ P := by
    dsimp [P]
    change 2^8 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨d,hd⟩ := hpowDiv
  have hmod : (k+j+3*m+5)%256=0 := by
    have hdiv : 256 ∣ k+j+3*m+5 := by
      refine ⟨d*(j+3),?_⟩
      calc
        k+j+3*m+5 = P*(j+3) := hgate
        _ = (256*d)*(j+3) := by rw [hd]
        _ = 256*(d*(j+3)) := by ac_rfl
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hsum : ((2*j+3)+k)%16=4 := by omega
  have hdiff : (k-(2*j+3))%256=94 := by omega
  let p := ((2*j+3)+k-4)/16
  let q := (k-(2*j+3)-94)/256
  have hp : (2*j+3)+k=16*p+4 := by dsimp [p]; omega
  have hq : k-(2*j+3)=256*q+94 := by dsimp [q]; omega
  have hpq : 16*q+6≤p := by omega
  have hx : 2*j+3=8*p-128*q-45 := by omega
  have hy : k=8*p+128*q+49 := by omega
  rw [hx,hy]
  exact oddodd_slope_blank_unreachable p q time hpq

#print axioms high_halt_oddodd_256_unreachable
#print axioms oddodd_slope_blank_unreachable
#print axioms oddodd_parent_iff
end BB6.Agent3
