import CSixSeventhS2
import CSixSeventhS2QEven
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB6.Agent34S2Pullback
open BB6.Agent4Seven
open BB6.Agent46

/-- The standard six-state high-stop counter used by the Machine C filter. -/
def highK (j m : Nat) : Nat :=
  (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ (2:Nat)^(2*m+2)*(j+3) := by
  induction m with
  | zero => omega
  | succ m ih =>
      have hpow2 : (2:Nat)^2=4 := by decide
      have hpow : (2:Nat)^(2*(m+1)+2) = 4*(2:Nat)^(2*m+2) := by
        calc
          (2:Nat)^(2*(m+1)+2) = (2:Nat)^((2*m+2)+2) := by congr 1 <;> omega
          _ = (2:Nat)^(2*m+2)*(2:Nat)^2 := Nat.pow_add _ _ _
          _ = 4*(2:Nat)^(2*m+2) := by rw [hpow2]; ac_rfl
      have hmul := Nat.mul_le_mul_left 4 ih
      rw [hpow]
      calc
        j+3*(m+1)+5 = j+3*m+8 := by omega
        _ ≤ 4*(j+3*m+5) := by omega
        _ ≤ 4*((2:Nat)^(2*m+2)*(j+3)) := hmul
        _ = 4*(2:Nat)^(2*m+2)*(j+3) := by ac_rfl

private theorem high_stop_identity (j m : Nat) :
    highK j m + (j+3*m+5) = (2:Nat)^(2*m+2)*(j+3) := by
  unfold highK
  exact Nat.sub_add_cancel (high_score_nonnegative j m)

private theorem s2_m_mod512 (u m : Nat)
    (hmres : m%131072=(72746+75264*u)%131072) : m%512=42 := by
  have hdiv : 512∣131072 := by decide
  calc
    m%512 = (m%131072)%512 := (Nat.mod_mod_of_dvd m hdiv).symm
    _ = ((72746+75264*u)%131072)%512 := by rw [hmres]
    _ = 42 := by omega

private theorem s2_highstop_mod (u m k : Nat)
    (hmres : m%131072=(72746+75264*u)%131072)
    (hmod : (k+(319+512*u)+3*m+5)%131072=0) :
    (k+95232*u)%131072=43582 := by omega

private theorem s2_highstop_k_mod (u k : Nat)
    (hKcong : (k+95232*u)%131072=43582) : k%1024=574 := by
  have hdiv : 1024∣131072 := by decide
  have hmod1024 : (k+95232*u)%1024=43582%1024 := by
    calc
      (k+95232*u)%1024 = ((k+95232*u)%131072)%1024 :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = 43582%1024 := by rw [hKcong]
  have h95232 : 1024∣95232*u := by
    refine ⟨93*u,?_⟩
    omega
  have hmodAdd : (k+95232*u)%1024=k%1024 := by
    rcases h95232 with ⟨q,hq⟩
    omega
  omega

private theorem q_m_mod512 (u m : Nat)
    (hmres : m%1048576=(531498+337408*u)%1048576) : m%512=42 := by
  have hdiv : 512∣1048576 := by decide
  calc
    m%512 = (m%1048576)%512 := (Nat.mod_mod_of_dvd m hdiv).symm
    _ = ((531498+337408*u)%1048576)%512 := by rw [hmres]
    _ = 42 := by omega

private theorem q_highstop_mod (u m k : Nat)
    (hmres : m%1048576=(531498+337408*u)%1048576)
    (hmod : (k+(319+512*u)+3*m+5)%1048576=0) :
    (106*(319+512*u)+57*k)%1048576=355300 := by omega

private theorem q_highstop_k_mod (u k : Nat)
    (hKcong : (106*(319+512*u)+57*k)%1048576=355300) :
    k%1024=574 := by
  have hdiv : 1024∣1048576 := by decide
  have hmod1024 : (106*(319+512*u)+57*k)%1024=355300%1024 := by
    calc
      (106*(319+512*u)+57*k)%1024 =
          ((106*(319+512*u)+57*k)%1048576)%1024 :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = 355300%1024 := by rw [hKcong]
  omega

/-- Exact pullback of the S2 image sector to the high-stop (j,m) lattice. -/
theorem s2_parameter_pullback_iff (j m : Nat) :
  (j%512=319 ∧ (3*m+102921)%131072=(185*j)%131072) ↔
  (j%512=319 ∧ m%131072=(72746+75264*(j/512))%131072) := by
  constructor
  · rintro ⟨hj,hc⟩
    let u := j/512
    have hjEq : j=319+512*u := by
      have hd := Nat.mod_add_div j 512
      rw [hj] at hd
      dsimp [u]
      omega
    constructor
    · exact hj
    · omega
  · rintro ⟨hj,hm⟩
    let u := j/512
    have hjEq : j=319+512*u := by
      have hd := Nat.mod_add_div j 512
      rw [hj] at hd
      dsimp [u]
      omega
    constructor
    · exact hj
    · omega

/-- Exact pullback of the complementary q-even image sector to the high-stop lattice. -/
theorem q_even_parameter_pullback_iff (j m : Nat) :
  (j%512=319 ∧ (171*m+355585)%1048576=(49*j)%1048576) ↔
  (j%512=319 ∧ m%1048576=(531498+337408*(j/512))%1048576) := by
  constructor
  · rintro ⟨hj,hc⟩
    let u := j/512
    have hjEq : j=319+512*u := by
      have hd := Nat.mod_add_div j 512
      rw [hj] at hd
      dsimp [u]
      omega
    constructor
    · exact hj
    · omega
  · rintro ⟨hj,hm⟩
    let u := j/512
    have hjEq : j=319+512*u := by
      have hd := Nat.mod_add_div j 512
      rw [hj] at hd
      dsimp [u]
      omega
    constructor
    · exact hj
    · omega

/-- Adjacent q-even hcong=5 high-stop cylinder. This is only a parameter
    pullback; the bounce-parent blank-root question remains open. -/
theorem q_even_h5_parameter_pullback_iff (j m : Nat) :
  (j%512=319 ∧ (171*m+879873)%1048576=(49*j)%1048576) ↔
  (j%512=319 ∧ m%1048576=(7210+337408*(j/512))%1048576) := by
  constructor
  · rintro ⟨hj,hc⟩
    let u := j/512
    have hjEq : j=319+512*u := by
      have hd := Nat.mod_add_div j 512
      rw [hj] at hd
      dsimp [u]
      omega
    constructor
    · exact hj
    · omega
  · rintro ⟨hj,hm⟩
    let u := j/512
    have hjEq : j=319+512*u := by
      have hd := Nat.mod_add_div j 512
      rw [hj] at hd
      dsimp [u]
      omega
    constructor
    · exact hj
    · omega


/-- Every high-stop parameter in the S2 cylinder has an all-time root exclusion. -/
theorem s2_high_parameter_no_blank (j m time : Nat)
    (hj : j%512=319)
    (hm : m%131072=(72746+75264*(j/512))%131072) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,highK j m) := by
  let u := j/512
  let k := highK j m
  change BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k)
  have hjEq : j=319+512*u := by
    have hd := Nat.mod_add_div j 512
    rw [hj] at hd
    dsimp [u]
    omega
  have hm512 : m%512=42 := s2_m_mod512 u m (by simpa [u] using hm)
  have hm42 : 42≤m := by omega
  have hpow : 131072 ∣ (2:Nat)^(2*m+2) := by
    have hp : (2:Nat)^17 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^17=131072 by decide] using hp
  have hstop : k+(j+3*m+5)=(2:Nat)^(2*m+2)*(j+3) := by
    simpa [k] using high_stop_identity j m
  have hprod : 131072 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    obtain ⟨q,hq⟩ := hpow
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hdiv : 131072 ∣ k+(j+3*m+5) := by
    rw [hstop]
    exact hprod
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hmod' : (k+(319+512*u)+3*m+5)%131072=0 := by
    simpa [hjEq, Nat.add_assoc] using hmod
  have hKcong : (k+95232*u)%131072=43582 :=
    s2_highstop_mod u m k (by simpa [u] using hm) hmod'
  have hkmod : k%1024=574 := s2_highstop_k_mod u k hKcong
  let v := k/1024
  have hkv : k=574+1024*v := by
    have hd := Nat.mod_add_div k 1024
    dsimp [v]
    omega
  have hsector : (v+93*u)%128=42 := by
    rw [hkv] at hKcong
    omega
  obtain ⟨t,ht,hv⟩ := BB6.Agent4SevenS2.s2_sector_decompose u v hsector
  have hblank := BB6.Agent4SevenS2.blank_ne_s2_image u v t time ht hv
  have hx : 2*j+3=641+1024*u := by rw [hjEq]; omega
  intro hrun
  apply hblank
  rw [hx,hkv] at hrun
  exact hrun

/-- The q-even congruence on (u,v) is equivalent to the complementary source lift. -/
theorem q_even_image_blank_unreachable_uv (u v t time : Nat)
    (ht : u+v=2+4*t)
    (hcong : (53*u+57*v)%1024=282) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (641+1024*u,574+1024*v) := by
  have hmod : (u+7*t+10)%32=0 := by
    have h := Nat.mod_add_div (53*u+57*v) 1024
    rw [hcong] at h
    omega
  let z := (u+7*t+10)/32
  have hzEq : u+7*t+10=32*z := by
    have hd := Nat.mod_add_div (u+7*t+10) 32
    rw [hmod] at hd
    dsimp [z]
    omega
  have hu : u=32*z-7*t-10 := by omega
  have hv : v=12+11*t-32*z := by omega
  have hlo : 7*t+10≤32*z := by omega
  have hhi : 32*z≤12+11*t := by omega
  have hcong' : (2*t-z)%8=1 := by
    have h := Nat.mod_add_div (53*u+57*v) 1024
    rw [hcong] at h
    omega
  have hblank := BB6.Agent4SevenS2QEven.blank_ne_s2q_even_image t z time hlo hhi hcong'
  intro hrun
  apply hblank
  rw [hu,hv] at hrun
  exact hrun

/-- Every high-stop parameter in the q-even cylinder has an all-time root exclusion. -/
theorem q_even_high_parameter_no_blank (j m time : Nat)
    (hj : j%512=319)
    (hm : m%1048576=(531498+337408*(j/512))%1048576) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,highK j m) := by
  let u := j/512
  let k := highK j m
  change BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k)
  have hjEq : j=319+512*u := by
    have hd := Nat.mod_add_div j 512
    rw [hj] at hd
    dsimp [u]
    omega
  have hm512 : m%512=42 := q_m_mod512 u m (by simpa [u] using hm)
  have hm42 : 42≤m := by omega
  have hpow : 1048576 ∣ (2:Nat)^(2*m+2) := by
    have hp : (2:Nat)^20 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^20=1048576 by decide] using hp
  have hstop : k+(j+3*m+5)=(2:Nat)^(2*m+2)*(j+3) := by
    simpa [k] using high_stop_identity j m
  have hprod : 1048576 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    obtain ⟨q,hq⟩ := hpow
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hdiv : 1048576 ∣ k+(j+3*m+5) := by
    rw [hstop]
    exact hprod
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hmod' : (k+(319+512*u)+3*m+5)%1048576=0 := by
    simpa [hjEq, Nat.add_assoc] using hmod
  have hKcong : (106*(319+512*u)+57*k)%1048576=355300 :=
    q_highstop_mod u m k (by simpa [u] using hm) hmod'
  have hkmod : k%1024=574 := q_highstop_k_mod u k hKcong
  let v := k/1024
  have hkv : k=574+1024*v := by
    have hd := Nat.mod_add_div k 1024
    dsimp [v]
    omega
  have hqeven : (53*u+57*v)%1024=282 := by
    rw [hkv] at hKcong
    omega
  have hsum : (u+v)%4=2 := by omega
  let t := (u+v-2)/4
  have ht : u+v=2+4*t := by dsimp [t]; omega
  have hblank := q_even_image_blank_unreachable_uv u v t time ht hqeven
  have hx : 2*j+3=641+1024*u := by rw [hjEq]; omega
  intro hrun
  apply hblank
  rw [hx,hkv] at hrun
  exact hrun

theorem s2_high_parameter_not_CReach (j m : Nat)
    (hj : j%512=319)
    (hm : m%131072=(72746+75264*(j/512))%131072) :
    ¬ BB6.Agent3.CReach (2*j+3) (highK j m) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact s2_high_parameter_no_blank j m time hj hm hrun

theorem q_even_high_parameter_not_CReach (j m : Nat)
    (hj : j%512=319)
    (hm : m%1048576=(531498+337408*(j/512))%1048576) :
    ¬ BB6.Agent3.CReach (2*j+3) (highK j m) := by
  intro hreach
  rcases hreach with ⟨time,hrun⟩
  exact q_even_high_parameter_no_blank j m time hj hm hrun

/-- The S2 and q-even high-stop cylinders are disjoint. -/
theorem s2_q_even_parameter_classes_disjoint (j m : Nat)
    (hs : m%131072=(72746+75264*(j/512))%131072)
    (hq : m%1048576=(531498+337408*(j/512))%1048576) : False := by
  have hdiv : 131072∣1048576 := by decide
  have hmod : m%131072=(m%1048576)%131072 :=
    (Nat.mod_mod_of_dvd m hdiv).symm
  rw [hs,hq] at hmod
  omega

#print axioms s2_parameter_pullback_iff
#print axioms q_even_parameter_pullback_iff
#print axioms s2_high_parameter_no_blank
#print axioms s2_high_parameter_not_CReach
#print axioms q_even_image_blank_unreachable_uv
#print axioms q_even_high_parameter_no_blank
#print axioms q_even_high_parameter_not_CReach
#print axioms s2_q_even_parameter_classes_disjoint

end BB6.Agent34S2Pullback
