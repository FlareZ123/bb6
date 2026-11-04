import P1InverseFixed
import ConeKernel
import P1Gate

set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

namespace BB6.Agent8P1Exponent14
open BB6.Agent4Cone BB6.Agent47P1 BB6.P1Reduction

private theorem power_growth (t : Nat) :
    1025*t+114688 ≤ 7*2^(t+14) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have hstep : (2:Nat)^(t+1+14) = 2*2^(t+14) := by
      rw [show t+1+14=(t+14)+1 by omega, Nat.pow_succ]
      omega
    rw [hstep]
    omega

theorem n_le_w_plus14 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) : n≤w+14 := by
  have hx := power_growth (n-14)
  have hn14 : n-14+14=n := by omega
  rw [hn14] at hx
  omega

private theorem band_not_power (n x : Nat)
    (hl : 7*2^n < x+12) (hu : x+12 < 14*2^n) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  intro j he
  by_cases hj : j<n
  · have hp : 2^(j+1)≤(2:Nat)^n :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    omega
  · have hp : 2^n≤(2:Nat)^j :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

private theorem interval_not_power (n w a b : Nat)
    (hn : 14≤n) (hform : n+114674+1024*w=7*2^n)
    (ha : 1026 ≤ a) (ha2 : a≤2047)
    (hb : 114690 ≤ b) (hb2 : b≤229330) :
    ∀ j : Nat, a*w+b+12 ≠14*2^j := by
  have hnle := n_le_w_plus14 n w hn hform
  have hal := Nat.mul_le_mul_right w ha
  have hau := Nat.mul_le_mul_right w ha2
  have hl : 7*2^n < a*w+b+12 := by omega
  have hu : a*w+b+12 <14*2^n := by omega
  exact band_not_power n (a*w+b) hl hu

private theorem cone_root_0_0_2_0_0_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (200*w+22384) (1848*w+206935) := by
  have h0 : inverseAt (200*w+22384) (1848*w+206935) 0 = some (50*w+5595, 1948*w+218127) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (200*w+22384) (1848*w+206935) 1 = some (537*w+60127, 974*w+109062) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1948*w+218127 ∧ (1948*w+218127)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1848*w+206935)+(200*w+22384)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (200*w+22384) (1848*w+206935) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(50*w+5595, 1948*w+218127) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(537*w+60127, 974*w+109062) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (200*w+22384) (1848*w+206935) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(50*w+5595, 1948*w+218127) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 100*w+11186 := by omega
      have hy : c+4 = 1948*w+218131 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(537*w+60127, 974*w+109062) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1074*w+120250 := by omega
      have hy : c+4 = 974*w+109066 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0_0_2_0_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (400*w+44780) (1648*w+184541) := by
  have h0 : inverseAt (400*w+44780) (1648*w+184541) 0 = some (100*w+11194, 1848*w+206931) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (400*w+44780) (1648*w+184541) 1 = some (562*w+62927, 924*w+103464) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1848*w+206931 ∧ (1848*w+206931)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1648*w+184541)+(400*w+44780)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (400*w+44780) (1648*w+184541) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(100*w+11194, 1848*w+206931) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(562*w+62927, 924*w+103464) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (400*w+44780) (1648*w+184541) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(100*w+11194, 1848*w+206931) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 200*w+22384 := by omega
      have hy : c+4 = 1848*w+206935 := by omega
      rw [hx,hy]
      exact cone_root_0_0_2_0_0_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(562*w+62927, 924*w+103464) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1124*w+125850 := by omega
      have hy : c+4 = 924*w+103468 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0_0_2_0_1 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (1224*w+137048) (824*w+92271) := by
  have h0 : inverseAt (1224*w+137048) (824*w+92271) 0 = some (306*w+34261, 1436*w+160795) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (1224*w+137048) (824*w+92271) 1 = some (665*w+74460, 718*w+80396) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1436*w+160795 ∧ (1436*w+160795)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((824*w+92271)+(1224*w+137048)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1224*w+137048) (824*w+92271) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(306*w+34261, 1436*w+160795) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(665*w+74460, 718*w+80396) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1224*w+137048) (824*w+92271) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(306*w+34261, 1436*w+160795) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 612*w+68518 := by omega
      have hy : c+4 = 1436*w+160799 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(665*w+74460, 718*w+80396) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1330*w+148916 := by omega
      have hy : c+4 = 718*w+80400 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1330 148916 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0_0_2_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (800*w+89572) (1248*w+139751) := by
  have h0 : inverseAt (800*w+89572) (1248*w+139751) 0 = some (200*w+22392, 1648*w+184537) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (800*w+89572) (1248*w+139751) 1 = some (612*w+68526, 824*w+92267) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1648*w+184537 ∧ (1648*w+184537)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h2 : inverseAt (800*w+89572) (1248*w+139751) 2 = some (818*w+91593, 412*w+46132) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 824*w+92267 ∧ (824*w+92267)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1248*w+139751)+(800*w+89572)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (800*w+89572) (1248*w+139751) k 1 2 hk hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0case | h1case | h2case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(200*w+22392, 1648*w+184537) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(612*w+68526, 824*w+92267) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(818*w+91593, 412*w+46132) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (800*w+89572) (1248*w+139751) k c 2 h hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0case | h1case | h2case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(200*w+22392, 1648*w+184537) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 400*w+44780 := by omega
      have hy : c+4 = 1648*w+184541 := by omega
      rw [hx,hy]
      exact cone_root_0_0_2_0_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(612*w+68526, 824*w+92267) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1224*w+137048 := by omega
      have hy : c+4 = 824*w+92271 := by omega
      rw [hx,hy]
      exact cone_root_0_0_2_0_1 n w hn hform
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(818*w+91593, 412*w+46132) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1636*w+183182 := by omega
      have hy : c+4 = 412*w+46136 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_2_0_0_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (224*w+25072) (1824*w+204251) := by
  have h0 : inverseAt (224*w+25072) (1824*w+204251) 0 = some (56*w+6267, 1936*w+216787) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (224*w+25072) (1824*w+204251) 1 = some (540*w+60464, 968*w+108392) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1936*w+216787 ∧ (1936*w+216787)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1824*w+204251)+(224*w+25072)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (224*w+25072) (1824*w+204251) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(56*w+6267, 1936*w+216787) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(540*w+60464, 968*w+108392) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (224*w+25072) (1824*w+204251) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(56*w+6267, 1936*w+216787) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 112*w+12530 := by omega
      have hy : c+4 = 1936*w+216791 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(540*w+60464, 968*w+108392) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1080*w+120924 := by omega
      have hy : c+4 = 968*w+108396 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1080 120924 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0_0_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (256*w+28656) (1792*w+200673) := by
  have h0 : inverseAt (256*w+28656) (1792*w+200673) 0 = some (64*w+7163, 1920*w+215001) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (256*w+28656) (1792*w+200673) 1 = some (544*w+60913, 960*w+107499) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1920*w+215001 ∧ (1920*w+215001)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h2 : inverseAt (256*w+28656) (1792*w+200673) 2 = some (784*w+87788, 480*w+53748) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 960*w+107499 ∧ (960*w+107499)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1792*w+200673)+(256*w+28656)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (256*w+28656) (1792*w+200673) k 1 2 hk hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0case | h1case | h2case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(64*w+7163, 1920*w+215001) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(544*w+60913, 960*w+107499) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(784*w+87788, 480*w+53748) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (256*w+28656) (1792*w+200673) k c 2 h hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0case | h1case | h2case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(64*w+7163, 1920*w+215001) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 128*w+14322 := by omega
      have hy : c+4 = 1920*w+215005 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(544*w+60913, 960*w+107499) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1088*w+121822 := by omega
      have hy : c+4 = 960*w+107503 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(784*w+87788, 480*w+53748) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1568*w+175572 := by omega
      have hy : c+4 = 480*w+53752 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1568 175572 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0_0_2 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (1600*w+179156) (448*w+50169) := by
  have h0 : inverseAt (1600*w+179156) (448*w+50169) 0 = some (400*w+44788, 1248*w+139747) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (1600*w+179156) (448*w+50169) 1 = some (712*w+79725, 624*w+69872) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1248*w+139747 ∧ (1248*w+139747)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((448*w+50169)+(1600*w+179156)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1600*w+179156) (448*w+50169) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(400*w+44788, 1248*w+139747) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(712*w+79725, 624*w+69872) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1600*w+179156) (448*w+50169) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(400*w+44788, 1248*w+139747) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 800*w+89572 := by omega
      have hy : c+4 = 1248*w+139751 := by omega
      rw [hx,hy]
      exact cone_root_0_0_2_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(712*w+79725, 624*w+69872) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1424*w+159446 := by omega
      have hy : c+4 = 624*w+69876 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_2_0_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (448*w+50156) (1600*w+179169) := by
  have h0 : inverseAt (448*w+50156) (1600*w+179169) 0 = some (112*w+12538, 1824*w+204247) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (448*w+50156) (1600*w+179169) 1 = some (568*w+63600, 912*w+102122) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1824*w+204247 ∧ (1824*w+204247)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1600*w+179169)+(448*w+50156)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (448*w+50156) (1600*w+179169) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(112*w+12538, 1824*w+204247) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(568*w+63600, 912*w+102122) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (448*w+50156) (1600*w+179169) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(112*w+12538, 1824*w+204247) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 224*w+25072 := by omega
      have hy : c+4 = 1824*w+204251 := by omega
      rw [hx,hy]
      exact cone_root_2_0_0_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(568*w+63600, 912*w+102122) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1136*w+127196 := by omega
      have hy : c+4 = 912*w+102126 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1136 127196 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_2_0_2 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (1648*w+184528) (400*w+44793) := by
  have h0 : inverseAt (1648*w+184528) (400*w+44793) 0 = some (412*w+46131, 1224*w+137057) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (1648*w+184528) (400*w+44793) 1 = some (718*w+80395, 612*w+68527) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1224*w+137057 ∧ (1224*w+137057)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h2 : inverseAt (1648*w+184528) (400*w+44793) 2 = some (871*w+97527, 306*w+34262) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 612*w+68527 ∧ (612*w+68527)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((400*w+44793)+(1648*w+184528)/2+3)%2^(2+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1648*w+184528) (400*w+44793) k 1 2 hk hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0case | h1case | h2case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(412*w+46131, 1224*w+137057) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(718*w+80395, 612*w+68527) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(871*w+97527, 306*w+34262) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1648*w+184528) (400*w+44793) k c 2 h hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0case | h1case | h2case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(412*w+46131, 1224*w+137057) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 824*w+92258 := by omega
      have hy : c+4 = 1224*w+137061 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(718*w+80395, 612*w+68527) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1436*w+160786 := by omega
      have hy : c+4 = 612*w+68531 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(871*w+97527, 306*w+34262) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1742*w+195050 := by omega
      have hy : c+4 = 306*w+34266 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (512*w+57324) (1536*w+172007) := by
  have h0 : inverseAt (512*w+57324) (1536*w+172007) 0 = some (128*w+14330, 1792*w+200669) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (512*w+57324) (1536*w+172007) 1 = some (576*w+64497, 896*w+100333) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1792*w+200669 ∧ (1792*w+200669)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h2 : inverseAt (512*w+57324) (1536*w+172007) 2 = some (800*w+89580, 448*w+50165) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 896*w+100333 ∧ (896*w+100333)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h3 : inverseAt (512*w+57324) (1536*w+172007) 3 = some (912*w+102121, 224*w+25081) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 448*w+50165 ∧ (448*w+50165)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h4 : inverseAt (512*w+57324) (1536*w+172007) 4 = some (968*w+108391, 112*w+12539) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 224*w+25081 ∧ (224*w+25081)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h5 : inverseAt (512*w+57324) (1536*w+172007) 5 = some (996*w+111526, 56*w+6268) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ 112*w+12539 ∧ (112*w+12539)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1536*w+172007)+(512*w+57324)/2+3)%2^(5+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (512*w+57324) (1536*w+172007) k 1 5 hk hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0case | h1case | h2case | h3case | h4case | h5case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(128*w+14330, 1792*w+200669) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(576*w+64497, 896*w+100333) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(800*w+89580, 448*w+50165) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(912*w+102121, 224*w+25081) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(968*w+108391, 112*w+12539) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=(996*w+111526, 56*w+6268) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (512*w+57324) (1536*w+172007) k c 5 h hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0case | h1case | h2case | h3case | h4case | h5case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(128*w+14330, 1792*w+200669) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 256*w+28656 := by omega
      have hy : c+4 = 1792*w+200673 := by omega
      rw [hx,hy]
      exact cone_root_0_0_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(576*w+64497, 896*w+100333) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1152*w+128990 := by omega
      have hy : c+4 = 896*w+100337 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(800*w+89580, 448*w+50165) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1600*w+179156 := by omega
      have hy : c+4 = 448*w+50169 := by omega
      rw [hx,hy]
      exact cone_root_0_0_2 n w hn hform
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(912*w+102121, 224*w+25081) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1824*w+204238 := by omega
      have hy : c+4 = 224*w+25085 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(968*w+108391, 112*w+12539) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1936*w+216778 := by omega
      have hy : c+4 = 112*w+12543 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h5] at hval
      have hp : (k,c)=(996*w+111526, 56*w+6268) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1992*w+223048 := by omega
      have hy : c+4 = 56*w+6272 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1992 223048 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_2_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (896*w+100324) (1152*w+129003) := by
  have h0 : inverseAt (896*w+100324) (1152*w+129003) 0 = some (224*w+25080, 1600*w+179165) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (896*w+100324) (1152*w+129003) 1 = some (624*w+69871, 800*w+89581) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1600*w+179165 ∧ (1600*w+179165)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h2 : inverseAt (896*w+100324) (1152*w+129003) 2 = some (824*w+92266, 400*w+44789) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 800*w+89581 ∧ (800*w+89581)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h3 : inverseAt (896*w+100324) (1152*w+129003) 3 = some (924*w+103463, 200*w+22393) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 400*w+44789 ∧ (400*w+44789)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h4 : inverseAt (896*w+100324) (1152*w+129003) 4 = some (974*w+109061, 100*w+11195) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 200*w+22393 ∧ (200*w+22393)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h5 : inverseAt (896*w+100324) (1152*w+129003) 5 = some (999*w+111860, 50*w+5596) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ 100*w+11195 ∧ (100*w+11195)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1152*w+129003)+(896*w+100324)/2+3)%2^(5+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (896*w+100324) (1152*w+129003) k 1 5 hk hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0case | h1case | h2case | h3case | h4case | h5case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(224*w+25080, 1600*w+179165) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(624*w+69871, 800*w+89581) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(824*w+92266, 400*w+44789) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(924*w+103463, 200*w+22393) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(974*w+109061, 100*w+11195) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=(999*w+111860, 50*w+5596) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (896*w+100324) (1152*w+129003) k c 5 h hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0case | h1case | h2case | h3case | h4case | h5case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(224*w+25080, 1600*w+179165) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 448*w+50156 := by omega
      have hy : c+4 = 1600*w+179169 := by omega
      rw [hx,hy]
      exact cone_root_2_0_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(624*w+69871, 800*w+89581) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1248*w+139738 := by omega
      have hy : c+4 = 800*w+89585 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(824*w+92266, 400*w+44789) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1648*w+184528 := by omega
      have hy : c+4 = 400*w+44793 := by omega
      rw [hx,hy]
      exact cone_root_2_0_2 n w hn hform
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(924*w+103463, 200*w+22393) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1848*w+206922 := by omega
      have hy : c+4 = 200*w+22397 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(974*w+109061, 100*w+11195) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1948*w+218118 := by omega
      have hy : c+4 = 100*w+11199 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h5] at hval
      have hp : (k,c)=(999*w+111860, 50*w+5596) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1998*w+223716 := by omega
      have hy : c+4 = 50*w+5600 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1998 223716 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_0 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (1024*w+114660) (1024*w+114673) := by
  have h0 : inverseAt (1024*w+114660) (1024*w+114673) 0 = some (256*w+28664, 1536*w+172003) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (1024*w+114660) (1024*w+114673) 1 = some (640*w+71665, 768*w+86000) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1536*w+172003 ∧ (1536*w+172003)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((1024*w+114673)+(1024*w+114660)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1024*w+114660) (1024*w+114673) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(256*w+28664, 1536*w+172003) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(640*w+71665, 768*w+86000) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1024*w+114660) (1024*w+114673) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(256*w+28664, 1536*w+172003) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 512*w+57324 := by omega
      have hy : c+4 = 1536*w+172007 := by omega
      rw [hx,hy]
      exact cone_root_0_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(640*w+71665, 768*w+86000) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1280*w+143326 := by omega
      have hy : c+4 = 768*w+86004 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_2 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (1792*w+200660) (256*w+28669) := by
  have h0 : inverseAt (1792*w+200660) (256*w+28669) 0 = some (448*w+50164, 1152*w+128999) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (1792*w+200660) (256*w+28669) 1 = some (736*w+82414, 576*w+64498) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1152*w+128999 ∧ (1152*w+128999)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((256*w+28669)+(1792*w+200660)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1792*w+200660) (256*w+28669) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(448*w+50164, 1152*w+128999) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(736*w+82414, 576*w+64498) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1792*w+200660) (256*w+28669) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(448*w+50164, 1152*w+128999) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 896*w+100324 := by omega
      have hy : c+4 = 1152*w+129003 := by omega
      rw [hx,hy]
      exact cone_root_2_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(736*w+82414, 576*w+64498) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1472*w+164824 := by omega
      have hy : c+4 = 576*w+64502 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact interval_not_power n w 1472 164824 hn hform (by omega) (by omega) (by omega) (by omega)

private theorem cone_root_3 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (1920*w+214992) (128*w+14335) := by
  have h0 : inverseAt (1920*w+214992) (128*w+14335) 0 = some (480*w+53747, 1088*w+121831) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (1920*w+214992) (128*w+14335) 1 = some (752*w+84205, 544*w+60914) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1088*w+121831 ∧ (1088*w+121831)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((128*w+14335)+(1920*w+214992)/2+3)%2^(1+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1920*w+214992) (128*w+14335) k 1 1 hk hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(480*w+53747, 1088*w+121831) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(752*w+84205, 544*w+60914) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (1920*w+214992) (128*w+14335) k c 1 h hnmod
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0case | h1case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(480*w+53747, 1088*w+121831) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 960*w+107490 := by omega
      have hy : c+4 = 1088*w+121835 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(752*w+84205, 544*w+60914) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1504*w+168406 := by omega
      have hy : c+4 = 544*w+60918 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem cone_root (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    Blocked (2048*w+229332) (3) := by
  have h0 : inverseAt (2048*w+229332) (3) 0 = some (512*w+57332, 1024*w+114669) := by
    simp [inverseAt]
    omega
  have h1 : inverseAt (2048*w+229332) (3) 1 = some (768*w+85999, 512*w+57333) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1024*w+114669 ∧ (1024*w+114669)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h2 : inverseAt (2048*w+229332) (3) 2 = some (896*w+100332, 256*w+28665) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 512*w+57333 ∧ (512*w+57333)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h3 : inverseAt (2048*w+229332) (3) 3 = some (960*w+107498, 128*w+14331) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 256*w+28665 ∧ (256*w+28665)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have h4 : inverseAt (2048*w+229332) (3) 4 = some (992*w+111081, 64*w+7164) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 128*w+14331 ∧ (128*w+14331)%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hnmod : ((3)+(2048*w+229332)/2+3)%2^(4+1) ≠ 0 := by omega
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2048*w+229332) (3) k 1 4 hk hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0case | h1case | h2case | h3case | h4case
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(512*w+57332, 1024*w+114669) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(768*w+85999, 512*w+57333) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(896*w+100332, 256*w+28665) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(960*w+107498, 128*w+14331) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(992*w+111081, 64*w+7164) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod (2048*w+229332) (3) k c 4 h hnmod
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0case | h1case | h2case | h3case | h4case
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(512*w+57332, 1024*w+114669) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1024*w+114660 := by omega
      have hy : c+4 = 1024*w+114673 := by omega
      rw [hx,hy]
      exact cone_root_0 n w hn hform
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(768*w+85999, 512*w+57333) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1536*w+171994 := by omega
      have hy : c+4 = 512*w+57337 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(896*w+100332, 256*w+28665) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1792*w+200660 := by omega
      have hy : c+4 = 256*w+28669 := by omega
      rw [hx,hy]
      exact cone_root_2 n w hn hform
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(960*w+107498, 128*w+14331) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1920*w+214992 := by omega
      have hy : c+4 = 128*w+14335 := by omega
      rw [hx,hy]
      exact cone_root_3 n w hn hform
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(992*w+111081, 64*w+7164) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1984*w+222158 := by omega
      have hy : c+4 = 64*w+7168 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)


theorem no_root_14mod1024 (n w : Nat) (hn : 14≤n)
    (hform : n+114674+1024*w=7*2^n) :
    ¬ BB6.Agent1.Reach (2048*w+229332) 3 :=
  blocked_no_reach _ _ (cone_root n w hn hform)


private theorem critical_pow_nonneg (n : Nat) (hn : 14 ≤ n) :
    n+114674 ≤ 7*2^n := by
  have hx := power_growth (n-14)
  have hn14 : n-14+14=n := by omega
  rw [hn14] at hx
  omega

/-- Each critical exponent n congruent to 14 modulo 1024 lies on the
    explicit affine root line whose entire inverse tree is blocked. -/
theorem exists_w_at_critical_residue (n : Nat) (hn : 14≤n)
    (hmod : n%1024=14) :
    ∃ w, n+114674+1024*w=7*2^n := by
  have hlarge := critical_pow_nonneg n hn
  have hpowdiv : 1024 ∣ (2:Nat)^n := by
    have hp : 2^10 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 (by omega)
    simpa [show (2:Nat)^10=1024 by decide] using hp
  have hpowmod : (7*2^n)%1024=0 := by
    have hp : 1024 ∣ (7*(2:Nat)^n) := by
      obtain ⟨q,hq⟩ := hpowdiv
      exact ⟨7*q, by rw [hq]; omega⟩
    exact Nat.dvd_iff_mod_eq_zero.mp hp
  have humod : (n+114674)%1024=0 := by omega
  have hdiffmod : (7*2^n-(n+114674))%1024=0 := by omega
  let w := (7*2^n-(n+114674))/1024
  have hm := Nat.mod_add_div (7*2^n-(n+114674)) 1024
  refine ⟨w, ?_⟩
  dsimp [w]
  omega

/-- Uniform true-blank critical-hub nonreachability for infinitely many
    remaining n=14(mod 1024) exponents, using unchanged source Reach. -/
theorem no_critical_14_mod1024 (n : Nat) (hn : 14 ≤ n)
    (hmod : n%1024=14) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  obtain ⟨w,hform⟩ := exists_w_at_critical_residue n hn hmod
  let d := 14*2^n-2*n-10
  have hdform : d=229338+2048*w := by dsimp [d]; omega
  have hdlarge : 10≤d := by omega
  have hdmod : d%4=2 := by rw [hdform]; omega
  intro hreach
  have hthree : BB6.Agent1.Reach (d-6) 3 :=
    BB6.Agent50P1.critical_target_implies_three d hdlarge hdmod hreach
  have hdec : d-6=2048*w+229332 := by omega
  rw [hdec] at hthree
  exact no_root_14mod1024 n w hn hform hthree

#print axioms BB6.Agent8P1Exponent14.exists_w_at_critical_residue
#print axioms BB6.Agent8P1Exponent14.no_critical_14_mod1024

#print axioms BB6.Agent8P1Exponent14.no_root_14mod1024
end BB6.Agent8P1Exponent14
