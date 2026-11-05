import CylinderPower
import GenericBlocked11
import ShadowFiniteInvariant11
import ShadowFeederRoots
import ShadowQ29DepthSource
import ShadowNoExceptionalGeneral
import MediumConeReach
import ShortConeBridge
import P1TwoSector

namespace BB6.Agent8Generic11
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Shadow
open BB6.Agent1ShortCone BB6.Agent45TwoRoot BB6.Agent4Cone BB6.Agent8Cylinder

/-- Source-authentic affine graph witness for feeder L0, any q>=29. -/
theorem g0_witness
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m:Nat) (hcone:OddCone (4*u-4) (4*u+9) b d m)
    (hb4:b%4=0) :
    ∃ w z alpha, (m,z)∈nodes ∧ 0<z ∧ 4≤w ∧
      16*q+8+m=w+z ∧ 2^m*(b+4*w)=alpha*2^(16*q) := by
  obtain ⟨hrootmass,henc,_,_⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  exact finite_shadow_invariant_lifts_full_cone11
    (16*q) (16*q+8) (4*u-4) (4*u+9)
    (4*q+4) (12*q+4) 28 nodes
    hrootmass (by omega) (by omega)
    (by omega) (by omega) (by omega) henc
    hrootIn hclosed hsmall hnodiv b d m hcone hb4

theorem g0_cost
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m:Nat) (hcone:OddCone (4*u-4) (4*u+9) b d m)
    (hb4:b%4=0) : m≤11 := by
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    g0_witness q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  exact hsmall m z hmem

theorem g0_depth
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m t k c:Nat) (hcone:OddCone (4*u-4) (4*u+9) b d m)
    (hb4:b%4=0) (hi:inverseAt b d t=some (k,c)) : t≤8 := by
  obtain ⟨w,z,alpha,hmem,_,_,hoff,hscaled⟩ :=
    g0_witness q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have hmass0 := odd_cone_mass (4*u-4) (4*u+9) b d m hcone
  have hroot := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hmass : b+d+2*m+2*(16*q+8)+3=56*2^(16*q) := by omega
  have hm : m≤11 := hsmall m z hmem
  exact source_depth_le8_mod256
    (16*q) (16*q+8) m b d w z alpha t k c
    hmass hoff hscaled (by omega) (by omega) (hnodiv m z hmem) hi

theorem g0_width
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m:Nat) (hcone:OddCone (4*u-4) (4*u+9) b d m)
    (hb4:b%4=0) : 24≤b := by
  have hm := g0_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have hleft := odd_cone_left_bound (4*u-4) (4*u+9) b d m hcone
  have hpow : (2:Nat)^m≤2^11 := Nat.pow_le_pow_right (by decide) hm
  have hscaled : 2^m*(b+12)≤2^11*(b+12) :=
    Nat.mul_le_mul_right (b+12) hpow
  have heq : (4*u-4)+12=4*u+8 := by omega
  have hg := pow16_ge_linear q (by omega)
  have hwide : 2^11*36 < 4*u+8 := by omega
  by_cases hb : 24≤b
  · exact hb
  exfalso
  have hupper : b+12≤36 := by omega
  have hscaled2 : 2^11*(b+12)≤2^11*36 := Nat.mul_le_mul_left _ hupper
  omega

theorem g0_no_one
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m t k:Nat) (hcone:OddCone (4*u-4) (4*u+9) b d m)
    (hb4:b%4=0) (hi:inverseAt b d t=some (k,1)) : False := by
  have hm := g0_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have ht := g0_depth q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m t k 1 hcone hb4 hi
  have hmass0 := odd_cone_mass (4*u-4) (4*u+9) b d m hcone
  have hroot := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hmass : b+d+2*m+2*(16*q+8)+3=56*2^(16*q) := by omega
  have hbig := pow16_dominates_hub q m 8 hq hm (by omega)
  have hshift := shifted_gt_power (16*q) (16*q+8) m b d
     hmass (by exact hbig.1) (by omega)
  have hpow := inverseAt_power b d t k 1 hi
  have ht2 : 2^t≤2^8 := Nat.pow_le_pow_right (by decide) ht
  have hsmall2 : d+b/2+3≤1024 := by omega
  have hn : 1024<2^(16*q) := hbig.2
  omega

theorem g0_no_even
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (hu2:u=u2 q)
    (b d m t k c j:Nat) (hcone:OddCone (4*u-4) (4*u+9) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0):
    2*k+8≠14*2^j := by
  have hm := g0_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have ht := g0_depth q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m t k c hcone hb4 hi
  have hcost : m+t+1≤15*q := by omega
  have hcone' : OddCone (if true then 4*u2 q-4 else 6*u2 q-2)
                         (if true then 4*u2 q+9 else 2*u2 q+5) b d m := by
    simpa [hu2] using hcone
  exact medium_root_even_not_power q b d m t k c j true
    (by omega) (by simpa using hcone') hb hb4 hd hi hc hcost

theorem g0_blocked
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,12*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (hu2:u=u2 q)
    (hb4:(4*u-4)%4=0) (hdodd:(4*u+9)%2=1):
    Blocked (4*u-4) (4*u+9) := by
  apply blocked_of_uniform_cone_exit11 (4*u-4) (4*u+9)
  · intro b d m hcone hb
    exact g0_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb
  · intro b d m hcone hb
    exact g0_width q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb
  · intro b d m t k hcone hb hi
    exact g0_no_one q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m t k hcone hb hi
  · intro b d m t k c j hcone hb hb4 hd hi hc
    exact g0_no_even q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv hu2 b d m t k c j hcone hb hb4 hd hi hc
  · exact hb4
  · exact hdodd

/-- Source-authentic affine graph witness for feeder L1, any q>=29. -/
theorem g1_witness
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m:Nat) (hcone:OddCone (6*u-2) (2*u+5) b d m)
    (hb4:b%4=0) :
    ∃ w z alpha, (m,z)∈nodes ∧ 0<z ∧ 4≤w ∧
      16*q+9+m=w+z ∧ 2^m*(b+4*w)=alpha*2^(16*q) := by
  obtain ⟨_,_,hrootmass,henc⟩ :=
    two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  exact finite_shadow_invariant_lifts_full_cone11
    (16*q) (16*q+9) (6*u-2) (2*u+5)
    (6*q+5) (10*q+4) 42 nodes
    hrootmass (by omega) (by omega)
    (by omega) (by omega) (by omega) henc
    hrootIn hclosed hsmall hnodiv b d m hcone hb4

theorem g1_cost
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m:Nat) (hcone:OddCone (6*u-2) (2*u+5) b d m)
    (hb4:b%4=0) : m≤11 := by
  obtain ⟨w,z,alpha,hmem,_,_,_,_⟩ :=
    g1_witness q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  exact hsmall m z hmem

theorem g1_depth
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m t k c:Nat) (hcone:OddCone (6*u-2) (2*u+5) b d m)
    (hb4:b%4=0) (hi:inverseAt b d t=some (k,c)) : t≤8 := by
  obtain ⟨w,z,alpha,hmem,_,_,hoff,hscaled⟩ :=
    g1_witness q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have hmass0 := odd_cone_mass (6*u-2) (2*u+5) b d m hcone
  have hroot := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hmass : b+d+2*m+2*(16*q+9)+3=56*2^(16*q) := by omega
  have hm : m≤11 := hsmall m z hmem
  exact source_depth_le8_mod256
    (16*q) (16*q+9) m b d w z alpha t k c
    hmass hoff hscaled (by omega) (by omega) (hnodiv m z hmem) hi

theorem g1_width
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m:Nat) (hcone:OddCone (6*u-2) (2*u+5) b d m)
    (hb4:b%4=0) : 24≤b := by
  have hm := g1_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have hleft := odd_cone_left_bound (6*u-2) (2*u+5) b d m hcone
  have hpow : (2:Nat)^m≤2^11 := Nat.pow_le_pow_right (by decide) hm
  have hscaled : 2^m*(b+12)≤2^11*(b+12) :=
    Nat.mul_le_mul_right (b+12) hpow
  have heq : (6*u-2)+12=6*u+10 := by omega
  have hg := pow16_ge_linear q (by omega)
  have hwide : 2^11*36 < 6*u+10 := by omega
  by_cases hb : 24≤b
  · exact hb
  exfalso
  have hupper : b+12≤36 := by omega
  have hscaled2 : 2^11*(b+12)≤2^11*36 := Nat.mul_le_mul_left _ hupper
  omega

theorem g1_no_one
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (b d m t k:Nat) (hcone:OddCone (6*u-2) (2*u+5) b d m)
    (hb4:b%4=0) (hi:inverseAt b d t=some (k,1)) : False := by
  have hm := g1_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have ht := g1_depth q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m t k 1 hcone hb4 hi
  have hmass0 := odd_cone_mass (6*u-2) (2*u+5) b d m hcone
  have hroot := two_feeder_root_arithmetic q u (2^(16*q)) hu hu1
  have hmass : b+d+2*m+2*(16*q+9)+3=56*2^(16*q) := by omega
  have hbig := pow16_dominates_hub q m 9 hq hm (by omega)
  have hshift := shifted_gt_power (16*q) (16*q+9) m b d
     hmass (by exact hbig.1) (by omega)
  have hpow := inverseAt_power b d t k 1 hi
  have ht2 : 2^t≤2^8 := Nat.pow_le_pow_right (by decide) ht
  have hsmall2 : d+b/2+3≤1024 := by omega
  have hn : 1024<2^(16*q) := hbig.2
  omega

theorem g1_no_even
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (hu2:u=u2 q)
    (b d m t k c j:Nat) (hcone:OddCone (6*u-2) (2*u+5) b d m)
    (hb:8≤b) (hb4:b%4=0) (hd:d%2=1)
    (hi:inverseAt b d t=some (k,c)) (hc:c%2=0):
    2*k+8≠14*2^j := by
  have hm := g1_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb4
  have ht := g1_depth q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m t k c hcone hb4 hi
  have hcost : m+t+1≤15*q := by omega
  have hcone' : OddCone (if false then 4*u2 q-4 else 6*u2 q-2)
                         (if false then 4*u2 q+9 else 2*u2 q+5) b d m := by
    simpa [hu2] using hcone
  exact medium_root_even_not_power q b d m t k c j false
    (by omega) (by simpa using hcone') hb hb4 hd hi hc hcost

theorem g1_blocked
    (q u : Nat) (hq:29≤q) (hu:u+4*q+3=7*2^(16*q)) (hu1:1≤u)
    (nodes : List (Nat × Nat))
    (hrootIn:(0,10*q+4)∈nodes)
    (hclosed:∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes)
    (hsmall:∀ m z,(m,z)∈nodes→m≤11)
    (hnodiv:∀ m z,(m,z)∈nodes→¬256∣z)
    (hu2:u=u2 q)
    (hb4:(6*u-2)%4=0) (hdodd:(2*u+5)%2=1):
    Blocked (6*u-2) (2*u+5) := by
  apply blocked_of_uniform_cone_exit11 (6*u-2) (2*u+5)
  · intro b d m hcone hb
    exact g1_cost q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb
  · intro b d m hcone hb
    exact g1_width q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m hcone hb
  · intro b d m t k hcone hb hi
    exact g1_no_one q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv b d m t k hcone hb hi
  · intro b d m t k c j hcone hb hb4 hd hi hc
    exact g1_no_even q u hq hu hu1 nodes hrootIn hclosed hsmall hnodiv hu2 b d m t k c j hcone hb hb4 hd hi hc
  · exact hb4
  · exact hdodd

#print axioms g0_blocked
#print axioms g1_blocked
end BB6.Agent8Generic
