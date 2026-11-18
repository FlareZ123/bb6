import Std
import SheepPowerH4Source
import PowerGateH5Decision
import SpecialSourceNoPower
import SheepEvenReachInverse
import EvenSourceBridge

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace SheepPowerH5Source

def Gate5 (m : Nat) : Prop :=
  1 ≤ m ∧ m%3≠0 ∧ m%4=0 ∧ m%7≠3 ∧ m%9≠4 ∧ m%15≠11

theorem target_hidden_le5 (m h u : Nat)
    (hm3 : m%3≠0)
    (htarget : (2:Nat)^(162*m)=1+3^h*u) : h≤5 := by
  by_cases hh : h≤5
  · exact hh
  have h6 : 6≤h := by omega
  have hdiv : 729 ∣ 3^h*u := by
    refine ⟨3^(h-6)*u, ?_⟩
    have hsplit : h=6+(h-6) := by omega
    rw [hsplit, Nat.pow_add]
    have hsub : 6+(h-6)-6=h-6 := by omega
    rw [hsub]
    rw [show (3:Nat)^6=729 by decide]
    simp [Nat.mul_assoc]
  have hmod : (2:Nat)^(162*m)%729=1 := by
    rw [htarget, Nat.add_mod]
    have hz : (3^h*u)%729=0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [hz]
  have hperiod : (2:Nat)^486%729=1 := by decide
  have hred := Agent16SheepH4.pow_mod_reduce 729 486 (162*m) (by decide) (by decide) hperiod
  rw [hred] at hmod
  have hexp : (162*m)%486 = 162*(m%3) := by omega
  rw [hexp] at hmod
  have hmres : m%3=1 ∨ m%3=2 := by omega
  rcases hmres with hm1|hm2
  · have hres : (2:Nat)^162%729=244 := by decide
    rw [hm1,hres] at hmod
    omega
  · have hres : (2:Nat)^324%729=487 := by decide
    rw [hm2,hres] at hmod
    omega

theorem blank_even_cannot_hit_gate5 (m : Nat) (hm : Gate5 m) :
    ¬ SheepEven.EvenReach 10 (2^(162*m)) := by
  rcases hm with ⟨hmpos,hm3,hm4,hm7,hm9,hm15⟩
  intro hreach
  have hbig : 10 < (2:Nat)^(162*m) := by
    have hle : (2:Nat)^4 ≤ (2:Nat)^(162*m) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h16 : (2:Nat)^4=16 := by decide
    rw [h16] at hle
    omega
  have hnot : (2:Nat)^(162*m) ≠ 10 := by omega
  rcases SheepEvenReachInverse.blank_even_inverse_cases
      (y := (2:Nat)^(162*m)) (d := 1) (c := 0) (n := 162*m)
      hreach hnot (by simp) with hgen | hspec
  · rcases hgen with ⟨x,a,h,v,u,hreachx,ha,hv,hvo,huo,hx,hy,heq⟩
    have hh : h≤5 := target_hidden_le5 m h u hm3 hy
    by_cases hle4 : h≤4
    · have ht2 : (3*m)%2≠1 := by omega
      have ht4 : (3*m)%4≠2 := by omega
      have ht7 : (3*m)%7≠2 := by
        intro ht
        apply hm7
        omega
      have ht9 : (3*m)%9≠8 := by omega
      have ht15 : (3*m)%15≠7 := by omega
      have hmul : 54*(3*m)=162*m := by omega
      have heq4 : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
          = 2^(54*(3*m)+h+1)+3*3^h := by
        simpa [hmul] using heq
      exact SheepPowerH4Source.no_generic_all_a h a (3*m) v
        hle4 ha ht2 ht4 ht7 ht9 ht15 heq4
    · have h5 : h=5 := by omega
      have hcert : Agent16SheepH5.H5GenericEquation (162*m) a v := by
        dsimp [Agent16SheepH5.H5GenericEquation]
        have heq' := heq
        rw [h5] at heq'
        have hthree : (3:Nat)^5=243 := by decide
        have htwo : (2:Nat)^(5+1)=64 := by decide
        have hthree2 : 3*(3:Nat)^5=729 := by
          calc
            3*(3:Nat)^5 = 3*243 := congrArg (fun x : Nat => 3*x) hthree
            _ = 729 := by decide
        rw [hthree2, hthree, htwo] at heq'
        have hexp : 162*m+5+1=162*m+6 := by omega
        rw [hexp] at heq'
        simp only [Nat.one_mul, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at heq'
        omega
      rcases Agent16SheepH5.generic_h5_source_only (162*m) a v ha hcert with
        ⟨_,hmod⟩ | ⟨_,hmod⟩ | ⟨_,hmod⟩
      · have hmOdd : m%2=1 := by omega
        omega
      · have hmRes : m%9=4 := by omega
        exact hm9 hmRes
      · have hmRes : m%15=11 := by omega
        exact hm15 hmRes
  · rcases hspec with ⟨x,a,h,u,hreachx,ha,hu,hx,hy,heq⟩
    have hpow : (2:Nat)^(162*m+h)=2^h+2^h*3^h*u := by
      rw [Nat.pow_add, hy, Nat.add_mul]
      ac_rfl
    have hEq' : 3^h*(3*2^a+a+2)+2^h=2^(162*m+h) := by
      simpa using heq
    have hcancel : 3^h*(3*2^a+a+2)=2^h*3^h*u := by
      have hsum : 3^h*(3*2^a+a+2)+2^h=2^h+2^h*3^h*u := by
        rw [hEq',hpow]
      omega
    have hmul : 3^h*(3*2^a+a+2)=3^h*(2^h*u) := by
      calc
        3^h*(3*2^a+a+2)=2^h*3^h*u := hcancel
        _ = 3^h*(2^h*u) := by ac_rfl
    have hfactor : 3*2^a+a+2=2^h*u :=
      Nat.mul_left_cancel (Nat.pow_pos (by decide)) hmul
    exact Agent17SheepSpecial.special_no_even_power a h u (162*m)
      ha hfactor hu hy.symm

theorem blank_even_cannot_hit_gate5_source (m : Nat) (hm : Gate5 m) :
    ¬ BB6.Agent22.Sheep.Reach 5 (2^(162*m)) := by
  have hmpos : 1 ≤ m := hm.1
  intro hreach
  obtain ⟨n,hsteps⟩ := BB6.Agent16.SheepEvenSource.reach_to_even_steps hreach
  have he : (2^(162*m))%2=0 := by
    have hexp : 162*m=(162*m-1)+1 := by omega
    rw [hexp, Nat.pow_succ]
    simp
  have hblank : SheepEven.EvenReach 10 (2^(162*m)) :=
    (SheepEven.blank_even_reach_iff he).mp ⟨n,hsteps⟩
  exact blank_even_cannot_hit_gate5 m hm hblank

#print axioms target_hidden_le5
#print axioms blank_even_cannot_hit_gate5
#print axioms blank_even_cannot_hit_gate5_source

end SheepPowerH5Source
