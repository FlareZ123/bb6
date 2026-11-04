import BB429RootMod64R2
import Lean.Elab.Tactic.Omega

namespace BB429No1021Eight
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 15000000

private theorem force_first_odd (a b na nb : Nat)
    (ha : 13≤a) (ho : a%2=1) (hf : a=2*na+3 ∧ nb=b+a)
    (hs : ∀ x y, 4*x+26=4*a+b → 2*y=b+4 → b%4=2 →
      ¬ BB429Mod8.Allowed x y)
    (hr : Reach a b) : Reach na nb := by
  rcases odd_back a b ha ho hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he : x=na ∧ y=nb := by omega
    rcases he with ⟨rfl,rfl⟩
    exact hp
  · exact False.elim (hs x y hx hy hw (reach_allowed x y hp))

private theorem exclude_1021 (q : Nat) :
    ¬ Reach (16384*q+1021) (32768*q+2041) := by
  intro h0
  have h1 : Reach (8192*q+509) (49152*q+3062) := by
    apply force_first_odd (16384*q+1021) (32768*q+2041) (8192*q+509) (49152*q+3062)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+253) (57344*q+3571) := by
    apply force_first_odd (8192*q+509) (49152*q+3062) (4096*q+253) (57344*q+3571)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+125) (61440*q+3824) := by
    apply force_first_odd (4096*q+253) (57344*q+3571) (2048*q+125) (61440*q+3824)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+61) (63488*q+3949) := by
    apply force_first_odd (2048*q+125) (61440*q+3824) (1024*q+61) (63488*q+3949)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+29) (64512*q+4010) := by
    apply force_first_odd (1024*q+61) (63488*q+3949) (512*q+29) (64512*q+4010)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  rcases odd_back (512*q+29) (64512*q+4010)
      (by omega) (by omega) h5 with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x=256*q+13 := by omega
    have ye : y=65024*q+4039 := by omega
    rw [xe,ye] at hp
    rcases odd_back (256*q+13) (65024*q+4039)
        (by omega) (by omega) hp with
        ⟨xx,yy,hpp,hxx,hyy⟩ | ⟨xx,yy,hpp,hxx,hyy,hww⟩
    · exact BB429RootMod64R0.no_5_20 xx yy hpp (by omega) (by omega)
    · omega
  · exact BB429RootMod64R0.no_1_23 x y hp (by omega) (by omega)

theorem blank_halt_not_1021_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 1021 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+1021 := by dsimp [q]; omega
  have hb : b=32768*q+2041 := by omega
  have h0 : Reach (16384*q+1021) (32768*q+2041) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_1021 q h0

private theorem exclude_3069 (q : Nat) :
    ¬ Reach (16384*q+3069) (32768*q+6137) := by
  intro h0
  have h1 : Reach (8192*q+1533) (49152*q+9206) := by
    apply force_first_odd (16384*q+3069) (32768*q+6137) (8192*q+1533) (49152*q+9206)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+765) (57344*q+10739) := by
    apply force_first_odd (8192*q+1533) (49152*q+9206) (4096*q+765) (57344*q+10739)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+381) (61440*q+11504) := by
    apply force_first_odd (4096*q+765) (57344*q+10739) (2048*q+381) (61440*q+11504)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+189) (63488*q+11885) := by
    apply force_first_odd (2048*q+381) (61440*q+11504) (1024*q+189) (63488*q+11885)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+93) (64512*q+12074) := by
    apply force_first_odd (1024*q+189) (63488*q+11885) (512*q+93) (64512*q+12074)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  rcases odd_back (512*q+93) (64512*q+12074)
      (by omega) (by omega) h5 with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have xe : x=256*q+45 := by omega
    have ye : y=65024*q+12167 := by omega
    rw [xe,ye] at hp
    rcases odd_back (256*q+45) (65024*q+12167)
        (by omega) (by omega) hp with
        ⟨xx,yy,hpp,hxx,hyy⟩ | ⟨xx,yy,hpp,hxx,hyy,hww⟩
    · exact BB429RootMod64R2.no_21_20 xx yy hpp (by omega) (by omega)
    · omega
  · exact BB429RootMod64R0.no_33_23 x y hp (by omega) (by omega)

theorem blank_halt_not_3069_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 3069 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+3069 := by dsimp [q]; omega
  have hb : b=32768*q+6137 := by omega
  have h0 : Reach (16384*q+3069) (32768*q+6137) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_3069 q h0

/-- Eight disjoint all-natural rooted terminal exclusions, half of the
sixteen lifts in this formerly unresolved 1021 mod1024 cylinder. -/
theorem blank_halt_not_eight_1021_lifts (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384≠1021 ∧ a%16384≠2045 ∧ a%16384≠3069 ∧
    a%16384≠4093 ∧ a%16384≠9213 ∧ a%16384≠10237 ∧
    a%16384≠11261 ∧ a%16384≠12285 := by
  obtain ⟨h2045,h4093,h9213,h10237,h11261,h12285⟩ :=
    BB429No1021Six.blank_halt_not_six_1021_lifts n a b hr hg
  exact ⟨blank_halt_not_1021_mod16384 n a b hr hg,
    h2045,blank_halt_not_3069_mod16384 n a b hr hg,
    h4093,h9213,h10237,h11261,h12285⟩

#print axioms blank_halt_not_1021_mod16384
#print axioms blank_halt_not_3069_mod16384
#print axioms blank_halt_not_eight_1021_lifts

end BB429No1021Eight
