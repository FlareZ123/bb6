import BB429No1021More
import BB429RootMod16
import Lean.Elab.Tactic.Omega

namespace BB429No1021Five
open BB429NewResidue

set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

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

private theorem exclude_4093 (q : Nat) :
    ¬ Reach (16384*q+4093) (32768*q+8185) := by
  intro h0
  have h1 : Reach (8192*q+2045) (49152*q+12278) := by
    apply force_first_odd (16384*q+4093) (32768*q+8185) (8192*q+2045) (49152*q+12278)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+1021) (57344*q+14323) := by
    apply force_first_odd (8192*q+2045) (49152*q+12278) (4096*q+1021) (57344*q+14323)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+509) (61440*q+15344) := by
    apply force_first_odd (4096*q+1021) (57344*q+14323) (2048*q+509) (61440*q+15344)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+253) (63488*q+15853) := by
    apply force_first_odd (2048*q+509) (61440*q+15344) (1024*q+253) (63488*q+15853)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+125) (64512*q+16106) := by
    apply force_first_odd (1024*q+253) (63488*q+15853) (512*q+125) (64512*q+16106)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  have h6 : Reach (256*q+61) (65024*q+16231) := by
    apply force_first_odd (512*q+125) (64512*q+16106) (256*q+61) (65024*q+16231)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h5
  have h7 : Reach (128*q+29) (65280*q+16292) := by
    apply force_first_odd (256*q+61) (65024*q+16231) (128*q+29) (65280*q+16292)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h6
  have h8 : Reach (64*q+13) (65408*q+16321) := by
    apply force_first_odd (128*q+29) (65280*q+16292) (64*q+13) (65408*q+16321)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h7
  have h9 : Reach (32*q+5) (65472*q+16334) := by
    apply force_first_odd (64*q+13) (65408*q+16321) (32*q+5) (65472*q+16334)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h8
  rcases h9 with ⟨n,hn⟩
  have ha : (32*q+5)%16=5 := by omega
  have hb : (65472*q+16334)%8=6 := by omega
  exact (BB429RootMod16.rooted_not_5_6 n _ _ hn ha) hb

theorem blank_halt_not_4093_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 4093 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+4093 := by dsimp [q]; omega
  have hb : b=32768*q+8185 := by omega
  have h0 : Reach (16384*q+4093) (32768*q+8185) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_4093 q h0

private theorem exclude_10237 (q : Nat) :
    ¬ Reach (16384*q+10237) (32768*q+20473) := by
  intro h0
  have h1 : Reach (8192*q+5117) (49152*q+30710) := by
    apply force_first_odd (16384*q+10237) (32768*q+20473) (8192*q+5117) (49152*q+30710)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+2557) (57344*q+35827) := by
    apply force_first_odd (8192*q+5117) (49152*q+30710) (4096*q+2557) (57344*q+35827)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+1277) (61440*q+38384) := by
    apply force_first_odd (4096*q+2557) (57344*q+35827) (2048*q+1277) (61440*q+38384)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+637) (63488*q+39661) := by
    apply force_first_odd (2048*q+1277) (61440*q+38384) (1024*q+637) (63488*q+39661)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+317) (64512*q+40298) := by
    apply force_first_odd (1024*q+637) (63488*q+39661) (512*q+317) (64512*q+40298)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  have h6 : Reach (256*q+157) (65024*q+40615) := by
    apply force_first_odd (512*q+317) (64512*q+40298) (256*q+157) (65024*q+40615)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h5
  have h7 : Reach (128*q+77) (65280*q+40772) := by
    apply force_first_odd (256*q+157) (65024*q+40615) (128*q+77) (65280*q+40772)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h6
  have h8 : Reach (64*q+37) (65408*q+40849) := by
    apply force_first_odd (128*q+77) (65280*q+40772) (64*q+37) (65408*q+40849)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h7
  have h9 : Reach (32*q+17) (65472*q+40886) := by
    apply force_first_odd (64*q+37) (65408*q+40849) (32*q+17) (65472*q+40886)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h8
  rcases h9 with ⟨n,hn⟩
  have ha : (32*q+17)%16=1 := by omega
  have hb : (65472*q+40886)%8=6 := by omega
  exact (BB429RootMod16.rooted_not_1_6 n _ _ hn ha) hb

theorem blank_halt_not_10237_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 10237 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+10237 := by dsimp [q]; omega
  have hb : b=32768*q+20473 := by omega
  have h0 : Reach (16384*q+10237) (32768*q+20473) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_10237 q h0

/-- Five distinct blank-root exclusions in the formerly intact 1021 cylinder. -/
theorem blank_halt_not_five_1021_lifts (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384≠4093 ∧ a%16384≠9213 ∧ a%16384≠10237 ∧
      a%16384≠11261 ∧ a%16384≠12285 := by
  obtain ⟨h9213,h11261,h12285⟩ :=
    BB429No1021.blank_halt_not_three_1021_lifts n a b hr hg
  exact ⟨blank_halt_not_4093_mod16384 n a b hr hg,
    h9213, blank_halt_not_10237_mod16384 n a b hr hg, h11261, h12285⟩

#print axioms blank_halt_not_4093_mod16384
#print axioms blank_halt_not_10237_mod16384
#print axioms blank_halt_not_five_1021_lifts

end BB429No1021Five
