import BB429No1021Five
import BB429RootMod32
import Lean.Elab.Tactic.Omega

namespace BB429No1021Six
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

private theorem exclude_2045 (q : Nat) :
    ¬ Reach (16384*q+2045) (32768*q+4089) := by
  intro h0
  have h1 : Reach (8192*q+1021) (49152*q+6134) := by
    apply force_first_odd (16384*q+2045) (32768*q+4089) (8192*q+1021) (49152*q+6134)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+509) (57344*q+7155) := by
    apply force_first_odd (8192*q+1021) (49152*q+6134) (4096*q+509) (57344*q+7155)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+253) (61440*q+7664) := by
    apply force_first_odd (4096*q+509) (57344*q+7155) (2048*q+253) (61440*q+7664)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+125) (63488*q+7917) := by
    apply force_first_odd (2048*q+253) (61440*q+7664) (1024*q+125) (63488*q+7917)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+61) (64512*q+8042) := by
    apply force_first_odd (1024*q+125) (63488*q+7917) (512*q+61) (64512*q+8042)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  have h6 : Reach (256*q+29) (65024*q+8103) := by
    apply force_first_odd (512*q+61) (64512*q+8042) (256*q+29) (65024*q+8103)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h5
  have h7 : Reach (128*q+13) (65280*q+8132) := by
    apply force_first_odd (256*q+29) (65024*q+8103) (128*q+13) (65280*q+8132)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h6
  have h8 : Reach (64*q+5) (65408*q+8145) := by
    apply force_first_odd (128*q+13) (65280*q+8132) (64*q+5) (65408*q+8145)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h7
  rcases h8 with ⟨n,hn⟩
  have ha : (64*q+5)%32=5 := by omega
  have hb : (65408*q+8145)%16=1 := by omega
  exact (BB429RootMod32.rooted_not_5_1 n _ _ hn ha) hb

theorem blank_halt_not_2045_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 2045 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+2045 := by dsimp [q]; omega
  have hb : b=32768*q+4089 := by omega
  have h0 : Reach (16384*q+2045) (32768*q+4089) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_2045 q h0

/-- Six distinct universal blank-root terminal exclusions in 1021/1024. -/
theorem blank_halt_not_six_1021_lifts (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384≠2045 ∧ a%16384≠4093 ∧ a%16384≠9213 ∧
      a%16384≠10237 ∧ a%16384≠11261 ∧ a%16384≠12285 := by
  obtain ⟨h4093,h9213,h10237,h11261,h12285⟩ :=
    BB429No1021Five.blank_halt_not_five_1021_lifts n a b hr hg
  exact ⟨blank_halt_not_2045_mod16384 n a b hr hg,
    h4093,h9213,h10237,h11261,h12285⟩

#print axioms blank_halt_not_2045_mod16384
#print axioms blank_halt_not_six_1021_lifts

end BB429No1021Six
