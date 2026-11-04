import BB429No12285mod16384
import Lean.Elab.Tactic.Omega

namespace BB429No1021

open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 32768

private theorem force_odd (a b na nb : Nat)
    (ha : 13 ≤ a) (ho : a%2=1)
    (hf : a=2*na+3 ∧ nb=b+a)
    (hs : ∀ x y, 4*x+26=4*a+b → 2*y=b+4 → b%4=2 →
       ¬ BB429Mod8.Allowed x y)
    (hr : Reach a b) : Reach na nb := by
  rcases odd_back a b ha ho hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have he : x=na ∧ y=nb := by omega
    rcases he with ⟨rfl,rfl⟩
    exact hp
  · exact False.elim (hs x y hx hy hw (reach_allowed x y hp))

/-- A two-stage exceptional inverse arm is also incompatible with blank reach. -/
private theorem no_9213_side (q : Nat) :
    ¬ Reach (16400*q+9207) (32736*q+18399) := by
  intro hr
  rcases odd_back (16400*q+9207) (32736*q+18399)
      (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hxe : x=8200*q+4602 := by omega
    have hye : y=49136*q+27606 := by omega
    rw [hxe,hye] at hp
    obtain ⟨xx,yy,hp2,hxx,hyy,hmod⟩ :=
      even_back (8200*q+4602) (49136*q+27606)
        (by omega) (by omega) hp
    have hallow := reach_allowed xx yy hp2
    unfold BB429Mod8.Allowed at hallow
    omega
  · omega

private theorem no_9213_last (q : Nat) :
    ¬ Reach (32*q+15) (65472*q+36794) := by
  intro hr
  rcases odd_back (32*q+15) (65472*q+36794)
      (by omega) (by omega) hr with
    ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hw⟩
  · have hallow := reach_allowed x y hp
    unfold BB429Mod8.Allowed at hallow
    omega
  · have hxe : x=16400*q+9207 := by omega
    have hye : y=32736*q+18399 := by omega
    rw [hxe,hye] at hp
    exact no_9213_side q hp

private theorem exclude_9213 (q : Nat) :
    ¬ Reach (16384*q+9213) (32768*q+18425) := by
  intro h0
  have h1 : Reach (8192*q+4605) (49152*q+27638) := by
    apply force_odd (16384*q+9213) (32768*q+18425) (8192*q+4605) (49152*q+27638)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+2301) (57344*q+32243) := by
    apply force_odd (8192*q+4605) (49152*q+27638) (4096*q+2301) (57344*q+32243)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+1149) (61440*q+34544) := by
    apply force_odd (4096*q+2301) (57344*q+32243) (2048*q+1149) (61440*q+34544)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+573) (63488*q+35693) := by
    apply force_odd (2048*q+1149) (61440*q+34544) (1024*q+573) (63488*q+35693)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+285) (64512*q+36266) := by
    apply force_odd (1024*q+573) (63488*q+35693) (512*q+285) (64512*q+36266)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  have h6 : Reach (256*q+141) (65024*q+36551) := by
    apply force_odd (512*q+285) (64512*q+36266) (256*q+141) (65024*q+36551)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h5
  have h7 : Reach (128*q+69) (65280*q+36692) := by
    apply force_odd (256*q+141) (65024*q+36551) (128*q+69) (65280*q+36692)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h6
  have h8 : Reach (64*q+33) (65408*q+36761) := by
    apply force_odd (128*q+69) (65280*q+36692) (64*q+33) (65408*q+36761)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h7
  have h9 : Reach (32*q+15) (65472*q+36794) := by
    apply force_odd (64*q+33) (65408*q+36761) (32*q+15) (65472*q+36794)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h8
  exact no_9213_last q h9

private theorem exclude_11261 (q : Nat) :
    ¬ Reach (16384*q+11261) (32768*q+22521) := by
  intro h0
  have h1 : Reach (8192*q+5629) (49152*q+33782) := by
    apply force_odd (16384*q+11261) (32768*q+22521) (8192*q+5629) (49152*q+33782)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h0
  have h2 : Reach (4096*q+2813) (57344*q+39411) := by
    apply force_odd (8192*q+5629) (49152*q+33782) (4096*q+2813) (57344*q+39411)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h1
  have h3 : Reach (2048*q+1405) (61440*q+42224) := by
    apply force_odd (4096*q+2813) (57344*q+39411) (2048*q+1405) (61440*q+42224)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h2
  have h4 : Reach (1024*q+701) (63488*q+43629) := by
    apply force_odd (2048*q+1405) (61440*q+42224) (1024*q+701) (63488*q+43629)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h3
  have h5 : Reach (512*q+349) (64512*q+44330) := by
    apply force_odd (1024*q+701) (63488*q+43629) (512*q+349) (64512*q+44330)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h4
  have h6 : Reach (256*q+173) (65024*q+44679) := by
    apply force_odd (512*q+349) (64512*q+44330) (256*q+173) (65024*q+44679)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h5
  have h7 : Reach (128*q+85) (65280*q+44852) := by
    apply force_odd (256*q+173) (65024*q+44679) (128*q+85) (65280*q+44852)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h6
  have h8 : Reach (64*q+41) (65408*q+44937) := by
    apply force_odd (128*q+85) (65280*q+44852) (64*q+41) (65408*q+44937)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h7
  have h9 : Reach (32*q+19) (65472*q+44978) := by
    apply force_odd (64*q+41) (65408*q+44937) (32*q+19) (65472*q+44978)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h8
  have h10 : Reach (16*q+8) (65504*q+44997) := by
    apply force_odd (32*q+19) (65472*q+44978) (16*q+8) (65504*q+44997)
      (by omega) (by omega) (by omega)
    · intro x y hx hy hw hallow
      unfold BB429Mod8.Allowed at hallow
      omega
    · exact h9
  have hallow := reach_allowed _ _ h10
  unfold BB429Mod8.Allowed at hallow
  omega

theorem blank_halt_not_9213_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 9213 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+9213 := by dsimp [q]; omega
  have hb : b=32768*q+18425 := by omega
  have h0 : Reach (16384*q+9213) (32768*q+18425) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_9213 q h0

theorem blank_halt_not_11261_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 11261 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+11261 := by dsimp [q]; omega
  have hb : b=32768*q+22521 := by omega
  have h0 : Reach (16384*q+11261) (32768*q+22521) := by
    exact ⟨n, by simpa only [← ha, ← hb] using hr⟩
  exact exclude_11261 q h0

/-- Three excluded entire disjoint lifts in the formerly open 1021/1024 gate. -/
theorem blank_halt_not_three_1021_lifts (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    a%16384 ≠ 9213 ∧ a%16384 ≠ 11261 ∧ a%16384 ≠ 12285 :=
  ⟨blank_halt_not_9213_mod16384 n a b hr hg,
   blank_halt_not_11261_mod16384 n a b hr hg,
   blank_halt_not_12285_mod16384 n a b hr hg⟩

#print axioms blank_halt_not_three_1021_lifts

end BB429No1021
