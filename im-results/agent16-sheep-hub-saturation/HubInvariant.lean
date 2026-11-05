import HubSource
import PureTwo

namespace SheepHubs

/-- Source-grounded pure 2-power zero-fiber outgoing edge to every even residue. -/
theorem zero_fiber_all_even (k s : Nat) (hk : 1 ≤ k) (hs : s%2=0) :
    ∃ x y : Nat, x%(2^k)=0 ∧ y%(2^k)=s%(2^k) ∧ SheepEven.EvenEdge x y := by
  let b := 2^k
  let u := 1+2*s+4*2^k
  let x := 4^b*u
  let y := x+2*b+(u-1)/2
  obtain ⟨hb,hu,h4,hx0,hy0⟩ :=
    BB6.Agent17Forward.zero_two_power_generic k s hk hs
  have huodd : u%2=1 := by
    dsimp [u] at *
    omega
  have hp : 4^b=(2:Nat)^(2*b) := by
    calc
      4^b = (2^2)^b := by rfl
      _ = 2^(2*b) := (Nat.pow_mul 2 2 b).symm
  have hxp : x=2^(2*b)*u := by dsimp [x]; rw [hp]
  have hhalf : (u-1)/2=s+2*b := by dsimp [u,b]; omega
  have hyF : y=SheepEven.Generic (2*b) u := by
    dsimp [y,SheepEven.Generic]
    rw [hxp,hhalf]
  have hstep : SheepEven.Step x y := by
    rw [hxp,hyF]
    exact SheepEven.Step.generic (2*b) u huodd hu
  have hxp_even : x%2=0 := by
    have hd : 2 ∣ 2^k := Nat.pow_dvd_pow 2 hk
    have he : 2^k ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx0
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd he)
  have hyEven : y%2=0 := by
    dsimp [y]
    rw [hhalf]
    omega
  have h4pow : 0<4^b := Nat.pow_pos (by decide)
  have hxlarge : u≤x := by dsimp [x]; exact Nat.le_mul_of_pos_left u h4pow
  have hylarge : 5≤y := by dsimp [y]; omega
  have hwodd : (y-1)%2=1 := by omega
  have he : SheepEven.EvenEdge x y := by
    refine ⟨y,0,y-1,hstep,hylarge,hwodd,?_,?_⟩
    · simp; omega
    · omega
  exact ⟨x,y,hx0,hy0,he⟩

/-- A zero-fiber class in a globally inductive residue predicate forces
all even residue classes at the same power-of-two modulus. -/
theorem zero_fiber_residue_saturates (k : Nat) (hk : 1≤k)
    (I : Nat → Prop)
    (hres : ∀ {x y : Nat}, x%(2^k)=y%(2^k) → I x → I y)
    (hclosed : ∀ {x y : Nat}, SheepEven.EvenEdge x y → I x → I y)
    (hz : ∃ x : Nat, x%(2^k)=0 ∧ I x) :
    ∀ s : Nat, s%2=0 → I s := by
  obtain ⟨z,hz0,hIz⟩ := hz
  intro s hs
  obtain ⟨x,y,hx,hy,hedge⟩ := zero_fiber_all_even k s hk hs
  have hIx : I x := hres (by rw [hx,hz0]) hIz
  have hIy : I y := hclosed hedge hIx
  exact hres hy hIy

/-- From a legal generic Sheep hub source, any globally inductive
predicate depending on its 2-adic residue is saturated on all even classes. -/
theorem generic_hub_saturates_two_power (a L u W : Nat)
    (ha : 1≤a) (hu : 5≤u) (huodd : u%2=1)
    (heq : 2*(1+2^L*W)+1=(2^(a+1)+1)*u+2*a)
    (I : Nat → Prop)
    (hres : ∀ {x y : Nat}, x%(2^(a+L+1))=y%(2^(a+L+1)) → I x → I y)
    (hclosed : ∀ {x y : Nat}, SheepEven.EvenEdge x y → I x → I y)
    (hsource : I (2^a*u)) :
    ∀ s : Nat, s%2=0 → I s := by
  obtain ⟨t,ht,hedge,hzero,hx⟩ := genuine_hub_to_even_edge
    a L 1 u W 0 ha hu huodd (by decide) heq
  let x := 2^a*(u+2^(L+1)*1*t)
  let y := 1+3^L*(W+(2^(a+1)+1)*1*t)
  let q := 2^(a+L+1)
  have hxmod : x%q=(2^a*u)%q := by
    change (2^a*(u+2^(L+1)*1*t))%q=(2^a*u)%q
    rw [hx]
    simp [q, Nat.add_mod, Nat.mul_mod]
  have hIx : I x := hres hxmod.symm hsource
  have hIy : I y := hclosed hedge hIx
  have hy0 : y%q=0 := Nat.mod_eq_zero_of_dvd hzero
  have hqpos : 1≤a+L+1 := by omega
  exact zero_fiber_residue_saturates (a+L+1) hqpos I hres hclosed
    ⟨y,hy0,hIy⟩

#print axioms zero_fiber_all_even
#print axioms zero_fiber_residue_saturates
#print axioms generic_hub_saturates_two_power
end SheepHubs
