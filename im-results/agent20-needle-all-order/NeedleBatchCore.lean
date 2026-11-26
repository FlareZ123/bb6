import NeedleTerminalExtensionCore

namespace NeedleBatch
open NeedleTerminalExtension

def bias (v : Nat) : Nat :=
  if v=0 then 0 else if v=1 then 1 else 3+2^v*(2*v-3)

def weight : List Nat → Nat
  | [] => 0
  | v::w => v+1+weight w

def coeffA : List Nat → Nat
  | [] => 1
  | v::w => coeffA w * den v

def coeffC : List Nat → Nat
  | [] => 0
  | v::w => coeffA w * bias v + 2^(v+1)*coeffC w

theorem edge_affine {v x y : Nat} (h : Edge v x y) :
    2^(v+1)*(y-1)=den v*(x-1)+bias v := by
  have hi := inverse_complete v x y h
  obtain ⟨q,hx,hy⟩ := h
  have hp : 0<(2:Nat)^v := Nat.two_pow_pos _
  have hx1 : 1≤x := by have : 3*2^v≤x := hi.1; omega
  have hy1 : 1≤y := by omega
  have hxI : (x-1:Nat) = x-1 := rfl
  have hn : (2:Int)^(v+1)*((y:Int)-1)=(den v:Int)*((x:Int)-1)+(bias v:Int) := by
    have hpow : (2:Int)^(v+1)=2*(2:Int)^v := by rw [Int.pow_succ,Int.mul_comm]
    have hden : (den v:Int)=(2:Int)^(v+1)+3 := by simp [den]
    have he := hi.2
    simp only [mul,add] at he
    by_cases h0 : v=0
    · subst v; simp [den,bias] at he ⊢; omega
    · by_cases h1 : v=1
      · subst v; simp [den,bias] at he ⊢; omega
      · have hv : 3≤2*v := by omega
        have hbi : (bias v:Int)=3+(2:Int)^v*(2*(v:Int)-3) := by
          simp [bias,h0,h1,Int.ofNat_sub hv]
        rw [hden,hbi,hpow] at *
        grind
  have hxcast : ((x-1:Nat):Int)=(x:Int)-1 := Int.ofNat_sub hx1
  have hycast : ((y-1:Nat):Int)=(y:Int)-1 := Int.ofNat_sub hy1
  rw [←hxcast,←hycast] at hn
  exact_mod_cast hn

theorem path_affine {w : List Nat} {x y : Nat} (h : Path w x y) :
    2^weight w*(y-1)=coeffA w*(x-1)+coeffC w := by
  induction h with
  | nil x => simp [weight,coeffA,coeffC]
  | @cons v w x z y he hp ih =>
    have h1:=edge_affine he
    simp only [weight,coeffA,coeffC,Nat.pow_add]
    calc
      2^(v+1)*2^weight w*(y-1)=2^(v+1)*(2^weight w*(y-1)) := by ac_rfl
      _=2^(v+1)*(coeffA w*(z-1)+coeffC w) := by rw [ih]
      _=coeffA w*(2^(v+1)*(z-1))+2^(v+1)*coeffC w := by rw [Nat.mul_add]; ac_rfl
      _=coeffA w*(den v*(x-1)+bias v)+2^(v+1)*coeffC w := by rw [h1]
      _=coeffA w*den v*(x-1)+(coeffA w*bias v+2^(v+1)*coeffC w) := by rw [Nat.mul_add]; ac_rfl

/-- A path of exact low-bit observations. Low residues may be powers of two;
that does not assert that the corresponding full source is terminal. -/
inductive LowPath : Nat → Nat → List Nat → Nat → Prop where
  | nil (B r : Nat) : LowPath B r [] r
  | cons {B r v q out : Nat} {w : List Nat}
      (hv : v+1≤B) (hr : r=2^v*(2*q+1))
      (rest : LowPath (B-(v+1)) ((r+v+3*q)%2^(B-(v+1))) w out) :
      LowPath B r (v::w) out

theorem lowPath_weight {B r w out} (h : LowPath B r w out) : weight w≤B := by
  induction h with
  | nil => simp [weight]
  | cons hv hr rest ih => simp [weight]; omega

theorem lowPath_sound {B r w out} (h : LowPath B r w out) (x : Nat)
    (hx : 2^B≤x) (hr : x%2^B=r) :
    ∃ y, Path w x y ∧ 2^(B-weight w)≤y ∧ y%2^(B-weight w)=out := by
  induction h generalizing x with
  | nil B r => exact ⟨x,Path.nil x,by simpa [weight] using hx,by simpa [weight] using hr⟩
  | @cons B r v q w out hv hq rest ih =>
    let k := B-(v+1)
    let t := 2^k*(x/2^B)
    have hk : B=v+1+k := by dsimp [k]; omega
    have hdiv : 0<x/2^B := Nat.div_pos hx (Nat.two_pow_pos B)
    have ht : 0<t := Nat.mul_pos (Nat.two_pow_pos _) hdiv
    have hxEq : x=2^v*(2*(q+t)+1) := by
      have h := Nat.div_add_mod x (2^B)
      rw [hr,hq] at h
      conv at h => lhs; lhs; rw [hk,Nat.pow_add,Nat.pow_succ]
      dsimp [t]
      grind
    let y := x+v+3*(q+t)
    have he : Edge v x y := by
      refine ⟨q+t-1,?_,?_⟩
      · rw [hxEq,show 2*(q+t-1)+3=2*(q+t)+1 by omega]
      · dsimp [y]; omega
    have hyEq : y=r+v+3*q+den v*t := by
      dsimp [y,den]
      rw [hxEq,hq,Nat.pow_succ]
      grind
    have hrem : y%2^k=(r+v+3*q)%2^k := by
      rw [hyEq,Nat.add_mod]
      have hd : 2^k∣den v*t := by refine ⟨den v*(x/2^B),?_⟩; dsimp [t]; ac_rfl
      rw [Nat.mod_eq_zero_of_dvd hd,Nat.add_zero,Nat.mod_mod]
    have hky : 2^k≤y := by
      have hkb : k≤B := by dsimp [k]; omega
      have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hkb
      dsimp [y]; omega
    obtain ⟨z,hp,hlo,hmod⟩ := ih y hky hrem
    refine ⟨z,Path.cons he hp,?_,?_⟩
    · simpa [weight,k, Nat.sub_add_eq] using hlo
    · simpa [weight,k, Nat.sub_add_eq] using hmod

#print axioms edge_affine
#print axioms path_affine
#print axioms lowPath_weight
#print axioms lowPath_sound
end NeedleBatch
