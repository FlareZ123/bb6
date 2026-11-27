import LagPairPath
import PairCarryCore
namespace BB6.Agent43LagPair
open BB6.Agent9PairCarry (spreadPlan spreadWith spread4_sound)

theorem remainder_cases (r v b : Nat) (hr : 0<r) (hv : v<2*r+1) (h : v%r=b) :
    v=b ∨ v=b+r ∨ (b=0 ∧ v=2*r) := by
  by_cases h1 : v<r
  · rw [Nat.mod_eq_of_lt h1] at h
    exact Or.inl h
  · by_cases h2 : v<2*r
    · rw [Nat.mod_eq_sub_mod (by omega : r≤v),Nat.mod_eq_of_lt (by omega : v-r<r)] at h
      exact Or.inr (Or.inl (by omega))
    · have hv' : v=2*r := by omega
      rw [hv',Nat.mul_mod_left] at h
      exact Or.inr (Or.inr ⟨h.symm,hv'⟩)
theorem fold_cases (r u b : Nat) (hr : 0<r) (hu : u<4*r+2) (h : (u%(2*r+1))%r=b) :
    u=b ∨ u=b+r ∨ u=b+(2*r+1) ∨ u=b+(3*r+1) ∨ (b=0∧(u=2*r∨u=4*r+1)) := by
  by_cases hlo : u<2*r+1
  · rw [Nat.mod_eq_of_lt hlo] at h
    rcases remainder_cases r u b hr hlo h with h0|h1|⟨hb,hu'⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb,Or.inl hu'⟩)))
  · rw [Nat.mod_eq_sub_mod (by omega : 2*r+1≤u),Nat.mod_eq_of_lt (by omega : u-(2*r+1)<2*r+1)] at h
    rcases remainder_cases r (u-(2*r+1)) b hr (by omega) h with h0|h1|⟨hb,hu'⟩
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb,Or.inr (by omega)⟩)))

def zeroExtra (r u : Nat) : Nat := if u.testBit (2*r) || u.testBit (4*r+1) then 1 else 0
def pairBack (plan : List (Nat × Nat)) (r t bits : Nat) :=
  let u := spreadWith plan bits <<< t
  (u ||| (u >>> r) ||| (u >>> (2*r+1)) ||| (u >>> (3*r+1)) ||| zeroExtra r u) &&& (2^r-1)
theorem pairBack_sound (L r t bits a b : Nat) (ha : a<2^L) (hb : b<r)
    (hu : 4*a+t<4*r+2) (h : ((4*a+t)%(2*r+1))%r=b)
    (hbit : bits.testBit a=true) :
    (pairBack (spreadPlan L L) r t bits).testBit b=true := by
  let u := spreadWith (spreadPlan L L) bits <<< t
  have hs := spread4_sound L bits a ha hbit
  have ht : u.testBit (4*a+t)=true := by
    dsimp [u]
    rw [Nat.testBit_shiftLeft]
    simp [show t≤4*a+t by omega,show 4*a+t-t=4*a by omega,hs]
  change ((u ||| (u >>> r) ||| (u >>> (2*r+1)) ||| (u >>> (3*r+1)) ||| zeroExtra r u) &&& (2^r-1)).testBit b=true
  rw [Nat.testBit_and,Nat.testBit_two_pow_sub_one,decide_eq_true hb,Bool.and_true]
  simp only [Nat.testBit_or,Nat.testBit_shiftRight]
  rcases fold_cases r (4*a+t) b (by omega) hu h with h0|h1|h2|h3|⟨hb0,h4|h5⟩
  · rw [h0] at ht
    simp [ht]
  · rw [h1,Nat.add_comm b r] at ht
    simp [ht]
  · rw [h2,Nat.add_comm b (2*r+1)] at ht
    simp [ht]
  · rw [h3,Nat.add_comm b (3*r+1)] at ht
    simp [ht]
  · subst b
    rw [h4] at ht
    simp [zeroExtra,ht,hb0]
  · subst b
    rw [h5] at ht
    simp [zeroExtra,ht,hb0]

def Live (n P F r : Nat) (p : Nat → Prop) :=
  ∀ a z, FixedWalk n P (2*r) a (F-2*r) z → p (a/2)
theorem live_start (n P F r : Nat) : Live n P F r (fun a=>(2^r-1).testBit a=true) := by
  intro a z h
  have ha := fixed_start h
  simp [Nat.testBit_two_pow_sub_one,show a/2<r by omega]
theorem live_step (L n P F r bits : Nat) (hF : 2*(r+1)<F) (hcap : r+1≤2^L)
    (prev : Live n P F (r+1) (fun a=>bits.testBit a=true)) :
    Live n P F r (fun a=>(pairBack (spreadPlan L L) r (shift n P r) bits).testBit a=true) := by
  intro a z hw
  rw [show F-2*r=(F-2*(r+1)-1)+3 by omega] at hw
  obtain ⟨c,ht,ha,hc,hu,hp⟩ := path_pair hw
  have ht' : FixedWalk n P (2*(r+1)) c (F-2*(r+1)) z := by
    simpa [show 2*(r+1)=2*r+2 by omega,show F-(2*r+2)-1+1=F-(2*r+2) by omega] using ht
  exact pairBack_sound L r _ bits _ _ (by omega) ha hu hp (prev c z ht')

def denseRun (plan : List (Nat × Nat)) (n P r bits : Nat) : Nat → Nat
  | 0 => bits
  | d+1 => denseRun plan n P (r-1) (pairBack plan (r-1) (shift n P (r-1)) bits) d
theorem dense_extend (L n P F r d bits out : Nat) (hd : d<r) (hF : 2*r<F) (hcap : r≤2^L)
    (prev : Live n P F r (fun a=>bits.testBit a=true))
    (hcheck : denseRun (spreadPlan L L) n P r bits d=out) :
    Live n P F (r-d) (fun a=>out.testBit a=true) := by
  induction d generalizing r bits with
  | zero =>
    have he : bits=out := by simpa [denseRun] using hcheck
    subst out
    simpa [denseRun] using prev
  | succ d ih =>
    have hnew := live_step L n P F (r-1) bits (by omega) (by omega)
      (by simpa [show r-1+1=r by omega] using prev)
    have h := ih (r-1) _ (by omega) (by omega) (by omega) hnew (by simpa [denseRun] using hcheck)
    simpa [show r-1-d=r-(d+1) by omega] using h

def pack : List Nat → Nat
  | [] => 0
  | x::xs => 2^x ||| pack xs
theorem pack_mem (xs : List Nat) (a : Nat) : (pack xs).testBit a=true ↔ a∈xs := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    simp [pack,Nat.testBit_or,Nat.testBit_two_pow,ih]
    exact or_congr eq_comm Iff.rfl
theorem dense_to_sparse (n P F r bits : Nat) (xs : List Nat)
    (h : Live n P F r (fun a=>bits.testBit a=true)) (he : bits=pack xs) :
    Live n P F r (·∈xs) := by
  intro a z hw
  apply (pack_mem xs (a/2)).mp
  rw [←he]
  exact h a z hw

def pred (r t a : Nat) : Option Nat :=
  let u := 4*a+t
  if u<4*r+2 then some ((u%(2*r+1))%r) else none
def trail (n P r a : Nat) : Nat → Option Nat
  | 0 => some a
  | d+1 => match trail n P r a d with
    | none => none
    | some b => pred (r-(d+1)) (shift n P (r-(d+1))) b
theorem trail_cover (n P F r d : Nat) (xs : List Nat) (hd : d<r) (hF : 2*r<F)
    (prev : Live n P F r (·∈xs)) (a z : Nat)
    (hw : FixedWalk n P (2*(r-d)) a (F-2*(r-d)) z) :
    ∃ x∈xs, trail n P r x d=some (a/2) := by
  induction d generalizing a z with
  | zero => exact ⟨a/2,prev a z (by simpa using hw),rfl⟩
  | succ d ih =>
    let q := r-(d+1)
    have hq : q+1=r-d := by dsimp [q]; omega
    have hlen : F-2*q=(F-2*(r-d)-1)+3 := by omega
    change FixedWalk n P (2*q) a (F-2*q) z at hw
    rw [hlen] at hw
    obtain ⟨c,ht,ha,hc,hu,hp⟩ := path_pair hw
    have ht' : FixedWalk n P (2*(r-d)) c (F-2*(r-d)) z := by
      simpa [show 2*q+2=2*(r-d) by omega,show F-2*(r-d)-1+1=F-2*(r-d) by omega] using ht
    obtain ⟨x,hx,htrail⟩ := ih (by omega) c z ht'
    refine ⟨x,hx,?_⟩
    simp only [trail,htrail]
    change pred q (shift n P q) (c/2)=some (a/2)
    simp [pred,hu,hp]
def sparseCheck (n P r d : Nat) (xs ys : List Nat) : Bool :=
  xs.all fun a => match trail n P r a d with
    | none => true
    | some b => ys.contains b
theorem sparse_extend (n P F r d : Nat) (xs ys : List Nat) (hd : d<r) (hF : 2*r<F)
    (prev : Live n P F r (·∈xs)) (hc : sparseCheck n P r d xs ys=true) :
    Live n P F (r-d) (·∈ys) := by
  intro a z hw
  obtain ⟨x,hx,ht⟩ := trail_cover n P F r d xs hd hF prev a z hw
  unfold sparseCheck at hc
  have h := List.all_eq_true.mp hc x hx
  simpa [ht,List.contains_eq_mem] using h
#print axioms pairBack_sound
#print axioms dense_extend
#print axioms sparse_extend
end BB6.Agent43LagPair
