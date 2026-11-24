import Lean

namespace BB6.Agent19MixedStrip

set_option maxHeartbeats 500000

/-- An invariant closed under an injection on a finite domain is also
    closed under its inverse. -/
private theorem map_nodup_on {α β : Type} (f : α→β) (xs : List α)
    (hn : xs.Nodup) (hi : ∀ x∈xs, ∀ y∈xs, f x=f y → x=y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hn
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hn.2 (fun a ha b hb => hi a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    intro h
    obtain ⟨y,hy,he⟩ := List.mem_map.mp h
    have hxy := hi y (List.mem_cons_of_mem _ hy) x (by simp) he
    subst y
    exact hn.1 hy

theorem finite_inverse {α : Type} (xs : List α) (hn : xs.Nodup) (f : α→α) (P : α→Prop)
    (hf : ∀ x∈xs, f x∈xs) (hi : ∀ x∈xs, ∀ y∈xs, f x=f y → x=y)
    (hc : ∀ x∈xs, P x → P (f x)) (x : α) (hx : x∈xs) (h : P (f x)) : P x := by
  classical
  apply Classical.byContradiction
  intro hnP
  let ys := xs.filter (fun y => decide (P y))
  have hym (y : α) : y∈ys ↔ y∈xs ∧ P y := by simp [ys]
  have hyn : ys.Nodup := List.Nodup.sublist List.filter_sublist hn
  have hmap := map_nodup_on f ys hyn (fun a ha b hb => hi a (hym a |>.mp ha |>.1) b (hym b |>.mp hb |>.1))
  have hnmem : f x ∉ ys.map f := by
    intro hh
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hh
    have hyy := (hym y).mp hy
    have heq := hi y hyy.1 x hx he
    exact hnP (heq ▸ hyy.2)
  have hsub : f x :: ys.map f ⊆ ys := by
    intro y hy
    rcases List.mem_cons.mp hy with hxy|hy
    · subst y; exact (hym (f x)).mpr ⟨hf x hx,h⟩
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
      obtain ⟨hm,hP⟩ := (hym z).mp hz
      exact (hym (f z)).mpr ⟨hf z hm,hc z hm hP⟩
  have hlen := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hnmem,hmap⟩) hsub
  simp at hlen
  omega

def states (M L : Nat) : List (Int×Int) :=
  (List.range M).flatMap fun (z : Nat) => (List.range L).map fun (h : Nat) => ((z:Int),(h:Int))

private theorem states_mem (M L : Nat) (z h : Int) :
    (z,h)∈states M L ↔ 0≤z ∧ z<(M:Int) ∧ 0≤h ∧ h<(L:Int) := by
  simp only [states,List.mem_flatMap,List.mem_range,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,hez,heh⟩; omega
  · rintro ⟨hz,hz',hh,hh'⟩
    exact ⟨z.toNat,by omega,h.toNat,by omega,Int.toNat_of_nonneg hz,Int.toNat_of_nonneg hh⟩

private theorem states_nodup (M L : Nat) : (states M L).Nodup := by
  rw [states,List.nodup_iff_pairwise_ne,List.pairwise_flatMap]
  refine ⟨?_,?_⟩
  · intro a _
    rw [List.pairwise_map]
    apply List.Pairwise.imp _ (List.nodup_range (n:=L))
    intro i j hij he
    have h := congrArg Prod.snd he
    exact hij (by omega)
  · apply List.Pairwise.imp _ (List.nodup_range)
    intro a b hab x hx y hy he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
    have h := congrArg Prod.fst he
    exact hab (by omega)

def canon (M L : Nat) (s : Int×Int) : Int×Int := (s.1%M,s.2%L)

def Periodic (M L : Nat) (P : Int → Int → Prop) : Prop :=
  ∀ z h z' h' : Int, z%M=z'%M → h%L=h'%L → P z h → P z' h'

def D (s : Int×Int) : Int×Int := (s.1+4,2*s.2)
def H (s : Int×Int) : Int×Int := (s.1+7,4*s.2-s.1-3-s.1%2)

def Compatible (M L : Nat) (F : Int×Int→Int×Int) : Prop :=
  ∀ s t, canon M L s=canon M L t → canon M L (F s)=canon M L (F t)

def InjectiveResidue (M L : Nat) (F : Int×Int→Int×Int) : Prop :=
  ∀ s t, canon M L (F s)=canon M L (F t) → canon M L s=canon M L t

private theorem canon_mem (M L : Nat) (hM : 0<M) (hL : 0<L) (s : Int×Int) : canon M L s∈states M L := by
  rcases s with ⟨z,h⟩
  apply (states_mem M L _ _).mpr
  exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega),Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩

private theorem canon_id (M L : Nat) (s : Int×Int) (hs : s∈states M L) : canon M L s=s := by
  rcases s with ⟨z,h⟩
  obtain ⟨hz,hz',hh,hh'⟩ := (states_mem M L z h).mp hs
  simp [canon,Int.emod_eq_of_lt hz hz',Int.emod_eq_of_lt hh hh']

private theorem canon_idem (M L : Nat) (s : Int×Int) : canon M L (canon M L s)=canon M L s := by
  simp [canon]

private theorem periodic_canon (M L : Nat) (P : Int→Int→Prop) (hp : Periodic M L P) (s : Int×Int) :
    P s.1 s.2 ↔ P (canon M L s).1 (canon M L s).2 := by
  constructor
  · exact hp s.1 s.2 _ _ (by simp [canon]) (by simp [canon])
  · exact hp _ _ s.1 s.2 (by simp [canon]) (by simp [canon])

/-- Closed residue predicates are backwards closed under any modular
    permutation; no unproved Euler or multiplicative-order premise. -/
theorem modular_inverse (M L : Nat) (hM : 0<M) (hL : 0<L)
    (P : Int→Int→Prop) (hp : Periodic M L P) (F : Int×Int→Int×Int)
    (hcompat : Compatible M L F) (hinj : InjectiveResidue M L F)
    (hc : ∀ s, P s.1 s.2 → P (F s).1 (F s).2) (s : Int×Int)
    (hs : P (F s).1 (F s).2) : P s.1 s.2 := by
  let f := fun t => canon M L (F t)
  let Q := fun (t : Int×Int) => P t.1 t.2
  have hfc : f (canon M L s)=canon M L (F s) := hcompat _ _ (canon_idem M L s)
  have hh : Q (f (canon M L s)) := by rw [show f (canon M L s)=canon M L (F s) from hfc]; exact (periodic_canon M L P hp (F s)).mp hs
  have hq : Q (canon M L s) := finite_inverse (states M L) (states_nodup M L) f Q
      (fun t _ => canon_mem M L hM hL (F t))
      (fun a ha b hb he => by
        have he' := hinj a b he
        simpa [canon_id M L a ha,canon_id M L b hb] using he')
      (fun t _ ht => (periodic_canon M L P hp (F t)).mp (hc t ht))
      (canon M L s) (canon_mem M L hM hL s) hh
  exact (periodic_canon M L P hp s).mpr hq

theorem mod_sub (M x y : Int) : x%M=y%M ↔ M∣x-y := by
  rw [Int.dvd_iff_emod_eq_zero,Int.emod_eq_emod_iff_emod_sub_eq_zero]

theorem mod_add_const (M x y c : Int) : (x+c)%M=(y+c)%M ↔ x%M=y%M := by
  rw [mod_sub,mod_sub]
  have he : x+c-(y+c)=x-y := by omega
  rw [he]

theorem mod_mul_const (M x y c : Int) (h : x%M=y%M) : (c*x)%M=(c*y)%M := by
  rw [Int.mul_emod,Int.mul_emod c y,h]

theorem mod_add_pair (M a b c d : Int) (h1 : a%M=b%M) (h2 : c%M=d%M) :
    (a+c)%M=(b+d)%M := by rw [Int.add_emod,Int.add_emod b d,h1,h2]

theorem mod_sub_pair (M a b c d : Int) (h1 : a%M=b%M) (h2 : c%M=d%M) :
    (a-c)%M=(b-d)%M := by rw [Int.sub_emod,Int.sub_emod b d,h1,h2]

theorem mod_project (M L x y : Int) (hdiv : L∣M) (h : x%M=y%M) : x%L=y%L := by
  rw [←Int.emod_emod_of_dvd x hdiv,←Int.emod_emod_of_dvd y hdiv,h]

theorem cancel_two (L x y : Int) (hodd : L%2=1) (h : (2*x)%L=(2*y)%L) : x%L=y%L := by
  obtain ⟨q,hq⟩ := (mod_sub L _ _).mp h
  have he : 2*(x-y)=L*q := by omega
  have hqeven : q%2=0 := by
    have hm := congrArg (·%2) he
    rw [Int.mul_emod,Int.mul_emod L q,hodd] at hm
    simp at hm
    omega
  apply (mod_sub L x y).mpr
  refine ⟨q/2,?_⟩
  have hq' : q=2*(q/2) := by omega
  conv at he => rhs; rw [hq',←Int.mul_assoc,Int.mul_comm L 2,Int.mul_assoc]
  omega

theorem D_compatible (M L : Nat) : Compatible M L D := by
  intro s t he
  rcases s with ⟨z,h⟩; rcases t with ⟨z',h'⟩
  simp only [canon,Prod.mk.injEq] at he ⊢
  exact ⟨(mod_add_const M z z' 4).mpr he.1,mod_mul_const L h h' 2 he.2⟩

theorem D_injective (M L : Nat) (hodd : L%2=1) : InjectiveResidue M L D := by
  intro s t he
  rcases s with ⟨z,h⟩; rcases t with ⟨z',h'⟩
  simp only [canon,D,Prod.mk.injEq] at he ⊢
  exact ⟨(mod_add_const M z z' 4).mp he.1,cancel_two L h h' (by omega) he.2⟩

theorem H_compatible (M L : Nat) (hL : L∣M) (h2 : 2∣M) : Compatible M L H := by
  intro s t he
  rcases s with ⟨z,h⟩; rcases t with ⟨z',h'⟩
  simp only [canon,H,Prod.mk.injEq] at he ⊢
  have hz := mod_project (M:Int) (L:Int) z z' (Int.natCast_dvd_natCast.mpr hL) he.1
  have hp := mod_project (M:Int) 2 z z' (by exact Int.natCast_dvd_natCast.mpr h2) he.1
  refine ⟨(mod_add_const M z z' 7).mpr he.1,?_⟩
  rw [hp]
  apply mod_sub_pair _ _ _ _ _ ?_ rfl
  apply mod_sub_pair _ _ _ _ _ ?_ rfl
  exact mod_sub_pair _ _ _ _ _ (mod_mul_const L h h' 4 he.2) hz

theorem H_injective (M L : Nat) (hL : L∣M) (h2 : 2∣M) (hodd : L%2=1) : InjectiveResidue M L H := by
  intro s t he
  rcases s with ⟨z,h⟩; rcases t with ⟨z',h'⟩
  simp only [canon,H,Prod.mk.injEq] at he ⊢
  have hz := (mod_add_const M z z' 7).mp he.1
  have hzL := mod_project (M:Int) (L:Int) z z' (Int.natCast_dvd_natCast.mpr hL) hz
  have hp := mod_project (M:Int) 2 z z' (by exact Int.natCast_dvd_natCast.mpr h2) hz
  rw [hp] at he
  have he' : (4*h-z-3-z'%2)%L=(4*h'-z-3-z'%2)%L := he.2.trans (mod_sub_pair _ _ _ _ _ (mod_sub_pair _ _ _ _ _ (mod_sub_pair _ _ _ _ _ rfl hzL.symm) rfl) rfl)
  have h4 : (4*h)%L=(4*h')%L := by
    apply (mod_sub L _ _).mpr
    have hh := (mod_sub L _ _).mp he'
    have heq : 4*h-z-3-z'%2-(4*h'-z-3-z'%2)=4*h-4*h' := by omega
    rw [heq] at hh
    exact hh
  have h4' : (2*(2*h))%L=(2*(2*h'))%L := by rw [show 2*(2*h)=4*h by omega,show 2*(2*h')=4*h' by omega]; exact h4
  exact ⟨hz,cancel_two L h h' (by omega) (cancel_two L (2*h) (2*h') (by omega) h4')⟩

def DClosed (P : Int→Int→Prop) : Prop := ∀ z h : Int, P z h → P (z+4) (2*h)
def HClosed (P : Int→Int→Prop) : Prop := ∀ z h : Int, P z h → P (z+7) (4*h-z-3-z%2)
def DBackward (P : Int→Int→Prop) : Prop := ∀ z h : Int, P (z+4) (2*h) → P z h
def HBackward (P : Int→Int→Prop) : Prop := ∀ z h : Int, P (z+7) (4*h-z-3-z%2) → P z h

theorem D_backward (M L : Nat) (hM : 0<M) (hL : 0<L) (hodd : L%2=1)
    (P : Int→Int→Prop) (hp : Periodic M L P) (hc : DClosed P) : DBackward P := by
  intro z h hs
  exact modular_inverse M L hM hL P hp D (D_compatible M L) (D_injective M L hodd)
    (fun s => hc s.1 s.2) (z,h) hs

theorem H_backward (M L : Nat) (hM : 0<M) (hL : 0<L) (hdiv : L∣M) (h2 : 2∣M) (hodd : L%2=1)
    (P : Int→Int→Prop) (hp : Periodic M L P) (hc : HClosed P) : HBackward P := by
  intro z h hs
  exact modular_inverse M L hM hL P hp H (H_compatible M L hdiv h2) (H_injective M L hdiv h2 hodd)
    (fun s => hc s.1 s.2) (z,h) hs

private def half (L x : Int) : Int := if x%2=0 then x/2 else (x+L)/2

private theorem half_spec (L x : Int) (ho : L%2=1) : (2*half L x)%L=x%L := by
  unfold half
  split
  · rename_i h
    rw [show 2*(x/2)=x by omega]
  · rename_i h
    rw [show 2*((x+L)/2)=x+L by omega,Int.add_emod,Int.emod_self,Int.add_zero,Int.emod_emod]

private def half8 (L x : Int) : Int := half L (half L (half L x))

private theorem half8_spec (L x : Int) (ho : L%2=1) : (8*half8 L x)%L=x%L := by
  have h1 := mod_mul_const L _ _ 4 (half_spec L (half L (half L x)) ho)
  have h2 := mod_mul_const L _ _ 2 (half_spec L (half L x) ho)
  have h3 := half_spec L x ho
  unfold half8
  rw [show 8*half L (half L (half L x))=4*(2*half L (half L (half L x))) by omega,h1,
      show 4*half L (half L x)=2*(2*half L x) by omega,h2,h3]

private theorem mod_same_diff (M x y a b : Int) (h : x%M=y%M) (he : a-b=x-y) : a%M=b%M := by
  apply (mod_sub M a b).mpr
  rw [he]
  exact (mod_sub M x y).mp h

private def T (z : Int) := z-11-z%2

/-- Comparing HD and DH gives a pure h-translation. -/
private theorem translateT (M L : Nat) (ho : L%2=1) (P : Int→Int→Prop)
    (hp : Periodic M L P) (hd : DClosed P) (hh : HClosed P)
    (hdb : DBackward P) (hhb : HBackward P) (Z y : Int) (hP : P Z y) : P Z (y+T Z) := by
  let z := Z-11
  let t := z%2
  let v := half8 L (y+2*z+6+2*t)
  have hv : (8*v)%L=(y+2*z+6+2*t)%L := half8_spec L _ (by omega)
  have hZ : z+11=Z := by dsimp [z]; omega
  have hp' : t=1-Z%2 := by dsimp [t,z]; omega
  have hDHa : P (z+11) (8*v-2*z-6-2*t) := hp Z y _ _ (by rw [hZ])
    (mod_same_diff L (8*v) (y+2*z+6+2*t) _ _ hv (by omega)).symm hP
  have hDH : P (z+7+4) (2*(4*v-z-3-z%2)) := by
    rw [show z+7+4=z+11 by omega,show 2*(4*v-z-3-z%2)=8*v-2*z-6-2*t by dsimp [t]; omega]
    exact hDHa
  have h0 := hhb z v (hdb (z+7) (4*v-z-3-z%2) hDH)
  have h1 := hh (z+4) (2*v) (hd z v h0)
  have hHD : P Z (8*v-z-7-t) := by
    rw [show Z=z+4+7 by dsimp [z]; omega,show 8*v-z-7-t=4*(2*v)-(z+4)-3-(z+4)%2 by dsimp [t]; omega]
    exact h1
  exact hp Z _ Z _ rfl (mod_same_diff L (8*v) (y+2*z+6+2*t) _ _ hv (by unfold T; omega)) hHD

private theorem translateTneg (M L : Nat) (ho : L%2=1) (P : Int→Int→Prop)
    (hp : Periodic M L P) (hd : DClosed P) (hh : HClosed P)
    (hdb : DBackward P) (hhb : HBackward P) (Z y : Int) (hP : P Z y) : P Z (y-T Z) := by
  let z := Z-11
  let t := z%2
  let v := half8 L (y+z+7+t)
  have hv : (8*v)%L=(y+z+7+t)%L := half8_spec L _ (by omega)
  have hZ : z+11=Z := by dsimp [z]; omega
  have hp' : t=1-Z%2 := by dsimp [t,z]; omega
  have hHDa : P (z+11) (8*v-z-7-t) := hp Z y _ _ (by rw [hZ])
    (mod_same_diff L (8*v) (y+z+7+t) _ _ hv (by omega)).symm hP
  have hHD : P (z+4+7) (4*(2*v)-(z+4)-3-(z+4)%2) := by
    rw [show z+4+7=z+11 by omega,show 4*(2*v)-(z+4)-3-(z+4)%2=8*v-z-7-t by dsimp [t]; omega]
    exact hHDa
  have h0 := hdb z v (hhb (z+4) (2*v) hHD)
  have h1 := hd (z+7) (4*v-z-3-z%2) (hh z v h0)
  have hDH : P Z (8*v-2*z-6-2*t) := by
    rw [show Z=z+7+4 by dsimp [z]; omega,show 8*v-2*z-6-2*t=2*(4*v-z-3-z%2) by dsimp [t]; omega]
    exact h1
  exact hp Z _ Z _ rfl (mod_same_diff L (8*v) (y+z+7+t) _ _ hv (by unfold T; omega)) hDH

/-- Conjugating the translation by D and canceling twice gives constant +8. -/
private theorem translate8 (M L : Nat) (ho : L%2=1) (P : Int→Int→Prop)
    (hp : Periodic M L P) (hd : DClosed P) (hh : HClosed P)
    (hdb : DBackward P) (hhb : HBackward P) (Z y : Int) (hP : P Z y) : P Z (y+8) := by
  let z := Z-4
  let v := half L y
  have hv : (2*v)%L=y%L := half_spec L _ (by omega)
  have hD : P (z+4) (2*v) := hp Z y _ _ (by dsimp [z]; simp) hv.symm hP
  have h0 := hdb z v hD
  have h1 := translateTneg M L ho P hp hd hh hdb hhb z v h0
  have h2 := hd z (v-T z) h1
  have h3 : P Z (2*v-2*T z) := by
    rw [show Z=z+4 by dsimp [z]; omega,show 2*v-2*T z=2*(v-T z) by omega]
    exact h2
  have h4 : P Z (y-2*T Z+8) := hp Z _ Z _ rfl
    (mod_same_diff L (2*v) y _ _ hv (by unfold T; dsimp [z]; omega)) h3
  have h5 := translateT M L ho P hp hd hh hdb hhb Z _ h4
  have h6 := translateT M L ho P hp hd hh hdb hhb Z _ h5
  rw [show y-2*T Z+8+T Z+T Z=y+8 by omega] at h6
  exact h6

private theorem translate8n (P : Int→Int→Prop) (hc : ∀ z y : Int, P z y → P z (y+8))
    (z y : Int) (n : Nat) (hP : P z y) : P z (y+8*(n:Int)) := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    have hh := hc z _ ih
    rw [show y+8*((n+1:Nat):Int)=y+8*(n:Int)+8 by omega]
    exact hh

private theorem full_h (M L : Nat) (hL : 0<L) (ho : L%2=1) (P : Int→Int→Prop)
    (hp : Periodic M L P) (hd : DClosed P) (hh : HClosed P)
    (hdb : DBackward P) (hhb : HBackward P) (z y target : Int) (hP : P z y) : P z target := by
  let v := half8 L (target-y)
  let n := (v%(L:Int)).toNat
  have hn : (n:Int)=v%L := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hv : (8*v)%L=(target-y)%L := half8_spec L _ (by omega)
  have hnv : (n:Int)%L=v%L := by rw [hn,Int.emod_emod]
  have h8n := (mod_mul_const (L:Int) (n:Int) v 8 hnv).trans hv
  have he : (y+8*(n:Int))%L=target%L := mod_same_diff L (8*(n:Int)) (target-y) _ _ h8n (by omega)
  exact hp z _ z target rfl he (translate8n P (translate8 M L ho P hp hd hh hdb hhb) z y n hP)

/-- The modular permutations D and H act transitively on all (z mod M,
    h mod L) whenever M is divisible by 4 and L is an odd divisor. -/
theorem mixed_transitive (M L : Nat) (hM : 0<M) (hL : 0<L) (hdiv : L∣M)
    (h4 : 4∣M) (ho : L%2=1) (P : Int→Int→Prop) (hp : Periodic M L P)
    (hd : DClosed P) (hh : HClosed P) (seedZ seedH : Int) (hseed : P seedZ seedH) : ∀ Z Y : Int, P Z Y := by
  have h2 : 2∣M := Nat.dvd_trans (by decide : 2∣4) h4
  have hdb := D_backward M L hM hL ho P hp hd
  have hhb := H_backward M L hM hL hdiv h2 ho P hp hh
  have allH : ∀ z y target : Int, P z y → P z target := full_h M L hL ho P hp hd hh hdb hhb
  intro Z Y
  have hHn (n : Nat) : ∃ y : Int, P (seedZ+7*(n:Int)) y := by
    induction n with
    | zero => exact ⟨seedH,by simpa using hseed⟩
    | succ n ih =>
      obtain ⟨y,hy⟩ := ih
      refine ⟨4*y-(seedZ+7*(n:Int))-3-(seedZ+7*(n:Int))%2,?_⟩
      rw [show seedZ+7*((n+1:Nat):Int)=seedZ+7*(n:Int)+7 by omega]
      exact hh _ y hy
  let k := ((seedZ-Z)%4).toNat
  have hk : (k:Int)=(seedZ-Z)%4 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  obtain ⟨y,hy⟩ := hHn k
  let z := seedZ+7*(k:Int)
  have hz : z%4=Z%4 := by dsimp [z]; omega
  have hz0 : P z Y := allH z y Y hy
  have plus4 (q : Int) (hq : P q Y) : P (q+4) Y := allH _ (2*Y) Y (hd q Y hq)
  have minus4 (q : Int) (hq : P q Y) : P (q-4) Y := by
    apply hdb (q-4) Y
    rw [show q-4+4=q by omega]
    exact allH q Y (2*Y) hq
  have up (n : Nat) : P (z+4*(n:Int)) Y := by
    induction n with
    | zero => simpa using hz0
    | succ n ih =>
      rw [show z+4*((n+1:Nat):Int)=z+4*(n:Int)+4 by omega]
      exact plus4 _ ih
  have down (n : Nat) : P (z-4*(n:Int)) Y := by
    induction n with
    | zero => simpa using hz0
    | succ n ih =>
      rw [show z-4*((n+1:Nat):Int)=z-4*(n:Int)-4 by omega]
      exact minus4 _ ih
  by_cases hge : z≤Z
  · have he : Z=z+4*((Z-z).toNat/4:Nat) := by omega
    rw [he]
    exact up _
  · have he : Z=z-4*((z-Z).toNat/4:Nat) := by omega
    rw [he]
    exact down _

#print axioms mixed_transitive

#print axioms finite_inverse
#print axioms modular_inverse
#print axioms D_injective
#print axioms H_injective
end BB6.Agent19MixedStrip
