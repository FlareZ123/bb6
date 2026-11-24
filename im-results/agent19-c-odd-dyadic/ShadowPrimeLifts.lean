import Lean

namespace BB6.Agent19PrimeLifts

/-- Binary digit extracted from the representative of a residue. -/
def upper (q : Nat) (x : Nat) : Bool := decide (q ≤ 2*x)

def weight (q : Nat) (xs : List Nat) : Nat := xs.countP (upper q)

def fiber (q m x : Nat) : List Nat := (List.range m).map (fun t => x+t*q)

def fullLift (q m : Nat) (xs : List Nat) : List Nat :=
  xs.flatMap (fiber q m)

private theorem countP_all (p : Nat → Bool) (xs : List Nat)
    (h : ∀ x ∈ xs, p x = true) : xs.countP p=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    simp [hx, ih (fun y hy => h y (by simp [hy]))]

private theorem countP_none (p : Nat → Bool) (xs : List Nat)
    (h : ∀ x ∈ xs, p x = false) : xs.countP p=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    simp [hx, ih (fun y hy => h y (by simp [hy]))]

/-- A full odd fiber contributes its central base bit and exactly h additional ones. -/
theorem fiber_weight (q h x : Nat) (hx : x<q) :
    weight (q*(2*h+1)) (fiber q (2*h+1) x) = h + if upper q x then 1 else 0 := by
  have hm : 2*h+1=h+1+h := by omega
  unfold weight fiber
  rw [hm,List.range_add (n:=h+1) (m:=h),List.range_succ,List.map_append,List.map_append,
    List.countP_append,List.countP_append]
  rw [List.map_map]
  have hl : ((List.range h).map (fun t => x+t*q)).countP (upper (q*(h+1+h)))=0 := by
    apply countP_none
    intro y hy
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hy
    have ht' := List.mem_range.mp ht
    unfold upper
    apply decide_eq_false
    intro hb
    have hmul : (t+1)*q≤h*q := Nat.mul_le_mul_right q (by omega)
    have hqp : q>0 := by omega
    grind
  have hr : ((List.range h).map (fun t => x+(h+1+t)*q)).countP (upper (q*(h+1+h)))=h := by
    rw [countP_all]
    · simp
    · intro y hy
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hy
      unfold upper
      apply decide_eq_true
      have hmul : (h+1)*q≤(h+1+t)*q := Nat.mul_le_mul_right q (by omega)
      grind
  have hc : upper (q*(h+1+h)) (x+h*q)=upper q x := by
    unfold upper
    by_cases hh : q≤2*x
    · have he : q*(h+1+h)≤2*(x+h*q) := by grind
      simp [he,hh]
    · have he : ¬ q*(h+1+h)≤2*(x+h*q) := by grind
      simp [he,hh]
  simp only [List.map_cons,List.map_nil,List.countP_cons,List.countP_nil] at *
  rw [hl,hc]
  change 0+(0+(if upper q x = true then 1 else 0))+((List.range h).map (fun t => x+(h+1+t)*q)).countP _ = _
  rw [hr]
  split <;> simp_all <;> omega

/-- Imbalance survives every full odd lift, for arbitrary finite base representatives. -/
theorem full_weight (q h : Nat) (xs : List Nat) (hx : ∀ x ∈ xs, x<q) :
    weight (q*(2*h+1)) (fullLift q (2*h+1) xs) = h*xs.length + weight q xs := by
  induction xs with
  | nil => simp [fullLift,weight]
  | cons x xs ih =>
    have h1 := fiber_weight q h x (hx x (by simp))
    have h2 := ih (fun y hy => hx y (by simp [hy]))
    simp only [fullLift,List.flatMap_cons,weight,List.countP_append,List.countP_cons,List.length_cons] at *
    rw [h1,h2,Nat.mul_succ]
    omega

theorem full_length (q m : Nat) (xs : List Nat) :
    (fullLift q m xs).length=m*xs.length := by
  induction xs with
  | nil => simp [fullLift]
  | cons x xs ih =>
    change (fiber q m x ++ fullLift q m xs).length=m*(xs.length+1)
    rw [List.length_append,ih,Nat.mul_succ]
    simp [fiber,Nat.add_comm]

theorem fullLift_nodup (q m : Nat) (xs : List Nat) (hq : 0<q)
    (hn : xs.Nodup) (hx : ∀ x ∈ xs, x<q) : (fullLift q m xs).Nodup := by
  induction xs with
  | nil => simp [fullLift]
  | cons x xs ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hn
    change (fiber q m x ++ fullLift q m xs).Nodup
    apply List.nodup_append.mpr
    refine ⟨?_,ih hnd (fun y hy => hx y (by simp [hy])),?_⟩
    · unfold fiber
      exact List.Pairwise.map _ (fun a b h => by
        intro he
        apply h
        exact Nat.eq_of_mul_eq_mul_right hq (by omega)) List.nodup_range
    · intro a ha b hb he
      obtain ⟨t,ht,hat⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨w,hw,hbw⟩ := List.mem_map.mp hb
      have hx' := hx x (by simp)
      have hy' := hx y (by simp [hy])
      have eq := congrArg (fun z : Nat => z%q) (hat.trans (he.trans hbw.symm))
      rw [Nat.add_mul_mod_self_right,Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hx',Nat.mod_eq_of_lt hy'] at eq
      exact hnot (eq ▸ hy)

/-- A distinct list of the full fiber length projecting to the base orbit
    must exhaust every fiber. This is the exact combinatorial step needed for
    multiplicative orbits when the period grows by the lift multiplier. -/
theorem fullLift_perm (q m : Nat) (xs ys : List Nat) (hq : 0<q)
    (hx : ∀ x ∈ xs, x<q) (hxn : xs.Nodup) (hyn : ys.Nodup)
    (hy : ∀ y ∈ ys, y<q*m ∧ y%q∈xs)
    (hlen : ys.length=m*xs.length) : ys.Perm (fullLift q m xs) := by
  have hn := fullLift_nodup q m xs hq hxn hx
  have hlen' := full_length q m xs
  have hsub : ys ⊆ fullLift q m xs := by
    intro y hym
    obtain ⟨hsmall,hmem⟩ := hy y hym
    apply List.mem_flatMap.mpr
    refine ⟨y%q,hmem,List.mem_map.mpr ⟨y/q,?_,?_⟩⟩
    · exact List.mem_range.mpr (Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hsmall))
    · simpa [Nat.mul_comm] using Nat.mod_add_div y q
  apply (List.perm_ext_iff_of_nodup hyn hn).mpr
  intro a
  refine ⟨fun ha => hsub ha,?_⟩
  intro ha
  by_cases hmem : a∈ys
  · exact hmem
  · exfalso
    have hn' : (a::ys).Nodup := List.nodup_cons.mpr ⟨hmem,hyn⟩
    have hsub' : a::ys ⊆ fullLift q m xs := List.cons_subset.mpr ⟨ha,hsub⟩
    have := hn'.length_le_of_subset hsub'
    simp only [List.length_cons] at this
    omega

/-- No orbit implementation is assumed: `Perm` expresses the full-fiber conclusion
    of the exact order-multiplication argument. -/
theorem imbalance_invariant (q h : Nat) (xs ys : List Nat)
    (hx : ∀ x ∈ xs, x<q) (hy : ys.Perm (fullLift q (2*h+1) xs)) :
    2*(weight (q*(2*h+1)) ys : Int)-(ys.length : Int) =
      2*(weight q xs : Int)-(xs.length : Int) := by
  have hw := hy.countP_eq (upper (q*(2*h+1)))
  change weight (q*(2*h+1)) ys = weight (q*(2*h+1)) (fullLift q (2*h+1) xs) at hw
  rw [full_weight q h xs hx] at hw
  have hlen' := hy.length_eq.trans (full_length q (2*h+1) xs)
  have hlenI := congrArg (fun n : Nat => (n:Int)) hlen'
  have hwI := congrArg (fun n : Nat => (n:Int)) hw
  push_cast at hlenI hwI
  grind

/-- If q0 is divisible by C, the periodic drift condition at a full lift
    forces the lift multiplier to divide the original signed imbalance.
    This statement uses the doubled imbalance to avoid fractional notation. -/
theorem lift_divides_twice_imbalance (C q0 m b0 l0 l : Nat)
    (hc : 0<C) (hq : C∣q0) (hl : 2*l=m*b0+2*l0-b0)
    (hb : b0≤m*b0+2*l0) (hd : q0*m∣C*(3*(m*b0)+l)) :
    (m : Int) ∣ 2*(l0 : Int)-(b0 : Int) := by
  obtain ⟨q,hq⟩:=hq
  obtain ⟨k,hk⟩:=hd
  have h := congrArg (fun n : Nat => (n:Int)) hk
  push_cast at h
  have hq' := congrArg (fun n : Nat => (n:Int)) hq
  push_cast at hq'
  rw [hq'] at h
  have hC : (C:Int)≠0 := by omega
  have heq : (q:Int)*m*k=3*(m*b0)+l := by
    apply Int.eq_of_mul_eq_mul_left hC
    grind
  have hL := congrArg (fun n : Nat => (n:Int)) hl
  rw [Int.ofNat_sub hb] at hL
  push_cast at hL
  refine ⟨2*(q:Int)*k-7*b0,?_⟩
  grind

/-- With even base period the actual imbalance, not just its double,
    is divisible by the full lift multiplier. -/
theorem lift_divides_imbalance (C q0 m b l0 l : Nat)
    (hc : 0<C) (hq : C∣q0) (hl : l+(b/2)=m*(b/2)+l0)
    (hb : b%2=0) (hd : q0*m∣C*(3*(m*b)+l)) :
    (m : Int) ∣ (l0 : Int)-(b/2 : Nat) := by
  obtain ⟨q,hq⟩:=hq
  obtain ⟨k,hk⟩:=hd
  have h := congrArg (fun n : Nat => (n:Int)) hk
  push_cast at h
  have hq' := congrArg (fun n : Nat => (n:Int)) hq
  push_cast at hq'
  rw [hq'] at h
  have hC : (C:Int)≠0 := by omega
  have heq : (q:Int)*m*k=3*(m*b)+l := by
    apply Int.eq_of_mul_eq_mul_left hC
    grind
  have hL := congrArg (fun n : Nat => (n:Int)) hl
  push_cast at hL
  have hb' : (b:Int)=2*(b/2:Nat) := by omega
  refine ⟨(q:Int)*k-7*(b/2:Nat),?_⟩
  grind

#print axioms fullLift_perm
#print axioms fiber_weight
#print axioms full_weight
#print axioms imbalance_invariant
#print axioms lift_divides_imbalance
end BB6.Agent19PrimeLifts
