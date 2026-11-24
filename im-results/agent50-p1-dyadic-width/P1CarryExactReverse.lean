import P1CarryExactSource
import P1CarryExtinction

/-! Exact source-to-carry reverse direction, without a bounded-depth model. -/
namespace BB6.P1CarryExact
open BB6.Agent1Quarter BB6.Agent47P1
open BB6.P1CarryExtinction

theorem source_even_left (b0 d0 b d m : Nat) (hb0 : b0%2=0)
    (h : OddCone b0 d0 b d m) : b%2=0 := by
  cases h with
  | root => exact hb0
  | parent _ _ _ _ _ _ _ _ _ _ _ _ _ => omega

theorem source_odd_right (b0 d0 b d m : Nat) (hd0 : d0%2=1)
    (h : OddCone b0 d0 b d m) : d%2=1 := by
  cases h with
  | root => exact hd0
  | parent _ _ _ _ _ _ _ _ _ _ _ _ hc => omega

/-- Recover the exact gap arithmetic from the original OddCone constructors. -/
theorem source_to_legal (n b d m : Nat) (hn : 14≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m) :
    LegalGap n m ((d-1)/2) ((b+12)/2) := by
  have hT := total_large n hn
  have hp := pow2_ge_1100_mul n hn
  have hrootMass : (14*2^n-2*n-16)+3+2*n+13=2*total n := by simp [total]; omega
  induction h with
  | root =>
    have hW : ((14*2^n-2*n-16)+12)/2 = total n-n-2 := by simp [total]; omega
    rw [hW]
    exact LegalGap.root
  | parent b d m t k c hcone hb hb4 hd hi hk hc ih =>
    have hm := odd_cone_mass _ _ b d m hcone
    have hP := (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
    let v := (d-1)/2
    let w := (b+12)/2
    let v' := ((c+4)-1)/2
    let w' := ((2*k-4)+12)/2
    have hstart : 10≤w ∧ w%2=0 := by dsimp [w]; omega
    have hend : 2≤v' ∧ 6≤w' := by dsimp [v',w']; omega
    have hMass : v'+w'+n+(m+(t+1))+1=total n := by dsimp [v',w']; omega
    have hrec : v+total n = 2^(t+1)*v'+(n+m+3) := by
      have hcv : c+3=2*v' := by dsimp [v']; omega
      have hs : v+total n=d+b/2+3+(n+m+3) := by dsimp [v]; omega
      rw [hs,hP.1,hcv,Nat.pow_succ,Nat.mul_assoc]
    have he := LegalGap.edge m v w (t+1) v' w' ih (by omega) hstart hend hMass hrec
    simpa [v',w',Nat.add_assoc] using he

/-- Split the unselected tail of a gap into exact unit-cost states. -/
theorem extend_zeros (n m v w k v' w' : Nat) (hn : 14≤n) (hm : 0<m)
    (h : Micro n m v w) (hv' : 1≤v')
    (hpow : v=2^k*v') (hMass : v'+w'+n+(m+k)+1=total n) :
    Micro n (m+k) v' w' := by
  induction k generalizing m v w with
  | zero =>
    have hm0 := micro_mass n m v w hn h
    simp at hpow hMass ⊢
    have hw : w=w' := by omega
    simpa [hpow,hw] using h
  | succ k ih =>
    let u := 2^k*v'
    let z := w+u-1
    have hu : 1≤u := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
    have hV : v=2*u := by
      dsimp [u]
      rw [hpow,Nat.pow_succ]; ac_rfl
    have hm0 := micro_mass n m v w hn h
    have hW : w+total n=2*z+(n+m+3) := by dsimp [z]; omega
    have hnext := Micro.zero m v w u z h hm hV hW
    have hMass' : v'+w'+n+(m+1+k)+1=total n := by omega
    have hfin := ih (m+1) u z (by omega) hnext rfl hMass'
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfin

/-- Every original gap path is a microtrace at all costs.  The converse was
    proved up to n, where all guards hold automatically. -/
theorem legal_to_micro (n m v w : Nat) (hn : 14≤n)
    (h : LegalGap n m v w) : Micro n m v w := by
  induction h with
  | root => exact Micro.root
  | edge m v w e v' w' h he hstart hend hMass hrec ih =>
    let k := e-1
    let u := 2^k*v'
    let z := w/2
    have hE : k+1=e := by dsimp [k]; omega
    have hpow : 2^e*v'=2*u := by rw [← hE,Nat.pow_succ]; dsimp [u]; ac_rfl
    have hv : v+total n=2*u+(n+m+3) := by rw [hrec,hpow]
    have hw : w=2*z := by dsimp [z]; omega
    have hnext := Micro.one m v w u z ih hv hw
    have hMass' : v'+w'+n+(m+1+k)+1=total n := by omega
    have hfin := extend_zeros n (m+1) u z k v' w' hn (by omega) hnext (by omega) rfl hMass'
    have heq : m+1+k=m+e := by omega
    simpa [heq] using hfin

theorem source_to_micro (n b d m : Nat) (hn : 14≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b d m) :
    Micro n m ((d-1)/2) ((b+12)/2) :=
  legal_to_micro n _ _ _ hn (source_to_legal n b d m hn h)

theorem micro_prefix (n m v w K : Nat) (h : Micro n m v w) (hK : K≤m) :
    ∃ v' w', Micro n K v' w' := by
  induction h with
  | root =>
    have he : K=0 := by omega
    subst K
    exact ⟨_,_,Micro.root⟩
  | one m v w v' w' h hv hw ih =>
    by_cases he : K=m+1
    · subst K; exact ⟨_,_,Micro.one m v w v' w' h hv hw⟩
    · exact ih (by omega)
  | zero m v w v' w' h hm hv hw ih =>
    by_cases he : K=m+1
    · subst K; exact ⟨_,_,Micro.zero m v w v' w' h hm hv hw⟩
    · exact ih (by omega)

theorem bitMass_snoc (j : Nat) (xs : List Bool) (b : Bool) :
    bitMass j (xs++[b])=bitMass j xs+(if b then 2^(j+xs.length) else 0) := by
  induction xs generalizing j with
  | nil => simp [bitMass]
  | cons a as ih =>
    simp only [List.cons_append,bitMass,ih,List.length_cons]
    have he : j+1+as.length=j+(as.length+1) := by omega
    rw [he]; omega

/-- Word identity holds even beyond n; cutoff only used for modular reduction. -/
theorem micro_word_identity (n m v w : Nat) (h : Micro n m v w) (hm : 0<m) :
    ∃ xs : List Bool, xs.length+1=m ∧
      2^m*v+expr n xs=1+total n*(1+bitMass 1 xs) := by
  induction h with
  | root => omega
  | one m v w v' w' h hv hw ih =>
    by_cases hm0 : m=0
    · subst m
      cases h with
      | root =>
        refine ⟨[],by simp,?_⟩
        simp [expr,absSum,bitMass]
        omega
    · obtain ⟨xs,hx,he⟩ := ih (by omega)
      refine ⟨xs++[true],by simp; omega,?_⟩
      have hidx : 1+xs.length=m := by omega
      have hv' : 2^m*v+2^m*total n=2^m*(2*v')+2^m*(n+m+3) := by
        rw [← Nat.mul_add,← Nat.mul_add,hv]
      have hweight : weight n m=2^m*(n+m+3) := by
        unfold weight
        rw [Nat.mul_comm]; congr 1; omega
      calc
        2^(m+1)*v'+expr n (xs++[true]) =
            (2^m*(2*v')+2^m*(n+m+3))+expr n xs := by
          rw [expr_snoc,hidx,Nat.pow_succ]
          simp only [ite_true,hweight]
          ac_rfl
        _ = (2^m*v+2^m*total n)+expr n xs := by rw [← hv']
        _ = (2^m*v+expr n xs)+total n*2^m := by ac_rfl
        _ = (1+total n*(1+bitMass 1 xs))+total n*2^m := by rw [he]
        _ = 1+total n*(1+bitMass 1 (xs++[true])) := by
          rw [bitMass_snoc,hidx]
          simp only [ite_true]
          simp only [Nat.mul_add,Nat.mul_one]
          ac_rfl
  | zero m v w v' w' h hm0 hv hw ih =>
    obtain ⟨xs,hx,he⟩ := ih hm0
    refine ⟨xs++[false],by simp; omega,?_⟩
    rw [expr_snoc,bitMass_snoc]
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero,Nat.pow_succ]
    rw [Nat.mul_assoc,← hv]
    exact he

/-- Original positive-cost microtraces below n satisfy the carry congruence. -/
theorem micro_width_pos (n m v w : Nat) (h : Micro n m v w)
    (hm : 0<m) (hmn : m≤n) : 0<width m n := by
  obtain ⟨xs,hx,he⟩ := micro_word_identity n m v w h hm
  have hdiv : 2^m ∣ total n := by
    unfold total
    have hp : 2^m ∣ 2^n := Nat.pow_dvd_pow 2 hmn
    exact Nat.dvd_mul_left_of_dvd hp 7
  obtain ⟨a,ha⟩ := hdiv
  have hmod := congrArg (fun t : Nat => t%2^m) he
  have hP : 1<2^m := by
    have hp := Nat.pow_lt_pow_right (show 1<2 by decide) hm
    simpa using hp
  rw [Nat.add_comm (2^m*v),Nat.add_mul_mod_self_left,ha,Nat.mul_assoc,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hP] at hmod
  exact (width_pos_iff m n hm).mpr ⟨xs,hx,hmod⟩

/-- Exact unrestricted prefix existence, in the original source relation. -/
theorem source_width_iff (n K : Nat) (hn : 14≤n) (hK : 0<K) (hKn : K≤n) :
    0<width K n ↔ ∃ b d m, K≤m ∧ OddCone (14*2^n-2*n-16) 3 b d m := by
  constructor
  · intro h
    obtain ⟨xs,hx,he⟩ := (width_pos_iff K n hK).mp h
    rw [expr_eq,← hx] at he
    obtain ⟨b,d,hcone⟩ := source_prefix_to_oddcone n xs hn (by omega) he
    exact ⟨b,d,xs.length+1,by omega,hcone⟩
  · rintro ⟨b,d,m,hm,hcone⟩
    obtain ⟨v,w,hM⟩ := micro_prefix n m _ _ K (source_to_micro n b d m hn hcone) hm
    exact micro_width_pos n K v w hM hK hKn

/-- An empty prefix layer excludes every right-five source history, including
    histories with cost beyond n. -/
theorem source_width_zero_no_right_five (n K b m : Nat) (hn : 14≤n)
    (hK : 0<K) (hKn : K≤n) (hz : width K n=0) :
    ¬ OddCone (14*2^n-2*n-16) 3 b 5 m := by
  intro h
  have hm : m<K := by
    by_cases hge : K≤m
    · have hp := (source_width_iff n K hn hK hKn).mpr ⟨b,5,m,hge,h⟩
      omega
    · omega
  have hmpos : 0<m := by
    cases h with
    | parent _ _ _ _ _ _ _ _ _ _ _ _ _ => omega
  have hMicro := source_to_micro n b 5 m hn h
  have hBounds := micro_bounds n m ((5-1)/2) ((b+12)/2) hn hMicro (by omega)
  have hv := hBounds.1 hmpos
  omega

theorem source_right_five_width_pos (n K b m : Nat) (hn : 14≤n)
    (hK : 0<K) (hKn : K≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) : 0<width K n := by
  by_cases hz : width K n=0
  · exact False.elim (source_width_zero_no_right_five n K b m hn hK hKn hz h)
  · omega

#print axioms source_right_five_width_pos
#print axioms source_to_legal
#print axioms legal_to_micro
#print axioms micro_word_identity
#print axioms source_width_iff
#print axioms source_width_zero_no_right_five
end BB6.P1CarryExact
