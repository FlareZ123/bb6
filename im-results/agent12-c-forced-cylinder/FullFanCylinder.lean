import FullSectionInverse
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12Fan
open BB6.Agent46

abbrev baseBad (d x y : Nat) : Prop :=
  2≤d ∧ 5≤y ∧ y%2=1 ∧ ((x+y)%4=1 ∨ (x+y)%4=2)
abbrev boxReady (d x y : Nat) : Prop :=
  3≤d ∧ 5≤y ∧ 2^d≤x+y ∧ (x+y)%2^d≠0 ∧ (x+y+1)%2^d≠0
abbrev fanGate (n s x y : Nat) : Prop :=
  (x+y+s)%2^(n+2)=0 ∧ (x+2*y)%2=(s+7+3*n)%2

def pa (n s x y : Nat) : Nat := (x+y+s)/2^(n+1)-(2+s)
def pk (n s x y : Nat) : Nat := (x+2*y-pa n s x y-7-3*n)/2
abbrev parentReady (n s x y : Nat) : Prop :=
  2+s≤(x+y+s)/2^(n+1) ∧ pa n s x y+7+3*n≤x+2*y

def fanReject : Nat → Nat → Nat → Nat → Bool
  | 0,d,x,y => decide (baseBad d x y)
  | f+1,d,x,y =>
    if baseBad d x y then true
    else if boxReady d x y then
      (if y%2=0 then fanReject f (d-1) (x+y-2) ((y-2)/2) else true) &&
      (List.range (d-2)).all (fun n =>
        ([0,1] : List Nat).all (fun s =>
          if fanGate n s x y then
            decide (parentReady n s x y) && fanReject f (d-(n+2)) (pa n s x y) (pk n s x y)
          else true))
    else false

private theorem pow_factor (d r : Nat) (h : r≤d) : 2^d=2^r*2^(d-r) := by
  conv => lhs; rw [show d=r+(d-r) by omega,Nat.pow_add]

private theorem sum_shift (d x y u v s : Nat) :
    (x+2^d*u)+(y+2^d*v)+s = (x+y+s)+2^d*(u+v) := by
  rw [Nat.mul_add]; omega
private theorem mass_shift (d x y u v : Nat) :
    (x+2^d*u)+2*(y+2^d*v) = (x+2*y)+2^d*(u+2*v) := by
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm (2^d) 2]
  omega
private theorem residue_shift (d r z w : Nat) (hr : r≤d) :
    (z+2^d*w)%2^r=z%2^r := by
  rw [pow_factor d r hr,Nat.mul_assoc,Nat.add_mul_mod_self_left]
private theorem large_nonzero_not_pow (d z t : Nat) (hl : 2^d≤z)
    (hm : z%2^d≠0) : z≠2^t := by
  intro he
  by_cases ht : d≤t
  · apply hm
    rw [he, ←Nat.dvd_iff_mod_eq_zero]
    exact Nat.pow_dvd_pow 2 ht
  · have hlt := Nat.pow_lt_pow_right (show 1<2 by decide) (show t<d by omega)
    omega

private theorem high_depth_lt (d n a s z : Nat) (hs : s≤1) (ha : a%2=s)
    (hm : z%2^d≠0) (he : z=2^(n+1)*(a+2+s)) : n+2<d := by
  by_cases hn : n+2<d
  · exact hn
  · exfalso
    have hp : a+2+s=2*((a+2+s)/2) := by omega
    have hD : 2^(n+2)∣z := by
      refine ⟨(a+2+s)/2,?_⟩
      calc
        z=2^(n+1)*(a+2+s) := he
        _=2^(n+1)*(2*((a+2+s)/2)) := congrArg (fun t => 2^(n+1)*t) hp
        _=2^(n+2)*((a+2+s)/2) := by rw [show 2^(n+2)=2^(n+1)*2 by rfl,Nat.mul_assoc]
    exact hm (Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : d≤n+2)) hD))

/-- Exhaustive overapproximation of all original-source parents of a large,
    nonzero-residue cylinder. Exceptional a=0/1 branches cannot occur. -/
theorem large_parent_cases (d x y a k : Nat)
    (hd : 3≤d) (hy : 5≤y) (hL : 2^d≤x+y)
    (h0 : (x+y)%2^d≠0) (h1 : (x+y+1)%2^d≠0)
    (h : sectionPreimageCriterion a k x y) :
    (y%2=0 ∧ a=x+y-2 ∧ k=(y-2)/2) ∨
    ∃ n s, n+2<d ∧ s≤1 ∧ a%2=s ∧
      x+y+s=2^(n+1)*(a+2+s) ∧ a+2*k+7+3*n=x+2*y := by
  have h8 : 8≤x+y := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<2) hd) hL
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,hk0,hk1] at h
        omega
      · simp only [sectionPreimageCriterion,if_pos rfl,if_neg hk0,if_neg hk1] at h
        obtain ⟨n,hn,_⟩ := h
        apply False.elim (large_nonzero_not_pow d (x+y) (n+3) hL h0 ?_)
        rw [Nat.pow_add]; exact hn
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageCriterion,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageCriterion,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [sectionPreimageCriterion, Nat.one_ne_zero, if_false, if_pos rfl, if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              obtain ⟨n,hn,_⟩ := h
              apply False.elim (large_nonzero_not_pow d (x+y+1) (n+4) (by omega) h1 ?_)
              rw [Nat.pow_add]; exact hn
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hl : 2*k≤a
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hl] at h
          exact Or.inl (by omega)
        · by_cases he : a%2=0
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_pos he] at h
            obtain ⟨n,hn,hM⟩ := h
            have hS : x+y+0=2^(n+1)*(a+2+0) := by
              rw [Nat.pow_succ,Nat.mul_assoc,show 2*(a+2+0)=2*(a-1)+6 by omega]
              omega
            exact Or.inr ⟨n,0,high_depth_lt d n a 0 (x+y) (by decide) he h0 (by simpa using hS),by decide,he,hS,by omega⟩
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_neg he] at h
            obtain ⟨n,hn,hM⟩ := h
            have ha : a%2=1 := by omega
            have hS : x+y+1=2^(n+1)*(a+2+1) := by
              rw [Nat.pow_succ,Nat.mul_assoc,show 2*(a+2+1)=2*(a-1)+8 by omega]
              exact hn
            exact Or.inr ⟨n,1,high_depth_lt d n a 1 (x+y+1) (by decide) ha h1 hS,by decide,ha,hS,by omega⟩

/-- Every large high-branch parent of a lifted target lies in the computed
    smaller parent cylinder. The bounds are checked rather than assumed. -/
theorem high_parent_lift (d n s x y u v a k : Nat)
    (hn : n+2<d) (hs : s≤1) (ha : a%2=s)
    (hS : (x+2^d*u)+(y+2^d*v)+s=2^(n+1)*(a+2+s))
    (hM : a+2*k+7+3*n=(x+2^d*u)+2*(y+2^d*v)) :
    fanGate n s x y ∧ (parentReady n s x y →
      ∃ U V, a=pa n s x y+2^(d-(n+2))*U ∧ k=pk n s x y+2^(d-(n+2))*V) := by
  let q := 2^(n+1)
  let b := 2^(d-(n+2))
  have hq : 1≤q := Nat.one_le_pow _ _ (by decide)
  have hL : 2^(n+2)=2*q := by simp [q,Nat.pow_succ,Nat.mul_comm]
  have hD : 2^d=2*q*b := by rw [pow_factor d (n+2) (by omega),hL]
  have hS' : x+y+s+2^d*(u+v)=q*(a+2+s) := by rw [←sum_shift]; exact hS
  have hM' : a+2*k+7+3*n=x+2*y+2^d*(u+2*v) := by rw [←mass_shift]; exact hM
  have hEven : a+2+s=2*((a+2+s)/2) := by omega
  have hDiv : (x+y+s+2^d*(u+v))%2^(n+2)=0 := by
    rw [hS',hEven,hL,Nat.mul_left_comm q 2,←Nat.mul_assoc]
    exact Nat.mul_mod_right _ _
  have hgS : (x+y+s)%2^(n+2)=0 := by
    rwa [residue_shift d (n+2) (x+y+s) (u+v) (by omega)] at hDiv
  have hMP : (x+2*y+2^d*(u+2*v))%2=(x+2*y)%2 := by
    simpa using residue_shift d 1 (x+2*y) (u+2*v) (by omega)
  have hgM : (x+2*y)%2=(s+7+3*n)%2 := by omega
  refine ⟨⟨hgS,hgM⟩,?_⟩
  intro hReady
  obtain ⟨hAQ,hKQ⟩ := hReady
  have hSD : (x+y+s+q*(2*b*(u+v)))/q=a+2+s := by
    have heq : x+y+s+q*(2*b*(u+v))=q*(a+2+s) := by
      rw [←hS',hD]
      simp only [Nat.mul_assoc,Nat.mul_left_comm q 2]
    rw [heq,Nat.mul_div_cancel_left _ (by omega : 0<q)]
  rw [Nat.add_mul_div_left _ _ (by omega : 0<q)] at hSD
  have hA : a=pa n s x y+2*b*(u+v) := by unfold pa; change 2+s≤(x+y+s)/q at hAQ; change a=(x+y+s)/q-(2+s)+2*b*(u+v); omega
  let V := (q-1)*(u+2*v)+v
  have hQ : q*(u+2*v)=(u+v)+V := by
    have heq : q=q-1+1 := by omega
    calc
      q*(u+2*v)=(q-1+1)*(u+2*v) := congrArg (fun t => t*(u+2*v)) heq
      _=(u+v)+V := by simp [V,Nat.add_mul]; omega
  have hMD : 2^d*(u+2*v)=2*b*(u+v)+2*b*V := by
    rw [hD,show 2*q*b*(u+2*v)=2*b*(q*(u+2*v)) by ac_rfl,hQ,Nat.mul_add]
  have hK : k=pk n s x y+b*V := by
    unfold pk
    rw [hMD] at hM'
    simp only [Nat.mul_assoc] at hM' hA
    omega
  exact ⟨2*(u+v),V,by simpa [b,Nat.mul_assoc,Nat.mul_left_comm b 2] using hA,hK⟩

private theorem direct_parent_lift (d x y u v a k : Nat)
    (hd : 1≤d) (hy : 2≤y)
    (h : (y+2^d*v)%2=0 ∧ a=(x+2^d*u)+(y+2^d*v)-2 ∧ k=(y+2^d*v-2)/2) :
    y%2=0 ∧ ∃ U V, a=x+y-2+2^(d-1)*U ∧ k=(y-2)/2+2^(d-1)*V := by
  obtain ⟨he,ha,hk⟩ := h
  have hD : 2^d=2*2^(d-1) := by simpa using pow_factor d 1 hd
  rw [hD] at he ha hk
  simp only [Nat.mul_assoc] at he ha hk
  refine ⟨by omega,2*(u+v),v,?_,?_⟩
  · simp only [Nat.mul_add,Nat.mul_left_comm (2^(d-1)) 2]
    omega
  · omega

private theorem base_bad_lift (d x y u v : Nat) (h : baseBad d x y) :
    5≤y+2^d*v ∧ (y+2^d*v)%2=1 ∧
    (((x+2^d*u)+(y+2^d*v))%4=1 ∨ ((x+2^d*u)+(y+2^d*v))%4=2) := by
  obtain ⟨hd,hy,he,hs⟩ := h
  have hP : (y+2^d*v)%2=y%2 := by simpa using residue_shift d 1 y v (by omega)
  have hS : ((x+2^d*u)+(y+2^d*v))%4=(x+y)%4 := by
    have h0 := sum_shift d x y u v 0
    simp only [Nat.add_zero] at h0
    rw [h0]
    simpa using residue_shift d 2 (x+y) (u+v) hd
  omega

/-- Sound finite full-parent certificate. It is an all-u,v statement, not
    a finite scan of the individual points in the cylinder. The interface
    requires only the original complete predecessor grammar and odd image. -/
theorem fanReject_sound (P : Nat → Nat → Prop)
    (hPred : ∀ x y, P x y → 5≤y → ∃ a k, P a k ∧ sectionPreimageCriterion a k x y)
    (hOdd : ∀ x y, P x y → 5≤y → y%2=1 → (x+y)%4=0 ∨ (x+y)%4=3)
    (f d x y : Nat) (h : fanReject f d x y=true) (u v : Nat) :
    ¬ P (x+2^d*u) (y+2^d*v) := by
  induction f generalizing d x y u v with
  | zero =>
    intro hp
    have hb : baseBad d x y := of_decide_eq_true h
    obtain ⟨hy,he,hs⟩ := base_bad_lift d x y u v hb
    have hh := hOdd _ _ hp hy he
    omega
  | succ f ih =>
    intro hp
    unfold fanReject at h
    by_cases hb : baseBad d x y
    · obtain ⟨hy,he,hs⟩ := base_bad_lift d x y u v hb
      have hh := hOdd _ _ hp hy he
      omega
    · rw [if_neg hb] at h
      by_cases hr : boxReady d x y
      · rw [if_pos hr,Bool.and_eq_true] at h
        obtain ⟨hDirect,hFan⟩ := h
        obtain ⟨hd,hy,hL,h0,h1⟩ := hr
        let X := x+2^d*u
        let Y := y+2^d*v
        have hY : 5≤Y := by dsimp [Y]; omega
        have hXY : X+Y=x+y+2^d*(u+v) := by simpa [X,Y] using sum_shift d x y u v 0
        have hXYL : 2^d≤X+Y := by omega
        have hXY0 : (X+Y)%2^d≠0 := by rw [hXY,Nat.add_mul_mod_self_left]; exact h0
        have hXY1 : (X+Y+1)%2^d≠0 := by
          rw [hXY,show x+y+2^d*(u+v)+1=x+y+1+2^d*(u+v) by omega,Nat.add_mul_mod_self_left]
          exact h1
        obtain ⟨a,k,hP,hC⟩ := hPred X Y hp hY
        rcases large_parent_cases d X Y a k hd hY hXYL hXY0 hXY1 hC with hA | ⟨n,s,hn,hs,ha,hS,hM⟩
        · obtain ⟨he,U,V,hA,hK⟩ := direct_parent_lift d x y u v a k (by omega) (by omega) hA
          rw [if_pos he] at hDirect
          exact ih (d-1) (x+y-2) ((y-2)/2) hDirect U V (by simpa [←hA,←hK] using hP)
        · obtain ⟨hg,hLift⟩ := high_parent_lift d n s x y u v a k hn hs ha hS hM
          have hN := (List.all_eq_true.mp hFan) n (List.mem_range.mpr (by omega))
          have hSm : s ∈ ([0,1] : List Nat) := by simp; omega
          have hB := (List.all_eq_true.mp hN) s hSm
          rw [if_pos hg,Bool.and_eq_true] at hB
          obtain ⟨hR,hChild⟩ := hB
          obtain ⟨U,V,hA,hK⟩ := hLift (of_decide_eq_true hR)
          exact ih (d-(n+2)) (pa n s x y) (pk n s x y) hChild U V (by simpa [←hA,←hK] using hP)
      · rw [if_neg hr] at h
        contradiction

def blankReach (x y : Nat) : Prop :=
  ∃ t, BB6.Agent8Section.run secNext t (some (5,1))=some (x,y)

theorem blankReach_parent (x y : Nat) (hr : blankReach x y) (hy : 5≤y) :
    ∃ a k, blankReach a k ∧ sectionPreimageCriterion a k x y := by
  obtain ⟨t,ht⟩ := hr
  cases t with
  | zero =>
    simp [BB6.Agent8Section.run] at ht
    omega
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at ht
    | some p =>
      rcases p with ⟨a,k⟩
      have he : secNext (a,k)=some (x,y) := by simpa [BB6.Agent8Section.run,hp] using ht
      exact ⟨a,k,⟨t,hp⟩,(complete_section_inverse a k x y hy).mp he⟩

theorem blankReach_odd (x y : Nat) (hr : blankReach x y) (hy : 5≤y) (ho : y%2=1) :
    (x+y)%4=0 ∨ (x+y)%4=3 := by
  obtain ⟨t,ht⟩ := hr
  cases t with
  | zero =>
    simp [BB6.Agent8Section.run] at ht
    omega
  | succ t =>
    exact BB6.Agent3.blank_section_odd_image t x y ht hy ho

theorem blankFanReject_sound (f d x y : Nat) (h : fanReject f d x y=true) (u v time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x+2^d*u,y+2^d*v) := by
  intro ht
  exact fanReject_sound blankReach blankReach_parent blankReach_odd f d x y h u v ⟨time,ht⟩

#print axioms large_parent_cases
#print axioms high_parent_lift
#print axioms fanReject_sound
#print axioms blankFanReject_sound
end BB6.Agent12Fan
