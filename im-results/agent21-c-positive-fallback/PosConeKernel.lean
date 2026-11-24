import Lean

namespace BB6.Agent21PositiveCone
abbrev P := Nat × Nat

-- The unmodified predicate from FullSectionInverse.lean, isolated for local checking.
def inverse (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else ∃ n : Nat,
      x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y
  else if a=1 then
    if k=0 then False
    else if k=1 then False
    else if k=2 then x=2 ∧ y=5
    else if k=3 then x=0 ∧ y=7
    else ∃ n : Nat,
      x+y+1=2^n*16 ∧ (2*k-3)+16+3*n=x+2*y+2
  else if k=0 then False
  else if 2*k≤a then x=a-2*k ∧ y=2*k+2
  else if a%2=0 then ∃ n : Nat,
    x+y=2^n*(2*(a-1)+6) ∧
    (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y
  else ∃ n : Nat,
    x+y+1=2^n*(2*(a-1)+8) ∧
    (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2

def v2Aux : Nat → Nat → Nat
  | 0,_ => 0
  | f+1,q => if q%2=0 then 1+v2Aux f (q/2) else 0

def depth (q : Nat) : Nat := v2Aux (q.log2+1) q

theorem v2Aux_bound (f q n : Nat) (hf : n≤f) (hd : 2^n∣q) : n≤v2Aux f q := by
  induction n generalizing f q with
  | zero => omega
  | succ n ih =>
    cases f with
    | zero => omega
    | succ f =>
      obtain ⟨w,hw⟩ := hd
      have he : q=2*(2^n*w) := by rw [hw,Nat.pow_succ]; ac_rfl
      have hm : q%2=0 := by rw [he]; simp
      have hdiv : 2^n∣q/2 := by
        refine ⟨w,?_⟩
        rw [he,Nat.mul_div_cancel_left _ (by decide : 0<(2:Nat))]
      simp only [v2Aux,hm,if_true]
      have h := ih f (q/2) (by omega) hdiv
      omega

theorem depth_bound (q n : Nat) (hq : 0<q) (hd : 2^n∣q) : n≤depth q := by
  have hle := Nat.le_of_dvd hq hd
  have hlog := (Nat.le_log2 (by omega : q≠0)).mpr hle
  exact v2Aux_bound _ _ _ (by omega) hd

def Q (x y : Nat) := x+y+(x+y)%2

def direct (x y : Nat) : List P :=
  if y%2=0 then [(x+y-2,(y-2)/2)] else []

def specials (x y : Nat) : List P :=
  (if x=2 ∧ y=5 then [(1,2)] else []) ++
  (if x=0 ∧ y=7 then [(1,3)] else [])

def level (x y n : Nat) : List P :=
  let e := x+2*y
  let o := (x+y)%2
  let q := Q x y
  let a := q/2^(n+1)-2-o
  let k := (e-a-7-3*n)/2
  let k0 := (e-9-3*n)/2
  let k1 := (e-11-3*n)/2
  (if o=0 ∧ q=2^n*8 ∧ 2≤k0 ∧ 2*k0+9+3*n=e then [(0,k0)] else []) ++
  (if o=1 ∧ q=2^n*16 ∧ 4≤k1 ∧ 2*k1+11+3*n=e then [(1,k1)] else []) ++
  (if 2≤a ∧ 0<k ∧ a<2*k ∧ a%2=o ∧ q=2^(n+1)*(a+2+o) ∧
      2*k+a+7+3*n=e then [(a,k)] else [])

def parents (x y : Nat) : List P :=
  direct x y ++ specials x y ++ (List.range (depth (Q x y)+1)).flatMap (level x y)

private theorem level_mem (x y n : Nat) (p : P) (hn : n≤depth (Q x y))
    (hp : p∈level x y n) : p∈parents x y := by
  unfold parents
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨n,List.mem_range.mpr (by omega),hp⟩

private theorem sum_par (x y n b : Nat) (h : x+y=2^n*(2*b)) : (x+y)%2=0 := by
  rw [h,Nat.mul_left_comm]; simp

private theorem sum_par_one (x y n b : Nat) (h : x+y+1=2^n*(2*b)) : (x+y)%2=1 := by
  have hh : (x+y+1)%2=0 := by rw [h,Nat.mul_left_comm]; simp
  omega

private theorem ordinary_mem (a k x y n o : Nat) (hy : 5≤y)
    (ho : (x+y)%2=o) (ha : 2≤a) (hk : 0<k) (hreg : a<2*k)
    (hpar : a%2=o) (hq : Q x y=2^(n+1)*(a+2+o))
    (hc : 2*k+a+7+3*n=x+2*y) : (a,k)∈parents x y := by
  have hpos : 0<Q x y := by unfold Q; omega
  have hdiv : 2^n∣Q x y := by
    rw [hq,Nat.pow_succ,Nat.mul_assoc]
    exact Nat.dvd_mul_right _ _
  apply level_mem x y n (a,k) (depth_bound _ _ hpos hdiv)
  have hA : Q x y/2^(n+1)-2-o=a := by
    rw [hq,Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0<(2:Nat)))]
    omega
  have hK : (x+2*y-a-7-3*n)/2=k := by omega
  simp only [level,ho,hA,hK]
  apply List.mem_append.mpr
  right
  simp [ha,hk,hreg,hpar,hq,hc]

theorem parents_complete (a k x y : Nat) (hy : 5≤y)
    (h : inverse a k x y) : (a,k)∈parents x y := by
  have hpos : 0<Q x y := by unfold Q; omega
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [inverse,hk0] at h
    · by_cases hk1 : k=1
      · simp [inverse,hk0,hk1] at h; omega
      · simp only [inverse,if_true,if_neg hk0,if_neg hk1] at h
        obtain ⟨n,hs,hc⟩ := h
        have ho : (x+y)%2=0 := by rw [hs]; simp [Nat.mul_mod]
        have hq : Q x y=2^n*8 := by unfold Q; rw [ho,Nat.add_zero,hs]
        have hd : 2^n∣Q x y := by rw [hq]; exact Nat.dvd_mul_right _ _
        have hk' : (x+2*y-9-3*n)/2=k := by omega
        apply level_mem x y n (0,k) (depth_bound _ _ hpos hd)
        have hk2 : 2≤k := by omega
        have hc' : 2*k+9+3*n=x+2*y := by omega
        simp [level,ho,hq,hk',hk2,hc']
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · simp [inverse,hk0] at h
      · by_cases hk1 : k=1
        · simp [inverse,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [inverse,hk0,hk1,hk2] at h
            obtain ⟨rfl,rfl⟩ := h
            simp [parents,specials,hk2]
          · by_cases hk3 : k=3
            · simp [inverse,hk0,hk1,hk2,hk3] at h
              obtain ⟨rfl,rfl⟩ := h
              simp [parents,specials,hk3]
            · simp only [inverse,if_false,if_true,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3,show ¬(1:Nat)=0 by decide] at h
              obtain ⟨n,hs,hc⟩ := h
              have ho : (x+y)%2=1 := by
                have hh : (x+y+1)%2=0 := by rw [hs]; simp [Nat.mul_mod]
                omega
              have hq : Q x y=2^n*16 := by unfold Q; rw [ho,Nat.add_zero,hs]
              have hd : 2^n∣Q x y := by rw [hq]; exact Nat.dvd_mul_right _ _
              have hk' : (x+2*y-11-3*n)/2=k := by omega
              apply level_mem x y n (1,k) (depth_bound _ _ hpos hd)
              have hk4 : 4≤k := by omega
              have hc' : 2*k+11+3*n=x+2*y := by omega
              simp [level,ho,hq,hk',hk4,hc']
    · by_cases hk0 : k=0
      · simp [inverse,ha0,ha1,hk0] at h
      · by_cases hr : 2*k≤a
        · simp [inverse,ha0,ha1,hk0,hr] at h
          obtain ⟨hx,hy'⟩ := h
          have ha : x+y-2=a := by omega
          have hk : (y-2)/2=k := by omega
          have he : y%2=0 := by omega
          simp [parents,direct,ha,hk,he]
        · by_cases he : a%2=0
          · simp only [inverse,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hr,if_pos he] at h
            obtain ⟨n,hs,hc⟩ := h
            have hs' : x+y=2^n*(2*(a+2)) := by rw [hs,show 2*(a-1)+6=2*(a+2) by omega]
            have ho := sum_par x y n (a+2) hs'
            have hq : Q x y=2^(n+1)*(a+2+0) := by
              simp only [Q,ho,Nat.add_zero,Nat.pow_succ]
              rw [hs']; ac_rfl
            exact ordinary_mem a k x y n 0 hy ho (by omega) (by omega) (by omega) he hq (by omega)
          · simp only [inverse,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hr,if_neg he] at h
            obtain ⟨n,hs,hc⟩ := h
            have hs' : x+y+1=2^n*(2*(a+3)) := by rw [hs,show 2*(a-1)+8=2*(a+3) by omega]
            have ho := sum_par_one x y n (a+3) hs'
            have hq : Q x y=2^(n+1)*(a+2+1) := by
              simp only [Q,ho,Nat.pow_succ]
              rw [hs']; ac_rfl
            exact ordinary_mem a k x y n 1 hy ho (by omega) (by omega) (by omega) (by omega) hq (by omega)

def bad (seen : P→Bool) (p : P) : Bool :=
  !seen p || decide (5≤p.2 ∧ p.2%2=1 ∧ ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

def check (seen : P→Bool) : Nat → P → Bool
  | 0,p => bad seen p
  | f+1,p => bad seen p || (decide (5≤p.2) && (parents p.1 p.2).all (check seen f))

theorem check_sound (reach : P→Prop) (seen : P→Bool)
    (hbad : ∀ p, bad seen p=true → ¬reach p)
    (hparent : ∀ p, 5≤p.2 → reach p → ∃ a k, reach (a,k) ∧ inverse a k p.1 p.2)
    (f : Nat) (p : P) (h : check seen f p=true) : ¬reach p := by
  induction f generalizing p with
  | zero => exact hbad p h
  | succ f ih =>
    simp only [check,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with h|⟨hy,hs⟩
    · exact hbad p h
    · intro hr
      obtain ⟨a,k,hr',hi⟩ := hparent p hy hr
      exact ih (a,k) (List.all_eq_true.mp hs (a,k) (parents_complete a k p.1 p.2 hy hi)) hr'

#print axioms parents_complete
#print axioms check_sound
end BB6.Agent21PositiveCone
