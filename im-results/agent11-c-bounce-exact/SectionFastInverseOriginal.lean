import FullSectionInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46

def fastCap (x y : Nat) := Nat.log2 (x+y+1)+1

def fastOne (x y n : Nat) : List (Nat × Nat) :=
 let e := x+2*y
 let f := 2^(n+1)
 let evenA := (x+y)/f-2
 let oddA := (x+y+1)/f-3
 [(0,(e-9-3*n)/2), (1,(e-11-3*n)/2),
  (evenA,(e-evenA-7-3*n)/2),
  (oddA,(e-oddA-7-3*n)/2)]

def fastUnfiltered (x y : Nat) : List (Nat × Nat) :=
  ((List.range (fastCap x y)).flatMap (fastOne x y)) ++
    [(x+2,0), (x+y-2,(y-2)/2), (1,2), (1,3)]

theorem pow_depth_bounded (x y n:Nat) (h:2^n≤x+y+1) : n<fastCap x y := by
  have hp : x+y+1≠0 := by omega
  have hh := (Nat.le_log2 hp).mpr h
  unfold fastCap
  omega

theorem level_present (x y n:Nat) (hn:n<fastCap x y)
    (a k:Nat) (h:(a,k)∈fastOne x y n) :
    (a,k)∈fastUnfiltered x y := by
  unfold fastUnfiltered
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  exact ⟨n,List.mem_range.mpr hn,h⟩

theorem direct_present (x y a k:Nat)
  (ha:a=x+y-2) (hk:k=(y-2)/2) :
  (a,k)∈fastUnfiltered x y := by
  simp [fastUnfiltered,ha,hk]

theorem zero_depth_present (x y k n:Nat)
    (hk:2≤k) (hS:x+y=2^n*8)
    (hcost:2*k+9+3*n=x+2*y) :
    (0,k)∈fastUnfiltered x y := by
  have h2 : 2^n ≤ x+y+1 := by
    have hp:0<8:=by decide
    have hh:=Nat.le_mul_of_pos_right (2^n) hp
    omega
  have hnum:(x+2*y-9-3*n)/2=k := by omega
  apply level_present x y n (pow_depth_bounded x y n h2)
  simp [fastOne,hnum]

theorem one_depth_present (x y k n:Nat)
    (hk:4≤k) (hS:x+y+1=2^n*16)
    (hcost:(2*k-3)+16+3*n=x+2*y+2) :
    (1,k)∈fastUnfiltered x y := by
  have h2 : 2^n ≤ x+y+1 := by
    have hh:=Nat.le_mul_of_pos_right (2^n) (show 0<16 by decide)
    omega
  have hnum:(x+2*y-11-3*n)/2=k := by omega
  apply level_present x y n (pow_depth_bounded x y n h2)
  simp [fastOne,hnum]

theorem even_depth_present (x y a k n:Nat)
    (ha:2≤a) (hk:0<k) (hregion:a<2*k)
    (hS:x+y=2^n*(2*(a-1)+6))
    (hcost:(2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y) :
    (a,k)∈fastUnfiltered x y := by
  have hS' : x+y = 2^(n+1)*(a+2) := by
    have hh:2*(a-1)+6=2*(a+2) := by omega
    rw [hh] at hS
    rw [Nat.pow_succ]
    calc
      x+y=2^n*(2*(a+2)) := hS
      _=(2^n*2)*(a+2) := by ac_rfl
  have h2 : 2^n≤x+y+1 := by
    have hp:0<a+2:=by omega
    have hh:=Nat.le_mul_of_pos_right (2^(n+1)) hp
    have hi:2^n≤2^(n+1):=by
      have hpow:0<2^n:=Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      omega
    omega
  have ha' : (x+y)/(2^(n+1))-2=a := by
    rw [hS',Nat.mul_div_cancel_left (a+2) (Nat.pow_pos (by decide))]
    omega
  have hcost': 2*k+a+7+3*n=x+2*y := by omega
  have hk' : (x+2*y-a-7-3*n)/2=k := by omega
  apply level_present x y n (pow_depth_bounded x y n h2)
  simp [fastOne,ha',hk']

theorem odd_depth_present (x y a k n:Nat)
    (ha:3≤a) (hk:0<k) (hregion:a<2*k)
    (hS:x+y+1=2^n*(2*(a-1)+8))
    (hcost:(2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) :
    (a,k)∈fastUnfiltered x y := by
  have hS' : x+y+1 = 2^(n+1)*(a+3) := by
    have hh:2*(a-1)+8=2*(a+3) := by omega
    rw [hh] at hS
    rw [Nat.pow_succ]
    calc
      x+y+1=2^n*(2*(a+3)) := hS
      _=(2^n*2)*(a+3) := by ac_rfl
  have h2 : 2^n ≤ x+y+1 := by
    have hh:=Nat.le_mul_of_pos_right (2^(n+1)) (show 0<a+3 by omega)
    have hi:2^n≤2^(n+1):=by
      rw [Nat.pow_succ]
      have hp:0<2^n:=Nat.pow_pos (by decide)
      omega
    omega
  have ha' : (x+y+1)/(2^(n+1))-3=a := by
    rw [hS',Nat.mul_div_cancel_left (a+3) (Nat.pow_pos (by decide))]
    omega
  have hcost': 2*k+a+7+3*n=x+2*y := by omega
  have hk' : (x+2*y-a-7-3*n)/2=k := by omega
  apply level_present x y n (pow_depth_bounded x y n h2)
  simp [fastOne,ha',hk']

theorem fastUnfiltered_length (x y:Nat) :
    (fastUnfiltered x y).length=4*fastCap x y+4 := by
  have h : ∀ l : List Nat, (l.map (fun _ => 4)).sum = 4*l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]; omega
  simp [fastUnfiltered, List.length_flatMap, fastOne, h]

theorem fastUnfiltered_complete (a k x y:Nat) (hy:5≤y)
    (h:secNext (a,k)=some (x,y)) :
    (a,k)∈fastUnfiltered x y := by
  have hi := (complete_section_inverse a k x y hy).mp h
  by_cases ha0:a=0
  · by_cases hk0:k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at hi
    · by_cases hk1:k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hi
        omega
      · have hh : ∃ n:Nat, x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageCriterion,ha0,hk0,hk1] using hi
        obtain ⟨n,hS,hcost⟩:=hh
        subst a
        apply zero_depth_present x y k n (by omega) hS
        omega
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hi
      · by_cases hk1:k=1
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at hi
        · by_cases hk2:k=2
          · unfold fastUnfiltered
            apply List.mem_append.mpr
            right
            simp [ha1,hk2]
          · by_cases hk3:k=3
            · unfold fastUnfiltered
              apply List.mem_append.mpr
              right
              simp [ha1,hk3]
            · have hh : ∃ n:Nat, x+y+1=2^n*16 ∧
                (2*k-3)+16+3*n=x+2*y+2 := by
                simpa [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] using hi
              obtain ⟨n,hS,hcost⟩:=hh
              subst a
              exact one_depth_present x y k n (by omega) hS hcost
    · by_cases hk0:k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hi
      · by_cases hregion:2*k≤a
        · have hh : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageCriterion,ha0,ha1,hk0,hregion] using hi
          obtain ⟨hx,hy'⟩:=hh
          apply direct_present x y a k
          · omega
          · omega
        · by_cases haEven:a%2=0
          · have hh : ∃ n:Nat,
              x+y=2^n*(2*(a-1)+6) ∧
              (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
                simpa [sectionPreimageCriterion,ha0,ha1,hk0,hregion,haEven] using hi
            obtain ⟨n,hS,hcost⟩:=hh
            exact even_depth_present x y a k n (by omega) (by omega)
              (by omega) hS hcost
          · have hh : ∃ n:Nat,
              x+y+1=2^n*(2*(a-1)+8) ∧
              (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2 := by
                simpa [sectionPreimageCriterion,ha0,ha1,hk0,hregion,haEven] using hi
            obtain ⟨n,hS,hcost⟩:=hh
            exact odd_depth_present x y a k n (by omega) (by omega)
              (by omega) hS hcost

def fastCandidates (x y:Nat) : List (Nat×Nat) :=
  (fastUnfiltered x y).filter (fun p => secNext p = some (x,y))

theorem fastCandidates_exact (a k x y:Nat) (hy:5≤y) :
    (a,k)∈fastCandidates x y ↔ secNext (a,k)=some (x,y) := by
  simp only [fastCandidates, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨fastUnfiltered_complete a k x y hy h,h⟩

theorem fastCandidates_length_le (x y:Nat) :
    (fastCandidates x y).length ≤ 4*fastCap x y+4 := by
  unfold fastCandidates
  have hl : (List.filter (fun p => secNext p = some (x,y))
      (fastUnfiltered x y)).length ≤ (fastUnfiltered x y).length :=
    List.length_filter_le _ _
  rw [fastUnfiltered_length] at hl
  exact hl

#print axioms fastCandidates_exact
#print axioms fastCandidates_length_le
end BB6.Agent11Fast
