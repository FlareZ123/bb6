import LowThreeImageOriginal
import LowFourImageOriginal
import Lean.Elab.Tactic.Omega
namespace BB6.Agent11Fast
open BB6.Agent46

def smallCap (x shift:Nat) := Nat.log2 (x+shift+1)+1

theorem smallPowBound (x shift n:Nat) (h:2^n≤x+shift+1) : n<smallCap x shift := by
  have hx:x+shift+1≠0 := by omega
  have hh: n≤Nat.log2 (x+shift+1) := (Nat.le_log2 hx).mpr h
  unfold smallCap
  omega

def lowThreeOne (x n:Nat) : List (Nat×Nat) :=
  let a := (x+6)/(2^(n+1))-3
  let k := (x+1-a-3*n)/2
  [(1,(x-3-3*n)/2),(a,k)]

def lowThreeList (x:Nat) : List (Nat×Nat) :=
  ((List.range (smallCap x 6)).flatMap (lowThreeOne x))++[(1,1)]

def lowFourOne (x n:Nat) : List (Nat×Nat) :=
  let a := (x+4)/(2^(n+1))-2
  let k := (x+1-a-3*n)/2
  [(0,(x-1-3*n)/2),(a,k)]

def lowFourList (x:Nat) : List (Nat×Nat) :=
  ((List.range (smallCap x 4)).flatMap (lowFourOne x))++[(0,1),(x+2,1)]

theorem lowThreeIndex (x n a k:Nat) (hn:n<smallCap x 6)
    (h:(a,k)∈lowThreeOne x n) : (a,k)∈lowThreeList x := by
  unfold lowThreeList
  exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
    ⟨n,List.mem_range.mpr hn,h⟩))

theorem lowFourIndex (x n a k:Nat) (hn:n<smallCap x 4)
    (h:(a,k)∈lowFourOne x n) : (a,k)∈lowFourList x := by
  unfold lowFourList
  exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
    ⟨n,List.mem_range.mpr hn,h⟩))

theorem lowThreeComplete (a k x:Nat)
    (h:secNext (a,k)=some (x,3)) : (a,k)∈lowThreeList x := by
  have hi := (threeImage_exact a k x).mp h
  by_cases ha0:a=0
  · simp [threeImageCriterion,ha0] at hi
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · simp [threeImageCriterion,ha0,ha1,hk0] at hi
      · by_cases hk1:k=1
        · unfold lowThreeList
          apply List.mem_append.mpr
          right
          simpa [ha1,hk1] using (show (1,1)∈([(1,1)]:List (Nat×Nat)) by simp)
        · by_cases hk2:k=2
          · simp [threeImageCriterion,ha0,ha1,hk0,hk1,hk2] at hi
          · by_cases hk3:k=3
            · simp [threeImageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at hi
            · have hh : ∃n:Nat, x+6=2^n*16 ∧
                (2*k-3)+14+3*n=x+8 := by
                simpa [threeImageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] using hi
              obtain ⟨n,hpow,hcost⟩:=hh
              have hp:2^n≤x+6+1:=by
                have hn:=Nat.le_mul_of_pos_right (2^n) (show 0<16 by decide)
                omega
              have hk':(x-3-3*n)/2=k := by omega
              apply lowThreeIndex x n a k (smallPowBound x 6 n hp)
              simp [lowThreeOne,ha1,hk']
    · by_cases hk0:k=0
      · simp [threeImageCriterion,ha0,ha1,hk0] at hi
      · by_cases hreg:2*k≤a
        · simp [threeImageCriterion,ha0,ha1,hk0,hreg] at hi
        · by_cases heven:a%2=0
          · simp [threeImageCriterion,ha0,ha1,hk0,hreg,heven] at hi
          · have hh:∃n:Nat,x+6=2^n*(2*(a-1)+8) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+8 := by
              simpa [threeImageCriterion,ha0,ha1,hk0,hreg,heven] using hi
            obtain ⟨n,hpow,hcost⟩:=hh
            have hpow': x+6=2^(n+1)*(a+3):=by
              have hf:2*(a-1)+8=2*(a+3):=by omega
              rw [hf] at hpow
              rw [Nat.pow_succ]
              calc
                x+6=2^n*(2*(a+3)):=hpow
                _=(2^n*2)*(a+3):=by ac_rfl
            have hbound:2^n≤x+6+1:=by
              have hn:=Nat.le_mul_of_pos_right (2^(n+1)) (show 0<a+3 by omega)
              have hn2:2^n≤2^(n+1):=by
                rw [Nat.pow_succ]
                have hn0:0<2^n:=Nat.pow_pos (by decide)
                omega
              omega
            have ha':(x+6)/(2^(n+1))-3=a:=by
              rw [hpow',Nat.mul_div_cancel_left (a+3) (Nat.pow_pos (by decide))]
              omega
            have hk':(x+1-a-3*n)/2=k:=by omega
            apply lowThreeIndex x n a k (smallPowBound x 6 n hbound)
            simp [lowThreeOne,ha',hk']

theorem lowFourComplete (a k x:Nat)
    (h:secNext (a,k)=some (x,4)) : (a,k)∈lowFourList x := by
  have hi := (fourImage_exact a k x).mp h
  by_cases ha0:a=0
  · by_cases hk0:k=0
    · simp [fourImageCriterion,ha0,hk0] at hi
    · by_cases hk1:k=1
      · unfold lowFourList
        apply List.mem_append.mpr
        right
        simpa [ha0,hk1] using (show (0,1)∈([(0,1),(x+2,1)]:List (Nat×Nat)) by simp)
      · have hh:∃n:Nat,x+4=2^n*8 ∧ (2*k+1)+8+3*n=x+8 := by
          simpa [fourImageCriterion,ha0,hk0,hk1] using hi
        obtain ⟨n,hpow,hcost⟩:=hh
        have hbound:2^n≤x+4+1:=by
          have hn:=Nat.le_mul_of_pos_right (2^n) (show 0<8 by decide)
          omega
        have hk':(x-1-3*n)/2=k:=by omega
        apply lowFourIndex x n a k (smallPowBound x 4 n hbound)
        simp [lowFourOne,ha0,hk']
  · by_cases ha1:a=1
    · simp [fourImageCriterion,ha0,ha1] at hi
    · by_cases hk0:k=0
      · simp [fourImageCriterion,ha0,ha1,hk0] at hi
      · by_cases hreg:2*k≤a
        · have hh:x=a-2*k ∧ k=1 := by
            simpa [fourImageCriterion,ha0,ha1,hk0,hreg] using hi
          have ha':a=x+2:=by omega
          have hk':k=1:=hh.2
          unfold lowFourList
          apply List.mem_append.mpr
          right
          simp [ha',hk']
        · by_cases heven:a%2=0
          · have hh:∃n:Nat,x+4=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+8 := by
              simpa [fourImageCriterion,ha0,ha1,hk0,hreg,heven] using hi
            obtain ⟨n,hpow,hcost⟩:=hh
            have hpow':x+4=2^(n+1)*(a+2):=by
              have hf:2*(a-1)+6=2*(a+2):=by omega
              rw [hf] at hpow
              rw [Nat.pow_succ]
              calc
                x+4=2^n*(2*(a+2)):=hpow
                _=(2^n*2)*(a+2):=by ac_rfl
            have hbound:2^n≤x+4+1:=by
              have hn:=Nat.le_mul_of_pos_right (2^(n+1)) (show 0<a+2 by omega)
              have hn2:2^n≤2^(n+1):=by
                rw [Nat.pow_succ]
                have hn0:0<2^n:=Nat.pow_pos (by decide)
                omega
              omega
            have ha':(x+4)/(2^(n+1))-2=a:=by
              rw [hpow',Nat.mul_div_cancel_left (a+2) (Nat.pow_pos (by decide))]
              omega
            have hk':(x+1-a-3*n)/2=k:=by omega
            apply lowFourIndex x n a k (smallPowBound x 4 n hbound)
            simp [lowFourOne,ha',hk']
          · simp [fourImageCriterion,ha0,ha1,hk0,hreg,heven] at hi

#print axioms lowFourComplete
#print axioms lowThreeComplete
end BB6.Agent11Fast
