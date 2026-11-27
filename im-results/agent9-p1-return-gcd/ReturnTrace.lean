import LagCore
import ReturnGeneral

namespace BB6.Agent9ReturnGCD
open BB6.Agent45.DelayedCarry

/-- Chronological selected bit, with bit zero the compulsory first step. -/
def bit (B j : Nat) : Int := if B.testBit j then 1 else 0

theorem bit_binary (B j : Nat) : bit B j=0 ∨ bit B j=1 := by
  unfold bit; split <;> simp

theorem bit_append_low (B i x j : Nat) (hB : B<2^i) (hj : j<i) :
    bit (B+2^i*x) j=bit B j := by
  have h := Nat.testBit_mod_two_pow (B+2^i*x) i j
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hB] at h
  simp [hj] at h
  simp only [bit,h]

theorem bit_append_top (B i x : Nat) (hB : B<2^i) (hx : x≤1) :
    bit (B+2^i*x) i=(x:Int) := by
  have h := Nat.testBit_div_two_pow (n:=i) (B+2^i*x) 0
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos i),Nat.div_eq_of_lt hB,Nat.zero_add,Nat.zero_add] at h
  unfold bit
  rw [←h,Nat.testBit_zero]
  rcases (show x=0∨x=1 by omega) with rfl|rfl <;> decide

theorem total_even_of_pos (n : Nat) (hn : 0<n) : total n%2=0 := by
  unfold total
  have hp : (2:Nat)^n%2=0 := Nat.dvd_iff_mod_eq_zero.mp
    (by simpa using Nat.pow_dvd_pow 2 (show 1≤n by omega))
  rw [Nat.mul_mod,hp] <;> simp

/-- The full micro-coordinate history of an original delayed-carry Trace.
    No pre-delay or guard restriction is used. -/
structure TracePath (n m B a : Nat) (v w : Nat→Int) : Prop where
  rootV : v 0=1
  rootW : w 0=(total n:Int)-n-2
  mass : ∀ j≤m, v j+w j=(total n:Int)-n-j-1
  bounds : ∀ j≤m, 1≤v j ∧ v j≤(total n:Int) ∧ 1≤w j ∧ w j≤(total n:Int)
  stepV : ∀ j<m, 2*v (j+1)=v j+((total n:Int)-n-j-3)*bit B j
  stepW : ∀ j<m, 2*w (j+1)=w j+((total n:Int)-n-j-3)*(1-bit B j)
  endpoint : v m+(a:Int)=(quotient n m B:Int)

/-- Exact bridge from the original source Trace, retaining its actual
    selected word and every positive integral coordinate. -/
theorem trace_path {n m B a : Nat} (hn : 14≤n) (heven : n%2=0)
    (ht : Trace n m B a) : ∃ v w, TracePath n m B a v w := by
  have hT := total_even_of_pos n (by omega)
  have hlarge : n+4≤total n := by
    have h := Nat.lt_two_pow_self (n:=n)
    unfold total
    omega
  induction ht with
  | first =>
    let p : Int := (quotient n 1 1:Int)-(((n+2)/2:Nat):Int)
    have hquot : quotient n 1 1=total n/2 := by simp [quotient]
    have hp : 2*p=(total n:Int)-n-2 := by
      dsimp [p]
      rw [hquot]
      omega
    let v : Nat→Int := fun j => if j=0 then 1 else p
    let w : Nat→Int := fun j => if j=0 then (total n:Int)-n-2 else p
    refine ⟨v,w,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [v]
    · simp [w]
    · intro j hj
      rcases (show j=0∨j=1 by omega) with rfl|rfl <;> simp [v,w] <;> omega
    · intro j hj
      rcases (show j=0∨j=1 by omega) with rfl|rfl <;> simp [v,w] <;> omega
    · intro j hj
      have hj0 : j=0 := by omega
      subst j
      simp [v,bit] <;> omega
    · intro j hj
      have hj0 : j=0 := by omega
      subst j
      simp [w,bit] <;> omega
    · simp [v,p]
  | step i B a x c h hx he ih =>
    obtain ⟨v,w,H⟩ := ih
    have hword := (trace_bounds n i B a h).2.1
    let z : Int := (quotient n (i+1) (B+2^i*x):Int)-(c:Int)
    let t : Int := (total n:Int)-n-(i+1:Nat)-1-z
    have hq := quotient_step n i B x
    have hpar : (quotient n i B+total n*x)%2=target n i B := by
      rw [target_eq,Nat.add_mod,Nat.mul_mod,hT]; simp
    have hqeq : 2*quotient n (i+1) (B+2^i*x)+target n i B=quotient n i B+total n*x := by omega
    have hqeqI := congrArg (fun k : Nat => (k:Int)) hqeq
    have heI := congrArg (fun k : Nat => (k:Int)) he
    push_cast at hqeqI heI
    have hV : 2*z=v i+((total n:Int)-n-i-3)*(x:Int) := by
      have hEnd := H.endpoint
      dsimp [z]
      rcases (show x=0∨x=1 by omega) with h0|h1 <;> subst x <;> simp at hqeqI heI ⊢ <;> omega
    have hmass := H.mass i (by omega)
    have hbound := H.bounds i (by omega)
    have hW : 2*t=w i+((total n:Int)-n-i-3)*(1-(x:Int)) := by
      dsimp [t]
      rcases (show x=0∨x=1 by omega) with h0|h1
      · rw [h0] at hV ⊢; simp at hV ⊢; omega
      · rw [h1] at hV ⊢; simp at hV ⊢; omega
    have hzpos : 1≤z := by
      rcases (show x=0∨x=1 by omega) with hb|hb <;> rw [hb] at hV <;> simp at hV <;> omega
    have htpos : 1≤t := by
      rcases (show x=0∨x=1 by omega) with hb|hb <;> rw [hb] at hW <;> simp at hW <;> omega
    let v' : Nat→Int := fun j => if j≤i then v j else z
    let w' : Nat→Int := fun j => if j≤i then w j else t
    refine ⟨v',w',?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [v'] using H.rootV
    · simpa [w'] using H.rootW
    · intro j hj
      by_cases hji : j≤i
      · simpa [v',w',hji] using H.mass j hji
      · have hji' : j=i+1 := by omega
        subst j
        simp [v',w',t]
        omega
    · intro j hj
      by_cases hji : j≤i
      · simpa [v',w',hji] using H.bounds j hji
      · have hji' : j=i+1 := by omega
        subst j
        simp [v',w']
        have hmass' : z+t=(total n:Int)-n-(i+1:Nat)-1 := by dsimp [t]; omega
        omega
    · intro j hj
      by_cases hji : j<i
      · have h1 : j≤i := by omega
        have h2 : j+1≤i := by omega
        simpa [v',h1,h2,bit_append_low B i x j hword hji] using H.stepV j hji
      · have heq : j=i := by omega
        subst j
        simpa [v',show ¬ i+1≤i by omega,bit_append_top B i x hword hx] using hV
    · intro j hj
      by_cases hji : j<i
      · have h1 : j≤i := by omega
        have h2 : j+1≤i := by omega
        simpa [w',h1,h2,bit_append_low B i x j hword hji] using H.stepW j hji
      · have heq : j=i := by omega
        subst j
        simpa [w',show ¬ i+1≤i by omega,bit_append_top B i x hword hx] using hW
    · simp [v',show ¬ i+1≤i by omega,z]

#print axioms trace_path

end BB6.Agent9ReturnGCD
