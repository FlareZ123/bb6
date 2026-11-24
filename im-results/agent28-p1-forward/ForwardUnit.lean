import PosEvenForm
import ReverseUnitMap
namespace BB6.Agent28Forward
open BB6.Agent1 BB6P1Unit

def coord (a d : Nat) : Nat × Nat := (a/2+(d-1)/2+4,(d-1)/2)

def coordPair (p : Nat × Nat) : Nat × Nat := coord p.1 p.2

theorem run_cons (q v t : Nat) : run q v (1+t) = run (q+1) (unit q v) t := by
  rw [run_add]
  rfl

theorem unit_low (q v : Nat) (h : 2*v<q+1) : unit q v=2*v := by
  exact Nat.mod_eq_of_lt h

theorem unit_high (q v : Nat) (h : v<q) (hh : q+1≤2*v) : unit q v=2*v-(q+1) := by
  unfold unit
  rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega : 2*v-(q+1)<q+1)]

def firstWrap (q v t : Nat) : Prop :=
  0<t ∧ (∀ j, j+1<t → bit (q+j) (run q v j)=0) ∧
    bit (q+(t-1)) (run q v (t-1))=1

/-- The full odd G map, including its zero-left middle exit, is a first wrap
    in the moving-modulus doubling map. q=k+v+2 is the input mass index. -/
theorem g_first_wrap (k v : Nat) (hv : 2≤v) :
    ∃ t, firstWrap (k+v+2) v t ∧
      coordPair (G k (2*v-3))=(k+v+2+t,run (k+v+2) v t) := by
  induction k using Nat.strongRecOn generalizing v with
  | ind k ih =>
    let q := k+v+2
    by_cases hlow : 2*v-3<2*k
    · have hsmall : 2*v<q := by dsimp [q]; omega
      have hdec : k-(v-1)<k := by omega
      have harg : (2*v-3)/2+1=v-1 := by omega
      have hq : k-(v-1)+2*v+2=q+1 := by dsimp [q]; omega
      obtain ⟨t, hw, hc⟩ := ih (k-(v-1)) hdec (2*v) (by omega)
      rw [hq] at hw hc
      have hu : unit q v=2*v := unit_low q v (by omega)
      refine ⟨1+t, ⟨by omega, ?_, ?_⟩, ?_⟩
      · intro j hj
        cases j with
        | zero =>
          change bit q v=0
          simp [bit, show ¬q+1≤2*v by omega]
        | succ j =>
          have he : run q v (j+1)=run (q+1) (2*v) j := by
            rw [Nat.add_comm j 1,run_cons,hu]
          rw [he, show q+(j+1)=q+1+j by omega]
          exact hw.2.1 j (by omega)
      · have ht : 1≤t := by exact hw.1
        have he : 1+t-1=1+(t-1) := by omega
        rw [he,run_cons,hu, show q+(1+(t-1))=q+1+(t-1) by omega]
        exact hw.2.2
      · rw [G]
        simp only [hlow,dite_true,harg]
        have he : 2*(2*v-3)+3=2*(2*v)-3 := by omega
        rw [he, hc]
        change (q+1+t,run (q+1) (2*v) t)=(q+(1+t),run q v (1+t))
        rw [run_cons,hu]
        congr 1 <;> omega
    · by_cases hmid : 2*v-3≤2*k+1
      · have hq : 2*v=q := by dsimp [q]; omega
        have hu : unit q v=q := by rw [unit_low q v (by omega),hq]
        have hu2 : unit (q+1) q=q-2 := by rw [unit_high (q+1) q (by omega) (by dsimp [q]; omega)]; omega
        have hr : run q v 2=q-2 := by change unit (q+1) (unit q v)=q-2; rw [hu,hu2]
        refine ⟨2,⟨by decide,?_,?_⟩,?_⟩
        · intro j hj
          have : j=0 := by omega
          subst j
          change bit q v=0
          simp [bit,show ¬q+1≤2*v by omega]
        · change bit (q+1) (unit q v)=1
          rw [hu]
          simp [bit,show q+1+1≤2*q by dsimp [q]; omega]
        · rw [G]
          simp only [hlow,dite_false,hmid,ite_true,coordPair,coord]
          change (0/2+(2*(2*v-3)+3-1)/2+4,(2*(2*v-3)+3-1)/2)=(q+2,run q v 2)
          rw [hr]
          congr 1 <;> omega
      · have hhigh : q+1≤2*v := by dsimp [q]; omega
        have hu : unit q v=2*v-(q+1) := unit_high q v (by dsimp [q]; omega) hhigh
        refine ⟨1,⟨by decide,?_,?_⟩,?_⟩
        · intro j hj; omega
        · change bit q v=1
          simp [bit,hhigh]
        · rw [G]
          simp only [hlow,dite_false,hmid,ite_false,coordPair,coord]
          change ((4*k+4)/2+(2*v-3-(2*k+2)-1)/2+4,(2*v-3-(2*k+2)-1)/2)=(q+1,unit q v)
          rw [hu]
          dsimp [q]
          congr 1 <;> omega

#print axioms g_first_wrap
end BB6.Agent28Forward
