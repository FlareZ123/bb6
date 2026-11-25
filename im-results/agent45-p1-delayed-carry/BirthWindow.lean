import ReverseBlockSource
namespace BB6.Agent45ReverseBlock

/-- If a central birth occurs at any of the first k decreasing-clock steps,
    its terminal endpoint lies in a single narrow static modular window. -/
theorem center_window {F z j k : Nat} (hj : j≤k) (hfit : 2^(k+2)≤F)
    (heven : (F-j)%2=0)
    (hwalk : Walk F z (List.replicate j 0) ((F-j-2)/2)) :
    F-2^(k+2)<(2^(k+1)*z)%F := by
  obtain ⟨B,hB,he⟩ := eq_of_walk hwalk
  simp only [List.length_replicate,digits_zero,Nat.add_zero] at he
  have hc := corr_bound j B
  have hpow : 2^(j+2)≤2^(k+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hjlt : j+2≤F := by have := Nat.lt_two_pow_self (n:=j+2); omega
  have hcenter : 2*((F-j-2)/2)+j+2=F := by omega
  let E := 2^(k-j)*(2*corr j B+j+2)
  have hE : 0<E := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  have hEbound : E<2^(k+2) := by
    have hlocal : 2*corr j B+j+2<2^(j+2) := by rw [show j+2=j+1+1 by omega,Nat.pow_succ]; omega
    have hm := Nat.mul_lt_mul_of_pos_left hlocal (Nat.two_pow_pos (k-j))
    rw [←Nat.pow_add,show k-j+(j+2)=k+2 by omega] at hm
    exact hm
  have hEq : 2^(k+1)*z+E=F*(2^(k-j)*(2*B+1)) := by
    have h := congrArg (fun x : Nat => 2*x+j+2) he
    have h' : 2^(j+1)*z+(2*corr j B+j+2)=F*(2*B+1) := by
      rw [Nat.pow_succ,Nat.mul_add,Nat.mul_one]
      grind
    have h'' := congrArg (fun x : Nat => 2^(k-j)*x) h'
    rw [Nat.mul_add,←Nat.mul_assoc,←Nat.pow_add,show k-j+(j+1)=k+1 by omega] at h''
    dsimp [E]
    grind
  have hf : 0<F := by have := Nat.two_pow_pos (k+2); omega
  have hrem := congrArg (fun x : Nat => x%F) hEq
  rw [Nat.add_mod,Nat.mod_eq_of_lt (show E<F by omega)] at hrem
  simp only [Nat.mul_mod_right] at hrem
  have hr := Nat.mod_lt (2^(k+1)*z) hf
  have hsum : (2^(k+1)*z)%F+E<2*F := by omega
  by_cases hle : (2^(k+1)*z)%F+E<F
  · rw [Nat.mod_eq_of_lt hle] at hrem; omega
  · rw [Nat.mod_eq_sub_mod (by omega : F≤(2^(k+1)*z)%F+E),Nat.mod_eq_of_lt (by omega)] at hrem
    omega

/-- Same necessary window expressed using the original interior walk. -/
theorem source_center_window {F z q k : Nat} (hq : q≤F) (hk : F-q≤k)
    (hfit : 2^(k+2)≤F) (heven : q%2=0)
    (hw : SourceWalk q ((q-2)/2) (F-q) z) :
    F-2^(k+2)<(2^(k+1)*z)%F := by
  have h := source_to_reverse hw
  rw [show q+(F-q)=F by omega] at h
  exact center_window hk hfit (by simpa [show F-(F-q)=q by omega] using heven)
    (by simpa [show F-(F-q)=q by omega] using h)

#print axioms center_window
#print axioms source_center_window
end BB6.Agent45ReverseBlock
