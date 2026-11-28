import DensityOneCore
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

def scaledA (z:ArithmeticCert) (d A:Int):Prop :=
 (2:Int)^z.shift * A = (z.u:Int)*d+z.v

def sumAt (z:ArithmeticCert) (d A D:Int):Prop :=
 A+D=2*d+1-(z.sumDecrease:Int)

private theorem highScaled (P U V d A D A' c:Int)
 (hA:P*A=U*d+V)
 (hS:A+D=2*d+1-c)
 (hH:2*A'=2*A+D+1) :
 (2*P)*A'=(U+2*P)*d+(V+P*(2-c)) := by
 have hSP := congrArg (fun x:Int =>P*x) hS
 have hHP := congrArg (fun x:Int =>P*x) hH
 have h1 (x:Int) : P*(2*x) = 2*(P*x) := by ac_rfl
 have h2 (x:Int) : (2*P)*x = 2*(P*x) := by ac_rfl
 simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.add_mul, h1, h2] at hSP hHP ⊢
 omega

private theorem farScaled (P U V d A A' : Int)
 (hA : P*A=U*d+V)
 (hF : 4*A'=A-6) :
 (4*P)*A'=U*d+(V-6*P) := by
 have hFP := congrArg (fun x:Int=>P*x) hF
 have h1 (x:Int) : P*(4*x) = 4*(P*x) := by ac_rfl
 have h2 (x:Int) : (4*P)*x = 4*(P*x) := by ac_rfl
 simp only [Int.mul_sub, h1, h2] at hFP ⊢
 omega

theorem high_preserves_scaled (z:ArithmeticCert) (d A D A':Int)
 (hA: scaledA z d A)
 (hS: sumAt z d A D)
 (hH:2*A'=2*A+D+1) :
 scaledA (advance z .high) d A' := by
 rcases z with ⟨u,v,s,c⟩
 dsimp [scaledA, sumAt] at hA hS
 have hh := highScaled ((2:Int)^s) (u:Int) v d A D A' (c:Int) hA hS hH
 simpa [scaledA,advance,Int.natCast_add,Int.natCast_pow,Int.pow_succ,
       Int.mul_comm,Int.mul_left_comm,Int.mul_assoc] using hh

theorem far_preserves_scaled (z:ArithmeticCert) (d A A':Int)
 (hA:scaledA z d A)
 (hF:4*A'=A-6) :
 scaledA (advance z .far) d A' := by
 rcases z with ⟨u,v,s,c⟩
 dsimp [scaledA] at hA
 have hf := farScaled ((2:Int)^s) (u:Int) v d A A' hA hF
 have hpow : (2:Int)^(s+2) = 4*(2:Int)^s := by
   rw [Int.pow_add]
   simp [Int.mul_comm]
 simpa [scaledA,advance,Int.natCast_pow,hpow,
       Int.mul_comm,Int.mul_left_comm,Int.mul_assoc] using hf

theorem high_preserves_sum (z:ArithmeticCert)
 (d A D A' D':Int)
 (hS:sumAt z d A D)
 (hA:2*A'=2*A+D+1)
 (hD:2*D'=D-3) :
 sumAt (advance z .high) d A' D' := by
 have hChange := high_inverse_sum hA hD
 rcases z with ⟨u,v,s,c⟩
 dsimp [sumAt, advance] at hS ⊢
 omega

theorem far_preserves_sum (z:ArithmeticCert)
 (d A D A' D':Int)
 (hS:sumAt z d A D)
 (hA:4*A'=A-6)
 (hD:D'=D+3*A') :
 sumAt (advance z .far) d A' D' := by
 have hChange := far_inverse_sum hA hD
 rcases z with ⟨u,v,s,c⟩
 dsimp [sumAt, advance] at hS ⊢
 omega

inductive FormalInversePath (d:Int) : List InverseLetter → Int → Int → Prop where
 | nil : FormalInversePath d [] (d+1) d
 | stepH {w A D A' D'}
     (hp:FormalInversePath d w A D)
     (ha:2*A'=2*A+D+1) (hd:2*D'=D-3) :
     FormalInversePath d (.high::w) A' D'
 | stepF {w A D A' D'}
     (hp:FormalInversePath d w A D)
     (ha:4*A'=A-6) (hd:D'=D+3*A') :
     FormalInversePath d (.far::w) A' D'

theorem formal_inverse_path_certificate
 {d:Int} {w:List InverseLetter} {A D:Int}
 (hp:FormalInversePath d w A D) :
 scaledA (compile w) d A ∧ sumAt (compile w) d A D := by
 induction hp with
 | nil =>
     constructor <;> simp [compile, scaledA, sumAt, initial] <;> omega
 | stepH hp ha hd ih =>
     constructor
     · exact high_preserves_scaled (compile _) _ _ _ _ ih.1 ih.2 ha
     · exact high_preserves_sum (compile _) _ _ _ _ _ ih.2 ha hd
 | stepF hp ha hd ih =>
     constructor
     · exact far_preserves_scaled (compile _) _ _ _ ih.1 ha
     · exact far_preserves_sum (compile _) _ _ _ _ _ ih.2 ha hd

/-- Every fully integral inverse high/far path carries an odd-numerator
    necessary dyadic congruence on the terminal parameter. -/
theorem formal_inverse_congruence
 {d:Int} {w:List InverseLetter} {A D:Int}
 (hp:FormalInversePath d w A D) :
 (2:Int)^(compile w).shift * A = ((compile w).u:Int)*d+(compile w).v ∧
 (compile w).u % 2 = 1 := by
 exact ⟨(formal_inverse_path_certificate hp).1, compiled_numerator_odd w⟩

#print axioms high_preserves_scaled
#print axioms far_preserves_scaled
#print axioms formal_inverse_congruence
end BB6.Agent31F321Density
