import Std
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 8000
set_option maxHeartbeats 0
namespace GapNumber
/-- An exact finite kernel-evaluated residue certificate: below n=25,
    no integer B can meet the source second-tier model and weak margin.
    The proof first bounds both n and j, then checks a 25-by-16 finite
    table with ordinary kernel reduction (decide). -/
theorem small_n_no_model (n j B:Nat) (hn:13≤n) (hmax:n<25)
  (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
  (hweak:2*(2^j*(2*n+3))+2*n+10≤2^(n-4)) : False := by
  have hbound:2^(n-4)≤2^20 :=
    Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
  have hjlt:j<16 := by
    by_cases hj:j<16
    · exact hj
    · have hj16:16≤j:=by omega
      have hjp:65536≤2^j:=by
        have h:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hj16
        simpa only [show (2:Nat)^16=65536 by decide] using h
      have hfactor:29≤2*n+3:=by omega
      have hmul:=Nat.mul_le_mul hjp hfactor
      omega
  have htest : ∀ (x:Fin 25) (y:Fin 16),
      13≤x.val →
      2*(2^y.val*(2*x.val+3))+2*x.val+10≤2^(x.val-4) →
      (16*2^(x.val-4)+128*(2^y.val*(2*x.val+3))+169*x.val)%81≠3 := by
    decide
  have hbad:=htest ⟨n,hmax⟩ ⟨j,hjlt⟩ hn hweak
  have heq:(16*2^(n-4)+128*(2^j*(2*n+3))+169*n)%81=3:=by
    rw [←hmodel]
    omega
  exact hbad heq
#print axioms small_n_no_model
end GapNumber
