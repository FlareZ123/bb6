import Init.Omega
namespace BB6.Agent50L1All

/-- Exact algebra connecting the rooted mass/power equations after any upper prefix. -/
theorem scaled_root_mass_power_to_dyadic
  (q r X Y P V J bp dp c : Nat)
  (hbp : bp%2=0)
  (hroot : X*(bp+12)+24*q+8=42*P)
  (hmass : bp+dp+2*r+32*q+21=56*P)
  (hpower : dp+bp/2+3=Y*(c+3))
  (hVdef : V+21=56*X)
  (hJdef : J+12*q+4=(32*q+12+2*r)*X) :
  X*Y*(c+3)+J=V*P := by
  have hM : X*bp+X*dp+2*(X*r)+32*(X*q)+21*X=56*(X*P) := by
    have hh := congrArg (fun w:Nat => X*w) hmass
    simp only [Nat.mul_add] at hh
    -- all monomials have been expanded exactly
    have hcalc : X*(2*r)=2*(X*r) := by ac_rfl
    have hcalc2 : X*(32*q)=32*(X*q) := by ac_rfl
    have hcalc3 : X*(56*P)=56*(X*P) := by ac_rfl
    omega
  have hR : X*bp+12*X+24*q+8=42*P := by
    have hh : X*(bp+12)=X*bp+12*X := by rw [Nat.mul_add]; ac_rfl
    omega
  have hPow : 2*(X*dp)+X*bp+6*X=2*(X*Y*(c+3)) := by
    have hbp2 : 2*(bp/2)=bp := by omega
    have hbx : (2*X)*(bp/2)=X*bp := by
      calc
        (2*X)*(bp/2)=X*(2*(bp/2)) := by ac_rfl
        _=X*bp := by rw [hbp2]
    have hdx : (2*X)*dp=2*(X*dp) := by ac_rfl
    have h3x : (2*X)*3=6*X := by ac_rfl
    have hrx : (2*X)*(Y*(c+3))=2*(X*Y*(c+3)) := by ac_rfl
    calc
      2*(X*dp)+X*bp+6*X = (2*X)*(dp+bp/2+3) := by
        rw [Nat.mul_add, Nat.mul_add, hdx,hbx,h3x]
      _=(2*X)*(Y*(c+3)) := by rw [hpower]
      _=2*(X*Y*(c+3)) := by ac_rfl
  have hV : V*P+21*P=56*(X*P) := by
    have hh := congrArg (fun w:Nat => w*P) hVdef
    simp only [Nat.add_mul] at hh
    have ht : (56*X)*P=56*(X*P) := by ac_rfl
    omega
  have hJ : J+12*q+4=32*(X*q)+12*X+2*(X*r) := by
    have hh:=hJdef
    simp only [Nat.add_mul] at hh
    have hq : (32*q)*X=32*(X*q) := by ac_rfl
    have hr : (2*r)*X=2*(X*r) := by ac_rfl
    omega
  omega

#print axioms scaled_root_mass_power_to_dyadic
end BB6.Agent50L1All
