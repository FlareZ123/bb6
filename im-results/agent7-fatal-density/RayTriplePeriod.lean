import RayResidues
set_option maxHeartbeats 0
namespace CascadeRayPeriod

private theorem pow_shift_four (j:Nat):
    (2:Int)^(j+4)=16*(2:Int)^j:=by
  have hp:(2:Nat)^(j+4)=16*2^j:=by
    rw[Nat.pow_add]
    have h:(2:Nat)^4=16:=by decide
    rw[h]
    omega
  exact_mod_cast hp

private theorem pow_shift_six (j:Nat):
    (2:Int)^(j+6)=64*(2:Int)^j:=by
  have hp:(2:Nat)^(j+6)=64*2^j:=by
    rw[Nat.pow_add]
    have h:(2:Nat)^6=64:=by decide
    rw[h]
    omega
  exact_mod_cast hp

theorem signedZ_step_six (n j:Nat):
    signedZ n (j+6)=signedZ n j-
      126*(2:Int)^j*(2*n+3):=by
  have he:j+6=(j+4)+2:=by omega
  calc
    signedZ n (j+6)=signedZ n (j+4)-
      6*(2:Int)^(j+4)*(2*n+3):=by rw[he,signedZ_step_two]
    _ = (signedZ n j-30*(2:Int)^j*(2*n+3))-
      6*(16*(2:Int)^j)*(2*n+3):=by
        rw[signedZ_step_four,pow_shift_four]
    _ = signedZ n j-126*(2:Int)^j*(2*n+3):=by
       have hx:6*(16*(2:Int)^j)*(2*(n:Int)+3)=96*(2:Int)^j*(2*n+3):=by
         simp only [← Int.mul_assoc, show (6:Int)*16=96 by decide]
       rw[hx]
       have hh : 30*(2:Int)^j*(2*n+3)+96*(2:Int)^j*(2*n+3)=126*(2:Int)^j*(2*n+3):=by
         simp only [← Int.add_mul, show (30:Int)+96=126 by decide]
       omega

theorem signedZ_step_twelve (n j:Nat):
    signedZ n (j+12)=signedZ n j-
      8190*(2:Int)^j*(2*n+3):=by
  have he:j+12=(j+6)+6:=by omega
  calc
    signedZ n (j+12)=signedZ n (j+6)-
      126*(2:Int)^(j+6)*(2*n+3):=by rw[he,signedZ_step_six]
    _=(signedZ n j-126*(2:Int)^j*(2*n+3))-
      126*(64*(2:Int)^j)*(2*n+3):=by
        rw[signedZ_step_six,pow_shift_six]
    _=signedZ n j-8190*(2:Int)^j*(2*n+3):=by
       have hx:126*(64*(2:Int)^j)*(2*(n:Int)+3)=8064*(2:Int)^j*(2*n+3):=by
         simp only [← Int.mul_assoc, show (126:Int)*64=8064 by decide]
       rw[hx]
       have hh : 126*(2:Int)^j*(2*n+3)+8064*(2:Int)^j*(2*n+3)=8190*(2:Int)^j*(2*n+3):=by
         simp only [← Int.add_mul, show (126:Int)+8064=8190 by decide]
       omega

private theorem elementary_mod27 (z d:Int) (hz:z%9=0)
    (hd:d%3=1∨d%3=2):
    (z%27=0∧(z-126*d)%27=9∧(z-8190*d)%27=18) ∨
    (z%27=0∧(z-126*d)%27=18∧(z-8190*d)%27=9) ∨
    (z%27=9∧(z-126*d)%27=0∧(z-8190*d)%27=18) ∨
    (z%27=9∧(z-126*d)%27=18∧(z-8190*d)%27=0) ∨
    (z%27=18∧(z-126*d)%27=0∧(z-8190*d)%27=9) ∨
    (z%27=18∧(z-126*d)%27=9∧(z-8190*d)%27=0):=by
  rcases hd with hd|hd <;> omega

/-- Three successive six-level potential odd-fork numerators form residues
    0,9,18 modulo 27, conditional on the first divisible by nine. -/
theorem signed_ray_three_packet_mod27 (n j:Nat)
    (hn:n%6=4∨n%6=5) (h9:signedZ n j%9=0):
    (signedZ n j%27=0∧signedZ n (j+6)%27=9∧signedZ n (j+12)%27=18) ∨
    (signedZ n j%27=0∧signedZ n (j+6)%27=18∧signedZ n (j+12)%27=9) ∨
    (signedZ n j%27=9∧signedZ n (j+6)%27=0∧signedZ n (j+12)%27=18) ∨
    (signedZ n j%27=9∧signedZ n (j+6)%27=18∧signedZ n (j+12)%27=0) ∨
    (signedZ n j%27=18∧signedZ n (j+6)%27=0∧signedZ n (j+12)%27=9) ∨
    (signedZ n j%27=18∧signedZ n (j+6)%27=9∧signedZ n (j+12)%27=0):=by
  have hd:=step_d_nonzero n j hn
  have hp:=elementary_mod27 (signedZ n j)
    ((2:Int)^j*(2*(n:Int)+3)) h9 hd
  rw[signedZ_step_six,signedZ_step_twelve]
  simpa only [Int.mul_assoc] using hp

#print axioms signedZ_step_six
#print axioms signedZ_step_twelve
#print axioms signed_ray_three_packet_mod27
end CascadeRayPeriod
