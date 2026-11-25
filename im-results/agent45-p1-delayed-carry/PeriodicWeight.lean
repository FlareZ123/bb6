import TraceWeight
namespace BB6.Agent45WeightedDigitGap

/-- Concatenate a low s-bit word V and a high p-bit word U. -/
theorem weight_concat (s p V U : Nat) (hV : V<2^s) (hU : U<2^p) :
    digitWeight (s+p) (V+2^s*U)=digitWeight s V+2^s*(digitWeight p U+s*U) := by
  induction p generalizing U with
  | zero =>
    have h : U=0 := by simpa using hU
    simp [h,digitWeight,BB6.Agent45ReverseBlock.corr]
  | succ p ih =>
    let R := U%2^p
    let x := U/2^p
    have hp := Nat.two_pow_pos p
    have hR : R<2^p := Nat.mod_lt _ hp
    have hx : x≤1 := by rw [Nat.pow_succ] at hU; dsimp [x]; exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).2 (by omega))
    have hUeq : U=R+2^p*x := (Nat.mod_add_div _ _).symm
    have hpw : 2^(s+p)=2^s*2^p := Nat.pow_add _ _ _
    have hbase : V+2^s*R<2^(s+p) := by
      rw [hpw]
      have hh := Nat.mul_le_mul_left (2^s) (show R+1≤2^p by omega)
      rw [Nat.mul_add,Nat.mul_one] at hh
      omega
    have hmain : V+2^s*U=(V+2^s*R)+2^(s+p)*x := by rw [hUeq,hpw]; grind
    rw [show s+(p+1)=s+p+1 by omega,hmain,weight_extend _ _ _ hbase hx,ih R hR]
    have hh := weight_extend p R x hR hx
    rw [←hUeq] at hh
    rw [hh,hUeq,hpw]
    grind

/-- Sum and first moment of a finite geometric progression. -/
def geom (P : Nat) : Nat → Nat
  | 0 => 0
  | t+1 => 1+P*geom P t

def moment (P : Nat) : Nat → Nat
  | 0 => 0
  | t+1 => P*(moment P t+geom P t)

theorem geom_eq (P t : Nat) : ((P:Int)-1)*(geom P t:Int)=(P:Int)^t-1 := by
  induction t with
  | zero => simp [geom]
  | succ t ih => simp only [geom,Int.natCast_add,Int.natCast_mul,Int.natCast_one,Int.pow_succ]; grind

theorem moment_eq (P t : Nat) : ((P:Int)-1)^2*(moment P t:Int)=((t:Int)*((P:Int)-1)-(P:Int))*(P:Int)^t+(P:Int) := by
  induction t with
  | zero => simp [moment] <;> omega
  | succ t ih =>
    have hg := geom_eq P t
    simp only [moment,Int.natCast_mul,Int.natCast_add,Int.natCast_succ,Int.pow_succ] at *
    grind

theorem repeat_bound (P U t : Nat) (hU : U<P) : U*geom P t<P^t := by
  induction t with
  | zero => simp [geom]
  | succ t ih =>
    have hh := Nat.mul_le_mul_left P (show U*geom P t+1≤P^t by omega)
    rw [Nat.mul_add,Nat.mul_one] at hh
    simp only [geom,Nat.pow_succ]
    have he : U*(1+P*geom P t)=U+P*(U*geom P t) := by rw [Nat.mul_add,Nat.mul_one]; ac_rfl
    rw [he,Nat.mul_comm (P^t) P]
    omega

theorem repeat_weight (p U t : Nat) (hU : U<2^p) :
    digitWeight (p*t) (U*geom (2^p) t)=digitWeight p U*geom (2^p) t+p*U*moment (2^p) t := by
  induction t with
  | zero => simp [geom,moment,digitWeight,BB6.Agent45ReverseBlock.corr]
  | succ t ih =>
    have hp : (2^p)^t=2^(p*t) := by rw [Nat.pow_mul]
    have hb : U*geom (2^p) t<2^(p*t) := by rw [←hp]; exact repeat_bound _ _ _ hU
    have he : U*geom (2^p) (t+1)=U+2^p*(U*geom (2^p) t) := by rw [geom,Nat.mul_add,Nat.mul_one]; ac_rfl
    rw [Nat.mul_succ,he,show p*t+p=p+p*t by omega,weight_concat p (p*t) U _ hU hb,ih,geom,moment]
    grind

/-- The signed numerator of the 2-adic eventually periodic word equation. -/
def periodicNumerator (A s p V U : Nat) : Int :=
  let P : Int := 2^p
  let D := P-1
  ((digitWeight s V:Int)-(A:Int)*V-1)*D^2 - (2:Int)^s*((digitWeight p U:Int)+((s:Int)-A)*U)*D + (2:Int)^s*(p:Int)*U*P

/-- A finite repeated block satisfies an exact integer identity, with error
    a multiple of 2^(s+p*t). -/
theorem periodic_identity (A s p V U t : Nat) (hV : V<2^s) (hU : U<2^p) :
    let B := V+2^s*(U*geom (2^p) t)
    let F : Int := (digitWeight (s+p*t) B:Int)-(A:Int)*B-1
    let P : Int := 2^p
    let D := P-1
    D^2*F=periodicNumerator A s p V U+2^(s+p*t)*
      (((digitWeight p U:Int)+((s:Int)-A)*U)*D+(p:Int)*U*((t:Int)*D-P)) := by
  have hp : (2^p)^t=2^(p*t) := by rw [Nat.pow_mul]
  have hb : U*geom (2^p) t<2^(p*t) := by rw [←hp]; exact repeat_bound _ _ _ hU
  dsimp only [periodicNumerator]
  rw [weight_concat s (p*t) V _ hV hb,repeat_weight p U t hU]
  have hg := geom_eq (2^p) t
  have hm := moment_eq (2^p) t
  simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.natCast_one] at *
  rw [Int.pow_add,Int.pow_mul]
  grind

/-- The original Trace congruence requires its periodic numerator to be
    divisible by the complete bit length. -/
theorem trace_periodic_dvd (n A s p V U t a : Nat) (hn : 0<n) (heven : n%2=0)
    (hA : BB6.Agent45.DelayedCarry.total n=n+3+A)
    (hV : V<2^s) (hU : U<2^p)
    (h : BB6.Agent45.DelayedCarry.Trace n (s+p*t) (V+2^s*(U*geom (2^p) t)) a) :
    ((2:Int)^(s+p*t)) ∣ periodicNumerator A s p V U := by
  let B := V+2^s*(U*geom (2^p) t)
  let m := s+p*t
  let T := BB6.Agent45.DelayedCarry.total n
  have ht := trace_identity h hn heven
  change E n m B=2^m*a+(T*B)%2^m+1 at ht
  have hd := Nat.div_add_mod (T*B) (2^m)
  have hT : T=n+3+A := hA
  have hf : (digitWeight m B:Int)-(A:Int)*B-1=2^m*((a:Int)-(T*B/2^m:Nat)) := by
    unfold E at ht
    have ht' := congrArg (fun u : Nat => (u:Int)) ht
    have hd' := congrArg (fun u : Nat => (u:Int)) hd
    have hT' := congrArg (fun u : Nat => (u:Int)) hT
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.natCast_one,Int.natCast_one] at ht' hd' hT' ⊢
    grind
  have hi := periodic_identity A s p V U t hV hU
  change ((2:Int)^p-1)^2*((digitWeight m B:Int)-(A:Int)*B-1)=_ at hi
  rw [hf] at hi
  refine ⟨((2:Int)^p-1)^2*((a:Int)-(T*B/2^m:Nat))-(((digitWeight p U:Int)+((s:Int)-A)*U)*((2:Int)^p-1)+(p:Int)*U*((t:Int)*((2:Int)^p-1)-(2:Int)^p)),?_⟩
  change periodicNumerator A s p V U=(2:Int)^m*_ 
  grind

#print axioms weight_concat
#print axioms periodic_identity
#print axioms trace_periodic_dvd
end BB6.Agent45WeightedDigitGap
