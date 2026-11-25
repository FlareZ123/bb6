import PeriodicWeight
namespace BB6.Agent45WeightedDigitGap

open BB6.Agent45ReverseBlock (corr)

theorem weight_zero (s : Nat) : digitWeight s 0=0 := by simp [digitWeight]

theorem no_positive_padded (A s V : Nat) (hV : V<2^s) :
    digitWeight s V≠A*V+1 := by
  by_cases hz : V=0
  · simp [hz,digitWeight]
  · have hlo := Nat.log2_self_le hz
    have hhi := Nat.lt_log2_self (n:=V)
    have hks := (Nat.log2_lt hz).2 hV
    have hp := weight_pad (V.log2+1) (s-(V.log2+1)) V hhi
    rw [show V.log2+1+(s-(V.log2+1))=s by omega] at hp
    rw [hp]
    exact no_positive_solution A V.log2 V hlo hhi

theorem no_negative_padded (A s V : Nat) (hV : V<2^s) :
    digitWeight s V≠A*V+A+1 := by
  by_cases hz : V=0
  · simp [hz,digitWeight]
  · have hlo := Nat.log2_self_le hz
    have hhi := Nat.lt_log2_self (n:=V)
    have hks := (Nat.log2_lt hz).2 hV
    have hp := weight_pad (V.log2+1) (s-(V.log2+1)) V hhi
    rw [show V.log2+1+(s-(V.log2+1))=s by omega] at hp
    rw [hp]
    exact no_negative_solution A V.log2 V hlo hhi

theorem weight_complement (s V : Nat) (hV : V<2^s) :
    digitWeight s V+digitWeight s (2^s-1-V)=digitWeight s (2^s-1) := by
  induction s generalizing V with
  | zero => have h : V=0 := by simpa using hV
            simp [h,digitWeight]
  | succ s ih =>
    have hp := Nat.two_pow_pos s
    have hall : 2^(s+1)-1=(2^s-1)+2^s*1 := by rw [Nat.pow_succ]; omega
    have hw := weight_extend s (2^s-1) 1 (by omega) (by decide)
    rw [←hall] at hw
    by_cases hlo : V<2^s
    · have hcomp : 2^(s+1)-1-V=(2^s-1-V)+2^s*1 := by rw [Nat.pow_succ]; omega
      have hv := weight_extend s V 0 hlo (by decide)
      simp only [Nat.mul_zero,Nat.add_zero] at hv
      rw [hv,hcomp,weight_extend s (2^s-1-V) 1 (by omega) (by decide),hw]
      have hh := ih V hlo
      omega
    · let R := V-2^s
      have hR : R<2^s := by dsimp [R]; rw [Nat.pow_succ] at hV; omega
      have hV' : V=R+2^s*1 := by dsimp [R]; omega
      have hcomp : 2^(s+1)-1-V=2^s-1-R := by dsimp [R]; rw [Nat.pow_succ]; omega
      rw [hcomp,hV',weight_extend s R 1 hR (by decide),hw]
      have h := weight_extend s (2^s-1-R) 0 (by omega) (by decide)
      simp only [Nat.mul_zero,Nat.add_zero] at h
      rw [h]
      have hh := ih R hR
      omega

theorem weight_ones (s : Nat) : (digitWeight s (2^s-1):Int)=((s:Int)-2)*2^s+2 := by
  induction s with
  | zero => decide
  | succ s ih =>
    have hp := Nat.two_pow_pos s
    have he : 2^(s+1)-1=(2^s-1)+2^s*1 := by rw [Nat.pow_succ]; omega
    rw [he,weight_extend s (2^s-1) 1 (by omega) (by decide)]
    simp only [Nat.mul_one,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.natCast_succ,Int.pow_succ]
    rw [ih]
    grind

theorem zero_block_nonzero (A s p V : Nat) (hp : 0<p) (hV : V<2^s) :
    periodicNumerator A s p V 0≠0 := by
  intro h
  have hd : (2:Int)^p-1≠0 := by
    have h := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤p by omega)
    have h' := congrArg (fun x : Nat => (x:Int)) (Nat.pow_one 2)
    have hh : (2:Int)≤2^p := by exact_mod_cast h
    omega
  simp [periodicNumerator,digitWeight] at h
  have hh : (digitWeight s V:Int)-(A:Int)*V-1=0 := by
    change ((digitWeight s V:Int)-(A:Int)*V-1)*((2:Int)^p-1)^2=0 at h
    rcases Int.mul_eq_zero.mp h with hh|hh
    · exact hh
    · exact False.elim (hd (by rw [Int.pow_succ,Int.pow_one] at hh; exact (Int.mul_eq_zero.mp hh).elim id id))
  apply no_positive_padded A s V hV
  exact_mod_cast (show (digitWeight s V:Int)=(A:Int)*V+1 by omega)

theorem ones_block_nonzero (A s p V : Nat) (hp : 0<p) (hV : V<2^s) :
    periodicNumerator A s p V (2^p-1)≠0 := by
  intro h
  have hp2 : 2≤2^p := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤p by omega)
  have hs2 := Nat.two_pow_pos s
  have hcast : ((2^p-1:Nat):Int)=(2:Int)^p-1 := by rw [Int.natCast_sub (by omega : 1≤2^p),Int.natCast_pow]; rfl
  have hpI : (2:Int)≤2^p := by exact_mod_cast hp2
  have hd : (2:Int)^p-1≠0 := by omega
  unfold periodicNumerator at h
  dsimp only at h
  rw [weight_ones p,hcast] at h
  have hfactor : ((digitWeight s V:Int)-(A:Int)*V-1-2^s*((s:Int)-A-2))*((2:Int)^p-1)^2=0 := by
    grind
  have he := (Int.mul_eq_zero.mp hfactor).resolve_right (by
    rw [Int.pow_succ,Int.pow_one]; exact Int.mul_ne_zero hd hd)
  let R := 2^s-1-V
  have hR : R<2^s := by dsimp [R]; omega
  have hc := weight_complement s V hV
  have hcc := congrArg (fun z : Nat => (z:Int)) hc
  simp only [Int.natCast_add,weight_ones] at hcc
  have hRcast : (R:Int)=(2:Int)^s-1-V := by dsimp [R]; rw [Int.natCast_sub (by omega : V≤2^s-1),Int.natCast_sub (by omega : 1≤2^s),Int.natCast_pow]; rfl
  change (digitWeight s V:Int)+(digitWeight s R:Int)=((s:Int)-2)*2^s+2 at hcc
  have hbad : (digitWeight s R:Int)=(A:Int)*R+A+1 := by rw [hRcast]; grind
  exact no_negative_padded A s R hR (by exact_mod_cast hbad)

#print axioms ones_block_nonzero
end BB6.Agent45WeightedDigitGap
