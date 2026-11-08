import OneShallowFiniteBridge
import TwoRunModel
import RootTwoDivisor

namespace BB6.Agent43TwoRun

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- A full scalar inverse word with arbitrary 2-runs around one 0-edge
cannot reach the shifted wall. The original-source lift remains separate. -/
theorem no_scalar_zero_word_wall
    (n s r p d : Nat) (hn : 14≤n)
    (hp : 8^s*p=2^n) (hd : 8^s*d=14*n+92)
    (Wa Ba Wb Wc Bc : Int)
    (hpre : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
    (hshallow : 2*Wb=Wa+4*Ba-8)
    (hsuffix : TwoRun ((2:Int)^n) Wb (Ba+1) r Wc Bc)
    (hwall : Wc=12*(2:Int)^n) : False := by
  let P : Int := (2:Int)^n
  let N : Int := n
  let q : Nat := 8^s
  have hqpos : 0<(8:Int)^s := Int.pow_pos (by decide)
  have henergyPre := run_energy P (14*P+2*N+4) (N+6) Wa Ba s hpre
  have hcostPre := run_cost P (14*P+2*N+4) (N+6) Wa Ba s hpre
  have hIroot : I P (14*P+2*N+4) (N+6) = 98*P-(14*N+92) := by
    unfold I
    omega
  rw [hIroot] at henergyPre
  have hpInt : (8:Int)^s*(p:Int)=P := by
    have hh := congrArg (fun x : Nat => (↑x:Int)) hp
    simpa [P,Int.natCast_mul,Int.natCast_pow] using hh
  have hdInt : (8:Int)^s*(d:Int)=14*N+92 := by
    have hh := congrArg (fun x : Nat => (↑x:Int)) hd
    simpa [N,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using hh
  have hIpreVal : I P Wa Ba = 98*(p:Int)-(d:Int) := by
    have hh : (8:Int)^s*(98*(p:Int)-(d:Int))=98*P-(14*N+92) := by
      rw [Int.mul_sub]
      have hs : (8:Int)^s*(98*(p:Int))=98*P := by
        calc
          _ = 98*((8:Int)^s*(p:Int)) := by ac_rfl
          _ = 98*P := by rw [hpInt]
      omega
    have heq : (8:Int)^s*I P Wa Ba =
      (8:Int)^s*(98*(p:Int)-(d:Int)) := by omega
    exact Int.eq_of_mul_eq_mul_left (by omega) heq
  have hIpost : 2*I P Wb (Ba+1) = I P Wa Ba-588*P+84*Ba-232 := by
    unfold I
    omega
  have henergyPost := run_energy P Wb (Ba+1) Wc Bc r hsuffix
  have hcostPost := run_cost P Wb (Ba+1) Wc Bc r hsuffix
  have hIend : I P Wc Bc= -(112*N+336*(s:Int)+336*(r:Int)+400) := by
    rw [hwall]
    rw [hcostPost, hcostPre]
    unfold I
    omega
  rw [hIend] at henergyPost
  have hBpre : Ba=N+6+3*(s:Int) := hcostPre
  have hPostScaled : 2*I P Wb (Ba+1) =
      -(2*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400)) := by
    rw [henergyPost]
    calc
      2*(-((8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400))) =
        -(2*((8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400))) :=
          Int.mul_neg _ _
      _ = -(2*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400)) := by
        congr 1
        ac_rfl
  have hCombine : 588*P-98*(p:Int) =
      2*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400) +
      84*N+252*(s:Int)+272-(d:Int) := by
    rw [hIpreVal] at hIpost
    omega
  have hk : (↑(588*q-98):Int) = 588*(q:Int)-98 := by
    have hqp : 1≤q := Nat.one_le_pow s 8 (by decide)
    omega
  have hcastEq : (↑((588*q-98)*p):Int) =
      ↑((224*n+672*s+672*r+800)*8^r +
        (84*n+252*s+272-d)) := by
    have hdle : d≤14*n+92 := by
      have hq : 1≤8^s := Nat.one_le_pow s 8 (by decide)
      have hh := Nat.mul_le_mul_right d hq
      omega
    have hdle' : d≤84*n+252*s+272 := by omega
    have hcastSub : (↑(84*n+252*s+272-d):Int)=
        84*N+252*(s:Int)+272-(d:Int) := by
      omega
    have hright : (↑((224*n+672*s+672*r+800)*(8:Nat)^r):Int) =
        2*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400) := by
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
      change (224*N+672*(s:Int)+672*(r:Int)+800)*(8:Int)^r =
        2*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400)
      have hlinear : (224*N+672*(s:Int)+672*(r:Int)+800) =
          2*(112*N+336*(s:Int)+336*(r:Int)+400) := by omega
      rw [hlinear]
      ac_rfl
    have hleft : (↑((588*q-98)*p):Int) = 588*P-98*(p:Int) := by
      simp only [Int.natCast_mul,hk]
      calc
        _ = 588*((q:Int)*(p:Int))-98*(p:Int) := by
          rw [Int.sub_mul]; ac_rfl
        _ = 588*P-98*(p:Int) := by
          have hqeq : (q:Int)=(8:Int)^s := by dsimp [q]
          rw [hqeq,hpInt]
    have hrhs : (↑((224*n+672*s+672*r+800)*8^r +
        (84*n+252*s+272-d)):Int) =
        2*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+400) +
          84*N+252*(s:Int)+272-(d:Int) := by
      simp only [Int.natCast_add]
      rw [hright,hcastSub]
      omega
    rw [hleft,hrhs]
    exact hCombine
  have hEqNat : (588*q-98)*p=
      (224*n+672*s+672*r+800)*8^r+(84*n+252*s+272-d) :=
    Int.ofNat_inj.mp hcastEq
  exact no_zero_middle_all n s r p d hn
    (by simpa [q] using hp) (by simpa [q] using hd)
    (by simpa [q] using hEqNat)

/-- The root prefix itself forces the dyadic quotient witnesses; users of
this stronger model theorem need only provide full exact scalar transitions. -/
theorem no_scalar_zero_word_wall_from_root
    (n s r : Nat) (hn : 14≤n)
    (Wa Ba Wb Wc Bc : Int)
    (hpre : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
    (hshallow : 2*Wb=Wa+4*Ba-8)
    (hsuffix : TwoRun ((2:Int)^n) Wb (Ba+1) r Wc Bc)
    (hwall : Wc=12*(2:Int)^n) : False := by
  obtain ⟨h3s,hDdiv⟩ := root_two_prefix_divisor n s Wa Ba hn hpre
  have hpow : (8:Nat)^s=2^(3*s) := by
    simpa only [show (8:Nat)=2^3 by decide] using (Nat.pow_mul 2 3 s).symm
  have hPdiv : (8:Nat)^s∣2^n := by
    rw [hpow]
    exact Nat.pow_dvd_pow 2 h3s
  obtain ⟨p,hp⟩ := hPdiv
  obtain ⟨d,hd⟩ := hDdiv
  exact no_scalar_zero_word_wall n s r p d hn
    (by simpa [Nat.mul_comm] using hp.symm)
    (by simpa [Nat.mul_comm] using hd.symm)
    Wa Ba Wb Wc Bc hpre hshallow hsuffix hwall

#print axioms BB6.Agent43TwoRun.no_scalar_zero_word_wall
#print axioms BB6.Agent43TwoRun.no_scalar_zero_word_wall_from_root
end BB6.Agent43TwoRun