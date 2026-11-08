import OneShallowModelBridge

namespace BB6.Agent43TwoRun
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem no_scalar_one_word_wall
    (n s r p d : Nat) (hn : 14≤n)
    (hp : 8^s*p=2^n) (hd : 8^s*d=14*n+92)
    (Wa Ba Wb Wc Bc : Int)
    (hpre : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
    (hshallow : 4*Wb=Wa+28*(2:Int)^n+8*Ba-8)
    (hsuffix : TwoRun ((2:Int)^n) Wb (Ba+2) r Wc Bc)
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
  have hIpost : 4*I P Wb (Ba+2) = I P Wa Ba-392*P+56*Ba-136 := by
    unfold I
    omega
  have henergyPost := run_energy P Wb (Ba+2) Wc Bc r hsuffix
  have hcostPost := run_cost P Wb (Ba+2) Wc Bc r hsuffix
  have hIend : I P Wc Bc= -(112*N+336*(s:Int)+336*(r:Int)+512) := by
    rw [hwall]
    rw [hcostPost, hcostPre]
    unfold I
    omega
  rw [hIend] at henergyPost
  have hBpre : Ba=N+6+3*(s:Int) := hcostPre
  have hPostScaled : 4*I P Wb (Ba+2) =
      -(4*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512)) := by
    rw [henergyPost]
    calc
      4*(-((8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512))) =
        -(4*((8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512))) :=
          Int.mul_neg _ _
      _ = -(4*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512)) := by
        congr 1
        ac_rfl
  have hCombine : 392*P-98*(p:Int) =
      4*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512) +
      56*N+168*(s:Int)+200-(d:Int) := by
    rw [hIpreVal] at hIpost
    omega
  have hk : (↑(392*q-98):Int) = 392*(q:Int)-98 := by
    have hqp : 1≤q := Nat.one_le_pow s 8 (by decide)
    omega
  have hcastEq : (↑((392*q-98)*p):Int) =
      ↑((448*n+1344*s+1344*r+2048)*8^r +
        (56*n+168*s+200-d)) := by
    have hdle : d≤14*n+92 := by
      have hq : 1≤8^s := Nat.one_le_pow s 8 (by decide)
      have hh := Nat.mul_le_mul_right d hq
      omega
    have hdle' : d≤56*n+168*s+200 := by omega
    have hcastSub : (↑(56*n+168*s+200-d):Int)=
        56*N+168*(s:Int)+200-(d:Int) := by
      omega
    have hright : (↑((448*n+1344*s+1344*r+2048)*(8:Nat)^r):Int) =
        4*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512) := by
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow]
      change (448*N+1344*(s:Int)+1344*(r:Int)+2048)*(8:Int)^r =
        4*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512)
      have hlinear : (448*N+1344*(s:Int)+1344*(r:Int)+2048) =
          4*(112*N+336*(s:Int)+336*(r:Int)+512) := by omega
      rw [hlinear]
      ac_rfl
    have hleft : (↑((392*q-98)*p):Int) = 392*P-98*(p:Int) := by
      simp only [Int.natCast_mul,hk]
      calc
        _ = 392*((q:Int)*(p:Int))-98*(p:Int) := by
          rw [Int.sub_mul]; ac_rfl
        _ = 392*P-98*(p:Int) := by
          have hqeq : (q:Int)=(8:Int)^s := by dsimp [q]
          rw [hqeq,hpInt]
    have hrhs : (↑((448*n+1344*s+1344*r+2048)*8^r +
        (56*n+168*s+200-d)):Int) =
        4*(8:Int)^r*(112*N+336*(s:Int)+336*(r:Int)+512) +
          56*N+168*(s:Int)+200-(d:Int) := by
      simp only [Int.natCast_add]
      rw [hright,hcastSub]
      omega
    rw [hleft,hrhs]
    exact hCombine
  have hEqNat : (392*q-98)*p=
      (448*n+1344*s+1344*r+2048)*8^r+(56*n+168*s+200-d) :=
    Int.ofNat_inj.mp hcastEq
  exact no_one_middle_all n s r p d hn
    (by simpa [q] using hp) (by simpa [q] using hd)
    (by simpa [q] using hEqNat)

#print axioms BB6.Agent43TwoRun.no_scalar_one_word_wall

/-- Root-only t=1 model exclusion: divisibility supplied by the genuine
initial scalar root and its exact depth-two prefix. -/
theorem no_scalar_one_word_wall_from_root
    (n s r : Nat) (hn : 14≤n)
    (Wa Ba Wb Wc Bc : Int)
    (hpre : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
    (hshallow : 4*Wb=Wa+28*(2:Int)^n+8*Ba-8)
    (hsuffix : TwoRun ((2:Int)^n) Wb (Ba+2) r Wc Bc)
    (hwall : Wc=12*(2:Int)^n) : False := by
  obtain ⟨h3s,hDdiv⟩ := root_two_prefix_divisor n s Wa Ba hn hpre
  have hpow : (8:Nat)^s=2^(3*s) := by
    simpa only [show (8:Nat)=2^3 by decide] using (Nat.pow_mul 2 3 s).symm
  have hPdiv : (8:Nat)^s∣2^n := by
    rw [hpow]
    exact Nat.pow_dvd_pow 2 h3s
  obtain ⟨p,hp⟩ := hPdiv
  obtain ⟨d,hd⟩ := hDdiv
  exact no_scalar_one_word_wall n s r p d hn
    (by simpa [Nat.mul_comm] using hp.symm)
    (by simpa [Nat.mul_comm] using hd.symm)
    Wa Ba Wb Wc Bc hpre hshallow hsuffix hwall

#print axioms BB6.Agent43TwoRun.no_scalar_one_word_wall_from_root
end BB6.Agent43TwoRun