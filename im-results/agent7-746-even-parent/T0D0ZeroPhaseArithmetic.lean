import Std

namespace Agent7D0

/-- The two exact source-level inverse-parent arms, copied for the arithmetic
    lemma below. The source-connected wrapper identifies this definition with
    CascadeResetInverse.ResetParent by definitional equality. -/
def ResetParentFormula (h u : Nat) : Prop :=
  (∃k, (6*2^k-1≤u ∧ u≤8*2^k-3) ∧ 2*u=8*2^k+h+k) ∨
  (∃k t d, d%2=1 ∧
    (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
    2*u+5=3^(t+1)*d ∧
    2*(2^t*d)=8*2^k+h+k+5)

theorem pow2_mod9_of_mod6_2 (n : Nat) (h : n % 6 = 2) : 2^n % 9 = 4 := by
  have hdecomp : n = 6*(n/6)+2 := by omega
  rw [hdecomp, Nat.pow_add]
  have hp : 2^(6*(n/6)) % 9 = 1 := by
    rw [Nat.pow_mul]
    induction n/6 with
    | zero => decide
    | succ m ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
  rw [Nat.mul_mod, hp]

theorem pow2_mod9_of_mod6_1 (n : Nat) (h : n % 6 = 1) : 2^n % 9 = 2 := by
  have hdecomp : n = 6*(n/6)+1 := by omega
  rw [hdecomp, Nat.pow_add]
  have hp : 2^(6*(n/6)) % 9 = 1 := by
    rw [Nat.pow_mul]
    induction n/6 with
    | zero => decide
    | succ m ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
  rw [Nat.mul_mod, hp]

theorem pow2_mod9_of_mod6_4 (n : Nat) (h : n % 6 = 4) : 2^n % 9 = 7 := by
  have hdecomp : n = 6*(n/6)+4 := by omega
  rw [hdecomp, Nat.pow_add]
  have hp : 2^(6*(n/6)) % 9 = 1 := by
    rw [Nat.pow_mul]
    induction n/6 with
    | zero => decide
    | succ m ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
  rw [Nat.mul_mod, hp]

theorem pow2_mono {m n : Nat} (h : m ≤ n) : 2^m ≤ 2^n := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step n h ih =>
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
    calc
      2^m ≤ 2^n := ih
      _ ≤ 2^(n+1) := by rw [Nat.pow_succ]; omega

theorem linear_le_pow2 (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
    rw [Nat.pow_succ]
    omega

/-- In the D0 ≡ 0 mod 3 phase, the first level-K entry lies strictly
    between the even-parent bands and fails the necessary 3-divisibility
    condition for every odd parent. -/
theorem d0_entry_no_parent
    (K a r p B D E : Nat)
    (hK : 266 ≤ K)
    (hK18 : K % 18 = 2)
    (ha18 : a % 18 = 2)
    (hra : r+a=K+1)
    (hp : p=2^K)
    (hB : B=(2*K+7)*2^(r+3))
    (hB24 : 24*p ≤ B)
    (hB28 : B ≤ 28*p)
    (hD : 3*D+16*p=B+2*K+1)
    (hE : E+D=8*p+K) :
    ¬ ∃h, ResetParentFormula h E := by
  have hK6 : K%6=2 := by omega
  have ha6 : a%6=2 := by omega
  have hr6 : r%6=1 := by omega
  have hr4 : (r+3)%6=4 := by omega
  have hc9 : (2*K+7)%9=2 := by omega
  have hk9 : (2*K+1)%9=5 := by omega
  have hp9 : p%9=4 := by rw [hp]; exact pow2_mod9_of_mod6_2 K hK6
  have hrp9 : 2^(r+3)%9=7 := pow2_mod9_of_mod6_4 (r+3) hr4
  have hB9 : B%9=5 := by
    rw [hB, Nat.mul_mod, hc9, hrp9]
  have hD3 : D%3=0 := by omega
  have hA3 : (16*p+2*K+5)%3=1 := by omega
  have hEeq : 2*E+5+2*D=16*p+2*K+5 := by omega
  have hE3 : (2*E+5)%3=1 := by omega
  have h3E : 3*E+B=40*p+K-1 := by omega
  have hpLinear : K+2 < 2*p := by
    have hpow : K+1≤p := by simpa [hp] using linear_le_pow2 K
    omega
  have hGapLow : 4*p < E := by omega
  have hGapHigh : E < 6*p-1 := by omega
  intro hparent
  rcases hparent with ⟨h, heven | hodd⟩
  · rcases heven with ⟨k, ⟨hlow,hhigh⟩, heq⟩
    by_cases hk : k<K
    · have hpow : 2^k≤2^(K-1) := pow2_mono (by omega)
      have hprev : 2^K=2*2^(K-1) := by
        calc
          2^K=2^(K-1+1) := by congr 1; omega
          _=2^(K-1)*2 := by rw [Nat.pow_succ]
          _=2*2^(K-1) := by omega
      have hupper : 8*2^k≤4*p := by
        calc
          8*2^k≤8*2^(K-1) := Nat.mul_le_mul_left 8 hpow
          _=4*p := by rw [hp,hprev]; omega
      omega
    · have hkK : K≤k := by omega
      have hpow : p≤2^k := by simpa [hp] using pow2_mono hkK
      have hlower : 6*p≤6*2^k := Nat.mul_le_mul_left 6 hpow
      omega
  · rcases hodd with ⟨k,t,d,hd,hband,hout,hsrc⟩
    have hpow : 3∣3^(t+1) := by
      rw [Nat.pow_succ]
      exact Nat.dvd_mul_left 3 (3^t)
    rcases hpow with ⟨m,hm⟩
    have hdiv : 3∣3^(t+1)*d := by
      rw [hm, Nat.mul_assoc]
      exact Nat.dvd_mul_right 3 (m*d)
    have hdivE : 3∣2*E+5 := by rw [hout]; exact hdiv
    have hmod : (2*E+5)%3=0 := Nat.dvd_iff_mod_eq_zero.mp hdivE
    omega

end Agent7D0

namespace Agent7D0

def d0Level (n : Nat) : Nat := 3*2^(18*n)+8

theorem pow2_18n_mod18 (n : Nat) (hn : 1≤n) : 2^(18*n)%18=10 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => decide
    | succ m =>
      have ih' : 2^(18*(m+1))%18=10 := ih (by omega)
      calc
        2^(18*(m+2))%18 = (2^(18*(m+1))*2^18)%18 := by
          rw [show 18*(m+2)=18*(m+1)+18 by omega, Nat.pow_add]
        _ = ((2^(18*(m+1))%18)*(2^18%18))%18 := by rw [Nat.mul_mod]
        _ = 10 := by rw [ih', show 2^18%18=10 by decide]

/-- Explicit infinite parameter sequence: a=18n+2 and
    K=3*2^(18n)+8. Its dyadic scale ratio is in [3/2,7/4]. -/
theorem explicit_params (n : Nat) (hn : 1≤n) :
    ∃ K a r p B, K=d0Level n ∧ 266≤K ∧ K%18=2 ∧ a%18=2 ∧ r+a=K+1 ∧
      p=2^K ∧ B=(2*K+7)*2^(r+3) ∧ 24*p≤B ∧ B≤28*p := by
  let a := 18*n+2
  let K := d0Level n
  let r := K+1-a
  let p := 2^K
  let B := (2*K+7)*2^(r+3)
  have hKgeA : a≤K := by
    dsimp [a,K,d0Level]
    have hlin : 18*n+1≤2^(18*n) := linear_le_pow2 (18*n)
    omega
  refine ⟨K,a,r,p,B,rfl,?_,?_,?_,?_,rfl,rfl,?_,?_⟩
  · dsimp [K,d0Level]
    have hpow : 2^18≤2^(18*n) := pow2_mono (by omega)
    have h18 : 2^18=262144 := by decide
    omega
  · dsimp [K,d0Level]
    rw [Nat.add_mod, Nat.mul_mod, pow2_18n_mod18 n hn]
  · dsimp [a]
    omega
  · dsimp [r]
    omega
  · -- lower and upper source-band bounds
    have hpow18 : 2^18≤2^(18*n) := pow2_mono (by omega)
    have h2a : 2^a=4*2^(18*n) := by
      dsimp [a]
      rw [Nat.pow_add]
      have hpow2 : 2^2=4 := by decide
      rw [hpow2]
      simp [Nat.mul_comm]
    have hKsplit : K=a+(K-a) := by omega
    have hpSplit : p=2^a*2^(K-a) := by
      dsimp [p]
      calc
        2^K=2^(a+(K-a)) := congrArg (fun x : Nat => 2^x) hKsplit
        _=2^a*2^(K-a) := by rw [Nat.pow_add]
    have hr3 : r+3=4+(K-a) := by dsimp [r]; omega
    have hBsplit : B=16*(2*K+7)*2^(K-a) := by
      dsimp [B]
      rw [hr3,Nat.pow_add]
      have hpow4 : 2^4=16 := by decide
      rw [hpow4]
      simp [Nat.mul_assoc,Nat.mul_comm]
    have hloC : 3*2^a≤2*(2*K+7) := by
      rw [h2a]
      dsimp [K,d0Level]
      omega
    have hhiC : 4*(2*K+7)≤7*2^a := by
      rw [h2a]
      dsimp [K,d0Level]
      have h18 : 2^18=262144 := by decide
      omega
    have hloC' : 24*2^a≤16*(2*K+7) := by omega
    have hlowB : 24*p≤B := by
      rw [hpSplit,hBsplit]
      have hm := Nat.mul_le_mul_right (2^(K-a)) hloC'
      simpa [Nat.mul_assoc] using hm
    exact hlowB
  · -- upper source-band bound
    have hpow18 : 2^18≤2^(18*n) := pow2_mono (by omega)
    have h2a : 2^a=4*2^(18*n) := by
      dsimp [a]
      rw [Nat.pow_add]
      have hpow2 : 2^2=4 := by decide
      rw [hpow2]
      simp [Nat.mul_comm]
    have hKsplit : K=a+(K-a) := by omega
    have hpSplit : p=2^a*2^(K-a) := by
      dsimp [p]
      calc
        2^K=2^(a+(K-a)) := congrArg (fun x : Nat => 2^x) hKsplit
        _=2^a*2^(K-a) := by rw [Nat.pow_add]
    have hr3 : r+3=4+(K-a) := by dsimp [r]; omega
    have hBsplit : B=16*(2*K+7)*2^(K-a) := by
      dsimp [B]
      rw [hr3,Nat.pow_add]
      have hpow4 : 2^4=16 := by decide
      rw [hpow4]
      simp [Nat.mul_assoc,Nat.mul_comm]
    have hhiC : 4*(2*K+7)≤7*2^a := by
      rw [h2a]
      dsimp [K,d0Level]
      have h18 : 2^18=262144 := by decide
      omega
    have hhiC' : 16*(2*K+7)≤28*2^a := by omega
    rw [hpSplit,hBsplit]
    have hm := Nat.mul_le_mul_right (2^(K-a)) hhiC'
    simpa [Nat.mul_assoc] using hm

/-- Every member of the explicit sequence has a parentless first entry. -/
theorem explicit_family_no_parent (n : Nat) (hn : 1≤n) :
    ∃ K E, K=d0Level n ∧ 266≤K ∧ K%18=2 ∧ 2<E ∧
      4*2^K≤E+K+4 ∧ E+K+5<8*2^K ∧
      (∃ r B, r%2=1 ∧ B=(2*K+7)*2^(r+3) ∧
        16*2^K+4*K+20≤B ∧ B≤28*2^K+4*K+8 ∧
        3*E+B=40*2^K+K-1) ∧
      ¬∃h, ResetParentFormula h E := by
  obtain ⟨K,a,r,p,B,hKexact,hK,hK18,ha18,hra,hp,hB,hB24,hB28⟩ := explicit_params n hn
  let N := B+2*K+1-16*p
  have hK6 : K%6=2 := by omega
  have hr6 : r%6=1 := by omega
  have hr4 : (r+3)%6=4 := by omega
  have hc9 : (2*K+7)%9=2 := by omega
  have hp9 : p%9=4 := by rw [hp]; exact pow2_mod9_of_mod6_2 K hK6
  have hrp9 : 2^(r+3)%9=7 := pow2_mod9_of_mod6_4 (r+3) hr4
  have hB9 : B%9=5 := by
    rw [hB,Nat.mul_mod,hc9,hrp9]
  have hN3 : N%3=0 := by dsimp [N]; omega
  have hNdiv : 3∣N := Nat.dvd_iff_mod_eq_zero.mpr hN3
  let D := N/3
  have hD : 3*D+16*p=B+2*K+1 := by
    have hmul : 3*(N/3)=N := Nat.mul_div_cancel' hNdiv
    dsimp [D,N]
    omega
  let M := 40*p+K-1-B
  have hM3 : M%3=0 := by
    have hp3 : p%3=1 := by omega
    have hB3 : B%3=2 := by omega
    have hK3 : K%3=2 := by omega
    dsimp [M]
    omega
  have hMdiv : 3∣M := Nat.dvd_iff_mod_eq_zero.mpr hM3
  let E := M/3
  have h3E : 3*E+B=40*p+K-1 := by
    have hmul : 3*(M/3)=M := Nat.mul_div_cancel' hMdiv
    dsimp [E,M]
    omega
  have hE : E+D=8*p+K := by omega
  have hEgt2 : 2<E := by
    have hpPos : 1≤p := by rw [hp]; exact Nat.one_le_pow K 2 (by decide)
    omega
  have hpLinear2 : K+4≤2*p := by
    have hpow : K+1≤p := by simpa [hp] using linear_le_pow2 K
    omega
  have hFirstLo : 4*p≤E+K+4 := by omega
  have hFirstHi : E+K+5<8*p := by omega
  have hRodd : r%2=1 := by omega
  have hBsourceLo : 16*p+4*K+20≤B := by omega
  have hBsourceHi : B≤28*p+4*K+8 := by omega
  have hFatal : 3*E+B=40*p+K-1 := by omega
  have hNo := d0_entry_no_parent K a r p B D E hK hK18 ha18 hra hp hB hB24 hB28 hD hE
  refine ⟨K,E,hKexact,hK,hK18,hEgt2,?_,?_,?_,hNo⟩
  · simpa [hp] using hFirstLo
  · simpa [hp] using hFirstHi
  · exact ⟨r,B,hRodd,hB,by simpa [hp] using hBsourceLo,by simpa [hp] using hBsourceHi,by simpa [hp] using hFatal⟩

/-- The levels of the parentless-entry family are unbounded, hence the
    family contains infinitely many distinct fatal-source levels. -/
theorem d0_family_unbounded (M : Nat) :
    ∃ K E, M<K ∧ K%18=2 ∧ 2<E ∧ ¬∃h, ResetParentFormula h E := by
  let n := M+1
  have hn : 1≤n := by omega
  obtain ⟨K,E,hKexact,hK,hK18,hEgt2,hFirstLo,hFirstHi,hTail,hNo⟩ :=
    explicit_family_no_parent n hn
  refine ⟨K,E,?_,hK18,hEgt2,hNo⟩
  rw [hKexact]
  dsimp [d0Level,n]
  have hlinear : 18*(M+1)+1≤2^(18*(M+1)) := linear_le_pow2 (18*(M+1))
  omega

end Agent7D0
