import BB429GenericFeederEntropy
import Lean.Elab.Tactic.Omega

namespace BB429Branch9FeederEntropy

open BB429NewResidue
open BB429InverseWord

set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

/-- Branch-9's outer reset exponent, written as J=4v+r. -/
def branch9J (r v : Nat) : Nat := 4*v+r

/-- The special branch-9 diagonal has n=8*2^J-11 and N=n+J. -/
def branch9N (r v : Nat) : Nat :=
  8*2^(branch9J r v) + branch9J r v - 11

/-- The interior S-parent index forced by t=N-(4k+3). -/
def branch9Index (q r v : Nat) : Nat :=
  2*2^(branch9J r v) + v-q

/-- First coordinate X of the exact branch-9 exceptional S parent. -/
def branch9A (t q r v : Nat) : Nat :=
  (12*2^(branch9N r v) + 6*2^t) -
    (6*2^(branch9J r v) + 8 + 3*branch9Index q r v)

/-- Its affine-ray offset: Y+offset=2X. -/
def branch9Offset (t : Nat) : Nat := 24*2^t-21

/-- Second coordinate, defined on the exact slope-two ray. -/
def branch9B (t q r v : Nat) : Nat :=
  2*branch9A t q r v - branch9Offset t

/-- The affine carry left after cancelling the branch-index term. -/
def branch9Carry (t q : Nat) : Nat := 6*2^t+3*q-8

/-- A fixed correction making X(v)+3v+e divisible by 2^K
    throughout the high-exponent range v>=K. -/
def branch9Correction (t q K : Nat) : Nat :=
  (branch9Carry t q + 1)*2^K - branch9Carry t q

private theorem pow2_pos (n : Nat) : 0 < 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

private theorem pow2_mono (a b : Nat) (h : a ≤ b) : 2^a ≤ 2^b := by
  revert a
  induction b with
  | zero =>
      intro a h
      have : a=0 := by omega
      subst a
      simp
  | succ b ih =>
      intro a h
      by_cases hab : a ≤ b
      · have hp := ih a hab
        rw [Nat.pow_succ]
        omega
      · have ha : a=b+1 := by omega
        subst a
        simp

private theorem branch9_exponent_bounds (r v K : Nat)
    (hr : r<4) (hK : 1≤K) (hv : K≤v) :
    K+2≤branch9J r v ∧
    branch9J r v+1≤branch9N r v ∧
    2^(K+2)≤2^(branch9J r v) ∧
    2^(branch9J r v+1)≤2^(branch9N r v) := by
  let J := branch9J r v
  let N := branch9N r v
  have hJK : K+2≤J := by
    dsimp [J,branch9J]
    omega
  have hJpos : 1≤J := by omega
  have hpowJ2 : 2≤2^J := by
    have hp : 0<2^(J-1) := pow2_pos (J-1)
    have heq : J=(J-1)+1 := by omega
    rw [heq,Nat.pow_succ]
    omega
  have hpowJ2' : 2≤2^(4*v+r) := by
    simpa [J,branch9J] using hpowJ2
  have hNJ : J+1≤N := by
    dsimp [N,branch9N,J,branch9J]
    omega
  have hpowJK := pow2_mono (K+2) J hJK
  have hpowJN := pow2_mono (J+1) N hNJ
  exact ⟨hJK,hNJ,hpowJK,hpowJN⟩

/-- The actual branch-9 index is nonnegative exactly when the
interior position satisfies t+3≤N. -/
private theorem branch9_index_nonnegative (t q r v : Nat)
    (htr : t+14=r+4*q)
    (hTN : t+3≤branch9N r v) :
    q≤2*2^(branch9J r v)+v := by
  have hh := hTN
  dsimp [branch9N,branch9J] at hh
  dsimp [branch9J]
  omega

/-- Exact affine identity along the branch-9 S-parent family. -/
private theorem branch9_affine_identity (t q r v K : Nat)
    (ht : 5≤t) (hr : r<4) (hK : 1≤K) (hv : K≤v)
    (hqidx : q≤2*2^(branch9J r v)+v) (hvlt : v<2^K) :
    branch9A t q r v + 3*v =
      (12*2^(branch9N r v)-12*2^(branch9J r v)) +
        branch9Carry t q := by
  let J := branch9J r v
  let N := branch9N r v
  let k := branch9Index q r v
  let C := branch9Carry t q
  have hb := branch9_exponent_bounds r v K hr hK hv
  rcases hb with ⟨hJK,hNJ,hpowJK,hpowJN⟩
  have hpowK : 1≤2^K := by have hp:=pow2_pos K; omega
  have hNbig : 24*2^J≤12*2^N := by
    have hpow2 : 2^(J+1)=2^J*2 := by simp [Nat.pow_succ]
    calc
      24*2^J = 12*(2^J*2) := by omega
      _ = 12*2^(J+1) := by rw [←hpow2]
      _ ≤ 12*2^N := Nat.mul_le_mul_left 12 hpowJN
  have hJbig : 48*2^K≤12*2^J := by
    have hpow4 : 2^(K+2)=2^K*4 := by
      rw [Nat.pow_add]
    calc
      48*2^K = 12*(2^K*4) := by omega
      _ = 12*2^(K+2) := by rw [←hpow4]
      _ ≤ 12*2^J := Nat.mul_le_mul_left 12 hpowJK
  have hqidx' : q≤2*2^J+v := hqidx
  have hidx : k+q=2*2^J+v := by
    dsimp [k,branch9Index,J]
    exact Nat.sub_add_cancel hqidx'
  have hsmall : 8+3*v≤12*2^J := by
    omega
  have hbase : 6*2^J+8+3*k≤12*2^N+6*2^t := by
    have hmid : 6*2^J+8+3*k≤12*2^J+8+3*v := by omega
    omega
  have hdiff : 12*2^J≤12*2^N := by omega
  have hCnonneg : 8≤6*2^t+3*q := by
    have hpowt := pow2_mono 5 t ht
    have h32 : 2^5=32 := by decide
    omega
  have hAeq :
      branch9A t q r v+(6*2^J+8+3*k)=12*2^N+6*2^t := by
    change (12*2^N+6*2^t-(6*2^J+8+3*k))+(6*2^J+8+3*k)=12*2^N+6*2^t
    exact Nat.sub_add_cancel hbase
  have hCeq : branch9Carry t q+8=6*2^t+3*q := by
    change (6*2^t+3*q-8)+8=6*2^t+3*q
    exact Nat.sub_add_cancel hCnonneg
  have hidx3 : 3*k+3*q=6*2^J+3*v := by omega
  have hsum : branch9A t q r v+3*v+12*2^J=12*2^N+C := by omega
  calc
    branch9A t q r v+3*v =
        (branch9A t q r v+3*v+12*2^J)-12*2^J := by omega
    _ = (12*2^N+C)-12*2^J := by rw [hsum]
    _ = (12*2^N-12*2^J)+C := by omega

private theorem branch9_high_counter (t q r v K : Nat)
    (ht : 5≤t) (hr : r<4) (hK : 1≤K)
    (hv : K≤v) (hqidx : q≤2*2^(branch9J r v)+v) (hvlt : v<2^K) :
    16*2^K≤branch9A t q r v+3 := by
  have hident := branch9_affine_identity t q r v K ht hr hK hv hqidx hvlt
  have hb := branch9_exponent_bounds r v K hr hK hv
  rcases hb with ⟨hJK,hNJ,hpowJK,hpowJN⟩
  have hpowK : 1≤2^K := by have hp:=pow2_pos K; omega
  have hNbig : 24*2^(branch9J r v)≤12*2^(branch9N r v) := by
    have hpow2 : 2^(branch9J r v+1)=2^(branch9J r v)*2 := by
      simp [Nat.pow_succ]
    calc
      24*2^(branch9J r v) =
          12*(2^(branch9J r v)*2) := by omega
      _ = 12*2^(branch9J r v+1) := by rw [←hpow2]
      _ ≤ 12*2^(branch9N r v) := Nat.mul_le_mul_left 12 hpowJN
  have hJbig : 48*2^K≤12*2^(branch9J r v) := by
    have hpow4 : 2^(K+2)=2^K*4 := by
      rw [Nat.pow_add]
    calc
      48*2^K = 12*(2^K*4) := by omega
      _ = 12*2^(K+2) := by rw [←hpow4]
      _ ≤ 12*2^(branch9J r v) := Nat.mul_le_mul_left 12 hpowJK
  have hdiff : 12*2^(branch9J r v)≤
      12*2^(branch9N r v)-12*2^(branch9J r v) := by omega
  have hC : 0≤branch9Carry t q := by
    dsimp [branch9Carry]
    have hpowt := pow2_mono 5 t ht
    have h32 : 2^5=32 := by decide
    omega
  have hlarge : 48*2^K≤branch9A t q r v+3+3*v := by
    omega
  omega

private theorem branch9_divisibility (t q r v K : Nat)
    (ht : 5≤t) (hr : r<4) (hK : 1≤K)
    (hv : K≤v) (hqidx : q≤2*2^(branch9J r v)+v) (hvlt : v<2^K) :
    2^K ∣ branch9A t q r v + 3*v + branch9Correction t q K := by
  let J := branch9J r v
  let N := branch9N r v
  let C := branch9Carry t q
  have hident := branch9_affine_identity t q r v K ht hr hK hv hqidx hvlt
  have hb := branch9_exponent_bounds r v K hr hK hv
  rcases hb with ⟨hJK,hNJ,hpowJK,hpowJN⟩
  have hsplitN : N+2=K+(N+2-K) := by omega
  have hsplitJ : J+2=K+(J+2-K) := by omega
  have hpowN : 2^(N+2)=2^N*4 := by
    rw [show N+2=(N+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    simp [Nat.mul_assoc]
  have hpowJ : 2^(J+2)=2^J*4 := by
    rw [show J+2=(J+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    simp [Nat.mul_assoc]
  have h12N : 12*2^N=2^K*(3*2^(N+2-K)) := by
    calc
      12*2^N = 3*(2^N*4) := by
        have h12 : 12=3*4 := by decide
        rw [h12]
        calc
          (3*4)*2^N = 3*(4*2^N) := by rw [Nat.mul_assoc]
          _ = 3*(2^N*4) := by rw [Nat.mul_comm 4 (2^N)]
      _ = 3*2^(N+2) := by rw [←hpowN]
      _ = 3*2^(K+(N+2-K)) := by rw [←hsplitN]
       _ = 3*(2^K*2^(N+2-K)) := by rw [Nat.pow_add]
      _ = 2^K*(3*2^(N+2-K)) := by
        calc
          3*(2^K*2^(N+2-K)) = (3*2^K)*2^(N+2-K) := by rw [←Nat.mul_assoc]
          _ = (2^K*3)*2^(N+2-K) := by rw [Nat.mul_comm 3 (2^K)]
          _ = 2^K*(3*2^(N+2-K)) := by rw [Nat.mul_assoc]
  have h12J : 12*2^J=2^K*(3*2^(J+2-K)) := by
    calc
      12*2^J = 3*(2^J*4) := by
        have h12 : 12=3*4 := by decide
        rw [h12]
        calc
          (3*4)*2^J = 3*(4*2^J) := by rw [Nat.mul_assoc]
          _ = 3*(2^J*4) := by rw [Nat.mul_comm 4 (2^J)]
      _ = 3*2^(J+2) := by rw [←hpowJ]
      _ = 3*2^(K+(J+2-K)) := by rw [←hsplitJ]
       _ = 3*(2^K*2^(J+2-K)) := by rw [Nat.pow_add]
      _ = 2^K*(3*2^(J+2-K)) := by
        calc
          3*(2^K*2^(J+2-K)) = (3*2^K)*2^(J+2-K) := by rw [←Nat.mul_assoc]
          _ = (2^K*3)*2^(J+2-K) := by rw [Nat.mul_comm 3 (2^K)]
          _ = 2^K*(3*2^(J+2-K)) := by rw [Nat.mul_assoc]
  let P := 3*2^(N+2-K)
  let Q := 3*2^(J+2-K)
  have horder : Q≤P := by
    dsimp [P,Q]
    have hp := pow2_mono (J+2-K) (N+2-K) (by omega)
    omega
  have hmul_sub : 2^K*P-2^K*Q=2^K*(P-Q) := by
    have hp : P=Q+(P-Q) := by omega
    have hmulP : 2^K*P=2^K*Q+2^K*(P-Q) := by
      have h := congrArg (fun z : Nat => 2^K*z) hp
      rw [Nat.mul_add] at h
      exact h
    calc
      2^K*P-2^K*Q = (2^K*Q+2^K*(P-Q))-2^K*Q := by rw [hmulP]
      _ = 2^K*(P-Q) := by omega
  have hdiff : 12*2^N-12*2^J = 2^K*(P-Q) := by
    rw [h12N,h12J]
    exact hmul_sub
  have hpowK : 1≤2^K := by have hp:=pow2_pos K; omega
  have hCplus : C+branch9Correction t q K=(C+1)*2^K := by
    change C+((C+1)*2^K-C)=(C+1)*2^K
    have hpowK : 1≤2^K := by have hp:=pow2_pos K; omega
    have hmul : C+1≤(C+1)*2^K := by
      have hh := Nat.mul_le_mul_left (C+1) hpowK
      simpa using hh
    have hCbound : C≤(C+1)*2^K := by omega
    calc
      C+((C+1)*2^K-C)=((C+1)*2^K-C)+C := by omega
      _ = (C+1)*2^K := Nat.sub_add_cancel hCbound
  have hsum :
      branch9A t q r v + 3*v + branch9Correction t q K =
        (12*2^N-12*2^J)+(C+branch9Correction t q K) := by
    rw [hident]
    exact Nat.add_assoc _ _ _
  refine ⟨P-Q+(C+1), ?_⟩
  calc
    branch9A t q r v + 3*v + branch9Correction t q K =
        (12*2^N-12*2^J)+(C+branch9Correction t q K) := hsum
    _ = 2^K*(P-Q)+(C+1)*2^K := by rw [hdiff,hCplus]
    _ = 2^K*(P-Q)+2^K*(C+1) := by rw [Nat.mul_comm (C+1) (2^K)]
    _ = 2^K*(P-Q+(C+1)) := by
      symm
      exact Nat.mul_add _ _ _

/-- The diagonal ray identity is valid throughout the actual interior
branch-9 range t+3≤N; it does not require the artificial restriction t≤K. -/
private theorem branch9_offset_le_two_A (t q r v K : Nat)
    (ht : 5≤t) (hr : r<4) (hK : 1≤K) (hv : K≤v)
    (hqidx : q≤2*2^(branch9J r v)+v) (hvlt : v<2^K)
    (hTN : t+3≤branch9N r v) :
    branch9Offset t≤2*branch9A t q r v := by
  have hident := branch9_affine_identity t q r v K ht hr hK hv hqidx hvlt
  have hb := branch9_exponent_bounds r v K hr hK hv
  rcases hb with ⟨hJK,hNJ,hpowJK,hpowJN⟩
  have hpowTN : 8*2^t≤2^(branch9N r v) := by
    have hp := pow2_mono (t+3) (branch9N r v) hTN
    have heq : 2^(t+3)=2^t*2^3 := by rw [Nat.pow_add]
    have h8 : (2:Nat)^3=8 := by decide
    rw [h8] at heq
    omega
  have hpowJN' : 2*2^(branch9J r v)≤2^(branch9N r v) := by
    have hp := hpowJN
    rw [Nat.pow_succ] at hp
    omega
  have hNK : K+3≤branch9N r v := by omega
  have hpowKN : 8*2^K≤2^(branch9N r v) := by
    have hp := pow2_mono (K+3) (branch9N r v) hNK
    have heq : 2^(K+3)=2^K*2^3 := by rw [Nat.pow_add]
    have h8 : (2:Nat)^3=8 := by decide
    rw [h8] at heq
    omega
  have hvsmall : v<2^(branch9N r v) := by omega
  have hC8 : branch9Carry t q+8=6*2^t+3*q := by
    dsimp [branch9Carry]
    have hpowt := pow2_mono 5 t ht
    have h32 : 2^5=32 := by decide
    omega
  have hAeq :
      branch9A t q r v+12*2^(branch9J r v)+8+3*v =
        12*2^(branch9N r v)+6*2^t+3*q := by
    have hh := hident
    omega
  have hA2 :
      2*branch9A t q r v+24*2^(branch9J r v)+16+6*v =
        24*2^(branch9N r v)+12*2^t+6*q := by
    have h := congrArg (fun z : Nat => 2*z) hAeq
    simp only [Nat.mul_add] at h
    omega
  have hterms :
      12*2^t+24*2^(branch9J r v)+6*v≤24*2^(branch9N r v) := by
    have htterm : 12*2^t≤6*2^(branch9N r v) := by omega
    have hjterm : 24*2^(branch9J r v)≤12*2^(branch9N r v) := by omega
    have hvterm : 6*v≤6*2^(branch9N r v) := by omega
    omega
  have hgoal : 24*2^t≤2*branch9A t q r v+21 := by omega
  dsimp [branch9Offset]
  omega

/-- For a fixed t and residue r satisfying t+14=r (mod 4), the genuine
branch-9 exceptional S parents have at most 2*sqrt(2^K) reachable outer
parameters v in [K,2^K), uniformly over the full actual interior range
t+3≤N. No assumption t≤K is needed. -/
theorem branch9_side_feeder_entropy
    (t r q K : Nat)
    (ht : 5≤t) (hr : r<4) (htr : t+14=r+4*q)
    (hK : 1≤K)
    (l : List Nat) (hn : l.Nodup)
    (hl : ∀v, v∈l → K≤v ∧ v<2^K ∧
      t+3≤branch9N r v ∧
      BB429NewResidue.Reach (branch9A t q r v) (branch9B t q r v)) :
    l.length≤2^(K/2) := by
  have hqidx : ∀v, v∈l → q≤2*2^(branch9J r v)+v := by
    intro v hv
    exact branch9_index_nonnegative t q r v htr ((hl v hv).2.2.1)
  have hline : ∀v, v∈l →
      branch9B t q r v + branch9Offset t = 2*branch9A t q r v := by
    intro v hv
    have hc := branch9_offset_le_two_A t q r v K ht hr hK
      ((hl v hv).1) (hqidx v hv) ((hl v hv).2.1)
      ((hl v hv).2.2.1)
    dsimp [branch9B]
    exact Nat.sub_add_cancel hc
  have hlegal :
      ∀v, v∈l →
        BB429NewResidue.Reach (branch9A t q r v) (branch9B t q r v) ∧
        branch9B t q r v + branch9Offset t =
          2*branch9A t q r v ∧
        16*2^K≤branch9A t q r v+3 ∧
        2^K∣branch9A t q r v+3*v+branch9Correction t q K := by
    intro v hv
    have hvK := (hl v hv).1
    have hvlt := (hl v hv).2.1
    have hTN := (hl v hv).2.2.1
    have hreach := (hl v hv).2.2.2
    have hidx := hqidx v hv
    have hhigh := branch9_high_counter t q r v K ht hr hK
      hvK hidx hvlt
    have hdiv := branch9_divisibility t q r v K ht hr hK
      hvK hidx hvlt
    exact ⟨hreach,hline v hv,hhigh,hdiv⟩
  have hfeed : ∀v, v∈l →
      v<2^K ∧ BB429NewResidue.Reach (branch9A t q r v) (branch9B t q r v) ∧
      branch9B t q r v+branch9Offset t=2*branch9A t q r v ∧
      16*2^K≤branch9A t q r v+3 ∧
      2^K∣branch9A t q r v+3*v+branch9Correction t q K := by
    intro v hv
    have hvlt := (hl v hv).2.1
    obtain ⟨hR,hline',hhigh,hdiv⟩ := hlegal v hv
    exact ⟨hvlt,hR,hline',hhigh,hdiv⟩
  have hphase : (anyRayPhase (branch9Offset t))%2=0 := by
    unfold anyRayPhase
    have hc : branch9Offset t%2=1 := by
      dsimp [branch9Offset]
      omega
    have hc4 : branch9Offset t%4=1 ∨ branch9Offset t%4=3 := by omega
    rcases hc4 with h|h <;> omega
  exact generic_feeder_cardinality_bound_even_phase
    (branch9Offset t) K 0 3 (branch9Correction t q K) (2^K)
    (branch9A t q r) (branch9B t q r) l hn
    (by omega) (by decide) (by simp) hfeed hphase

#print axioms branch9_side_feeder_entropy

end BB429Branch9FeederEntropy
