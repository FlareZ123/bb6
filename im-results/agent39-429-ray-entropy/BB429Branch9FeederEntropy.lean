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
  have hNJ : J+1≤N := by
    dsimp [N,branch9N]
    omega
  have hpowJK := pow2_mono (K+2) J hJK
  have hpowJN := pow2_mono (J+1) N hNJ
  exact ⟨hJK,hNJ,hpowJK,hpowJN⟩

/-- Exact affine identity along the branch-9 S-parent family. -/
private theorem branch9_affine_identity (t q r v K : Nat)
    (hr : r<4) (hK : 1≤K) (hv : K≤v)
    (hqv : q≤v) (hvlt : v<2^K) :
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
    have heq : 2^(J+1)=2^J*2 := by simp [Nat.pow_succ]
    omega
  have hJbig : 48*2^K≤12*2^J := by
    have heq : 2^(K+2)=2^K*4 := by simp [Nat.pow_succ]
    omega
  have hidx : k≤2*2^J+v := by
    dsimp [k,branch9Index,J]
    omega
  have hsmall : 8+3*v≤12*2^J := by
    omega
  have hbase : 6*2^J+8+3*k≤12*2^N+6*2^t := by
    have hmid : 6*2^J+8+3*k≤12*2^J+8+3*v := by omega
    omega
  have hdiff : 12*2^J≤12*2^N := by omega
  have hCnonneg : 8≤6*2^t+3*q := by
    have ht5 : 5≤t := by omega
    have hpowt := pow2_mono 5 t ht5
    have h32 : 2^5=32 := by decide
    omega
  dsimp [branch9A,branch9Carry,branch9Index,branch9J,branch9N]
  omega

private theorem branch9_high_counter (t q r v K : Nat)
    (ht : 5≤t) (hr : r<4) (hK : 1≤K)
    (hv : K≤v) (hqv : q≤v) (hvlt : v<2^K) :
    16*2^K≤branch9A t q r v+3 := by
  have hident := branch9_affine_identity t q r v K hr hK hv hqv hvlt
  have hb := branch9_exponent_bounds r v K hr hK hv
  rcases hb with ⟨hJK,hNJ,hpowJK,hpowJN⟩
  have hpowK : 1≤2^K := by have hp:=pow2_pos K; omega
  have hNbig : 24*2^(branch9J r v)≤12*2^(branch9N r v) := by
    have heq : 2^(branch9J r v+1)=2^(branch9J r v)*2 := by simp [Nat.pow_succ]
    omega
  have hJbig : 48*2^K≤12*2^(branch9J r v) := by
    have heq : 2^(K+2)=2^K*4 := by simp [Nat.pow_succ]
    omega
  have hdiff : 12*2^(branch9J r v)≤
      12*2^(branch9N r v)-12*2^(branch9J r v) := by omega
  have hC : 0≤branch9Carry t q := by
    dsimp [branch9Carry]
    have hpowt := pow2_mono 5 t ht
    have h32 : 2^5=32 := by decide
    omega
  have hlarge : 48*2^K≤branch9A t q r v+3+3*v := by
    rw [hident]
    omega
  omega

private theorem branch9_divisibility (t q r v K : Nat)
    (ht : 5≤t) (hr : r<4) (hK : 1≤K)
    (hv : K≤v) (hqv : q≤v) (hvlt : v<2^K) :
    2^K ∣ branch9A t q r v + 3*v + branch9Correction t q K := by
  let J := branch9J r v
  let N := branch9N r v
  let C := branch9Carry t q
  have hident := branch9_affine_identity t q r v K hr hK hv hqv hvlt
  have hb := branch9_exponent_bounds r v K hr hK hv
  rcases hb with ⟨hJK,hNJ,hpowJK,hpowJN⟩
  have hsplitN : N+2=K+(N+2-K) := by omega
  have hsplitJ : J+2=K+(J+2-K) := by omega
  have hpowN : 2^(N+2)=2^N*4 := by
    rw [show N+2=(N+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    omega
  have hpowJ : 2^(J+2)=2^J*4 := by
    rw [show J+2=(J+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    omega
  have h12N : 12*2^N=2^K*(3*2^(N+2-K)) := by
    calc
      12*2^N = 3*2^(N+2) := by rw [hpowN]; ring
      _ = 3*(2^K*2^(N+2-K)) := by rw [hsplitN,Nat.pow_add]
      _ = 2^K*(3*2^(N+2-K)) := by ring
  have h12J : 12*2^J=2^K*(3*2^(J+2-K)) := by
    calc
      12*2^J = 3*2^(J+2) := by rw [hpowJ]; ring
      _ = 3*(2^K*2^(J+2-K)) := by rw [hsplitJ,Nat.pow_add]
      _ = 2^K*(3*2^(J+2-K)) := by ring
  have horder : 3*2^(J+2-K)≤3*2^(N+2-K) := by
    have hp := pow2_mono (J+2-K) (N+2-K) (by omega)
    omega
  have hdiff : 12*2^N-12*2^J =
      2^K*(3*2^(N+2-K)-3*2^(J+2-K)) := by
    rw [h12N,h12J]
    omega
  have hpowK : 1≤2^K := by have hp:=pow2_pos K; omega
  have hCplus : C+branch9Correction t q K=(C+1)*2^K := by
    dsimp [branch9Correction,C]
    have hcarry : branch9Carry t q = 6*2^t+3*q-8 := rfl
    have hCnonneg : 8≤6*2^t+3*q := by
      have hpowt := pow2_mono 5 t ht
      have h32 : 2^5=32 := by decide
      omega
    omega
  have hsum :
      branch9A t q r v + 3*v + branch9Correction t q K =
        (12*2^N-12*2^J)+(C+branch9Correction t q K) := by
    rw [hident]
    omega
  refine ⟨3*2^(N+2-K)-3*2^(J+2-K)+(C+1), ?_⟩
  rw [hsum,hdiff,hCplus]
  ring

/-- For a fixed t and a fixed residue r satisfying t+14=r (mod 4),
the genuine branch-9 exceptional S parents have zero-density outer
parameter v= (J-r)/4 in dyadic ranges: at most 2*sqrt(2^K) of the
reachable parameters v in [K,2^K). -/
theorem branch9_side_feeder_entropy
    (t r q K : Nat)
    (ht : 5≤t) (hr : r<4) (htr : t+14=r+4*q)
    (hK : 1≤K) (hKt : t≤K)
    (l : List Nat) (hn : l.Nodup)
    (hl : ∀v, v∈l → K≤v ∧ v<2^K ∧
      BB429NewResidue.Reach (branch9A t q r v) (branch9B t q r v)) :
    l.length≤2*2^(K/2) := by
  have hqK : q≤K := by omega
  have hqv : ∀v, v∈l → q≤v := by
    intro v hv
    have hkv := (hl v hv).1
    omega
  have hcarry : 8≤6*2^t+3*q := by
    have hpowt := pow2_mono 5 t ht
    have h32 : 2^5=32 := by decide
    omega
  have he : branch9Carry t q + branch9Correction t q K =
      (branch9Carry t q+1)*2^K := by
    dsimp [branch9Correction]
    have hpowK := pow2_pos K
    omega
  have hline : ∀v, v∈l →
      branch9B t q r v + branch9Offset t = 2*branch9A t q r v := by
    intro v hv
    have hhigh := branch9_high_counter t q r v K ht hr hK
      ((hl v hv).1) (hqv v hv) ((hl v hv).2.1)
    have hpowTK : 2^t≤2^K := pow2_mono t K hKt
    have hc : branch9Offset t≤2*branch9A t q r v := by
      dsimp [branch9Offset]
      omega
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
    have hreach := (hl v hv).2.2
    have hhigh := branch9_high_counter t q r v K ht hr hK
      hvK (hqv v hv) hvlt
    have hdiv := branch9_divisibility t q r v K ht hr hK
      hvK (hqv v hv) hvlt
    exact ⟨hreach,hline v hv,hhigh,hdiv⟩
  have hbound := generic_feeder_cardinality_bound
    (branch9Offset t) K 0 3 (branch9Correction t q K) (2^K)
    (branch9A t q r) (branch9B t q r) l hn
    (by omega) (by decide) (by simp) ?_
  · exact hbound
  · intro v hv
    obtain ⟨hvK,hvlt,hreach⟩ := hl v hv
    obtain ⟨hR,hline',hhigh,hdiv⟩ := hlegal v hv
    exact ⟨hvlt,hR,hline',hhigh,hdiv⟩

#print axioms branch9_side_feeder_entropy

end BB429Branch9FeederEntropy
