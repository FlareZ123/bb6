import EpochBasinBound
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321BasinDensity
open BB6.Agent2F321Basin
open BB6.Agent2F321DangerCount

/-- The cutoff is small relative to k for deeper basins, balancing the
    long-prefix diameter and the short-epoch target count. -/
def gap (j k : Nat) : Nat := k / 4^(j+1)
def cutoff (j k : Nat) : Nat := max 2 (gap j k)

theorem cutoff_range (j k : Nat) (hk : 2≤k) : 2≤cutoff j k ∧ cutoff j k≤k := by
  have hg : gap j k≤k := Nat.div_le_self _ _
  unfold cutoff
  omega

def immediateBound (k : Nat) : Nat := 2*fib (k+12)

def basinBound : Nat → Nat → Nat
  | 0,k => immediateBound k
  | j+1,k =>
    let m := cutoff j k
    immediateBound k + 2*(k+1)*fib (m+4)*(2*diameter k m+1+2*basinBound j (k+4))

noncomputable def basinCover : Nat → Nat → List (Nat×Nat)
  | 0,k => anchorCover k
  | j+1,k => anchorCover k ++ epochPreCover k (cutoff j k) (basinCover j (k+4))

theorem immediateCover_length (k : Nat) : (anchorCover k).length≤immediateBound k := by
  have h1 := codesThrough_count 1 k
  have h2 := codesThrough_count 2 k
  unfold anchorCover immediateBound
  simp only [List.length_append]
  omega

theorem basinCover_length (j k : Nat) : (basinCover j k).length≤basinBound j k := by
  induction j generalizing k with
  | zero => exact immediateCover_length k
  | succ j ih =>
      simp only [basinCover,basinBound,List.length_append]
      have h1 := immediateCover_length k
      have h2 := epochPreCover_length (k:=k) (m:=cutoff j k) (targets:=basinCover j (k+4))
      have h3 := ih (k+4)
      have hinner : 2*diameter k (cutoff j k)+1+2*(basinCover j (k+4)).length ≤
          2*diameter k (cutoff j k)+1+2*basinBound j (k+4) := by omega
      have hmul := Nat.mul_le_mul_left (2*(k+1)*fib (cutoff j k+4)) hinner
      omega

theorem basinCover_complete {j k R c} (hk : 2≤k) (hR : R≤2^k) (hb : Basin j R c) :
    (R,c)∈basinCover j k := by
  induction j generalizing k R c with
  | zero => exact danger_mem_cover hk hR hb
  | succ j ih =>
      change DangerousAnchor R c ∨ (c=1∨c=2) ∧ ∃ U e, Epoch R c U e ∧ Basin j U e at hb
      rcases hb with hd | ⟨hc,U,e,he,hb⟩
      · exact List.mem_append.mpr (Or.inl (danger_mem_cover hk hR hd))
      · have hm := cutoff_range j k hk
        exact List.mem_append.mpr (Or.inr (epochPreCover_complete hm.1 hm.2 hc hR he
          (fun hU=>ih (by omega) hU hb)))

theorem basin_count_bound (j k : Nat) (hk : 2≤k) (xs : List (Nat×Nat))
    (hnd : xs.Nodup) (hall : ∀ p∈xs, p.1≤2^k ∧ Basin j p.1 p.2) : xs.length≤basinBound j k := by
  have hs : xs⊆basinCover j k := by
    intro p hp
    exact basinCover_complete hk (hall p hp).1 (hall p hp).2
  exact Nat.le_trans (hnd.length_le_of_subset hs) (basinCover_length j k)

/-- A rational dyadic estimate avoiding real logarithms. -/
theorem fib_four_step (n : Nat) : fib (n+6)≤8*fib (n+2) := by
  have h := fib_step_mono (n+1)
  have e0 : fib (n+2)=fib (n+1)+fib n := rfl
  have e1 : fib (n+3)=fib (n+2)+fib (n+1) := rfl
  have e2 : fib (n+4)=fib (n+3)+fib (n+2) := rfl
  have e3 : fib (n+5)=fib (n+4)+fib (n+3) := rfl
  have e4 : fib (n+6)=fib (n+5)+fib (n+4) := rfl
  omega

theorem fib_dyadic (n : Nat) : fib (n+4)≤8*2^(n-n/4) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : n<4
      · have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
        rcases h with rfl|rfl|rfl|rfl <;> decide
      · let m := n-4
        have hm : m+4=n := by dsimp [m]; omega
        have hrec := ih m (by dsimp [m]; omega)
        have hstep := fib_four_step (m+2)
        have he1 : m+2+6=n+4 := by omega
        have he2 : m+2+2=m+4 := by omega
        rw [he1,he2] at hstep
        have hdiv : n/4=m/4+1 := by omega
        have hExp : n-n/4=(m-m/4)+3 := by
          have hd : m/4≤m := Nat.div_le_self _ _
          omega
        rw [hExp,Nat.pow_add]
        change fib (n+4)≤8*(2^(m-m/4)*8)
        omega

theorem immediate_dyadic (k : Nat) : immediateBound k≤1024*2^(k-k/4) := by
  have h := fib_dyadic (k+8)
  have he : (k+8)-(k+8)/4=(k-k/4)+6 := by omega
  rw [he,Nat.pow_add] at h
  change fib (k+12)≤8*(2^(k-k/4)*64) at h
  unfold immediateBound
  omega

theorem gap_succ (j k : Nat) : gap j k/4=gap (j+1) k := by
  unfold gap
  rw [Nat.div_div_eq_div_mul,show j+1+1=(j+1).succ by omega,Nat.pow_succ 4 (j+1)]

theorem gap_le_quarter (j k : Nat) : gap j k≤k/4 := by
  unfold gap
  apply Nat.div_le_div_left _ (by decide)
  exact Nat.pow_le_pow_right (n:=4) (by decide) (by omega : 1≤j+1)

def C (j : Nat) : Nat := 2^(16+12*j)
def scalePoly (j k : Nat) : Nat := (k+4*j+1)^j

theorem C_succ (j : Nat) : C (j+1)=4096*C j := by
  unfold C
  rw [show 16+12*(j+1)=(16+12*j)+12 by omega,Nat.pow_add]
  change 2^(16+12*j)*4096=4096*2^(16+12*j)
  exact Nat.mul_comm _ _

theorem C_pos (j : Nat) : 1≤C j := Nat.one_le_pow _ _ (by decide)

/-- Explicit sublinear count for each fixed number of resets. No individual
    H/F epoch length is bounded in the definition of Basin. -/
theorem basin_dyadic (j k : Nat) (hk : 2≤k) :
    basinBound j k ≤ C j*scalePoly j k*2^(k-gap j k) := by
  induction j generalizing k with
  | zero =>
      have h := immediate_dyadic k
      change immediateBound k≤65536*1*2^(k-k/4)
      omega
  | succ j ih =>
      let m := cutoff j k
      let q := gap (j+1) k
      let p := k+4*(j+1)+1
      let X := 2^(k-q)
      have hm : 2≤m ∧ m≤k := cutoff_range j k hk
      have hmg : gap j k≤m := by unfold m cutoff; omega
      have hq : q≤m/4 := by
        change gap (j+1) k≤m/4
        rw [←gap_succ]
        exact Nat.div_le_div_right hmg
      have hqk : q≤k := Nat.div_le_self _ _
      have hmd : m/4≤m := Nat.div_le_self _ _
      have hgmono : gap j k≤gap j (k+4) := Nat.div_le_div_right (by omega)
      have hgg : gap j (k+4)≤k+4 := Nat.div_le_self _ _
      have hm2 : m≤gap j (k+4)+2 := by unfold m cutoff; omega
      have hExpL : (m-m/4)+(k-m)≤k-q := by omega
      have hExpS : (m-m/4)+((k+4)-gap j (k+4))≤(k-q)+6 := by omega
      have hLpow : 2^((m-m/4)+(k-m))≤X := Nat.pow_le_pow_right (by decide) hExpL
      have hSpow : 2^((m-m/4)+((k+4)-gap j (k+4)))≤64*X := by
        have h := Nat.pow_le_pow_right (n:=2) (by decide) hExpS
        rw [Nat.pow_add 2 (k-q) 6] at h
        change 2^((m-m/4)+((k+4)-gap j (k+4)))≤X*64 at h
        omega
      have hf := fib_dyadic m
      have hdiam : 2*diameter k m+1≤33*2^(k-m) := by
        unfold diameter
        have h := Nat.one_le_pow (k-m) 2 (by decide)
        omega
      have hLong0 := Nat.mul_le_mul hf hdiam
      have hLongEq : (8*2^(m-m/4))*(33*2^(k-m))=264*2^((m-m/4)+(k-m)) := by
        rw [Nat.pow_add]
        change (8*2^(m-m/4))*(33*2^(k-m))=(8*33)*(2^(m-m/4)*2^(k-m))
        ac_rfl
      rw [hLongEq] at hLong0
      have hLong : fib (m+4)*(2*diameter k m+1)≤264*X :=
        Nat.le_trans hLong0 (Nat.mul_le_mul_left _ hLpow)
      have hPrev := ih (k+4) (by omega)
      have hpEq : scalePoly j (k+4)=p^j := by
        unfold scalePoly p
        congr 1
        omega
      rw [hpEq] at hPrev
      have hPrev2 := Nat.mul_le_mul_left 2 hPrev
      have hShort0 := Nat.mul_le_mul hf hPrev2
      have hShortEq : (8*2^(m-m/4))*(2*(C j*p^j*2^(k+4-gap j (k+4))))=
          16*(C j*p^j)*2^((m-m/4)+(k+4-gap j (k+4))) := by
        rw [Nat.pow_add]
        change (8*2^(m-m/4))*(2*(C j*p^j*2^(k+4-gap j (k+4))))=
          (8*2)*(C j*p^j)*(2^(m-m/4)*2^(k+4-gap j (k+4)))
        ac_rfl
      rw [hShortEq] at hShort0
      have hShort1 := Nat.mul_le_mul_left (16*(C j*p^j)) hSpow
      have hShort2 : 16*(C j*p^j)*(64*X)=1024*(C j*p^j*X) := by
        change 16*(C j*p^j)*(64*X)=(16*64)*(C j*p^j*X)
        ac_rfl
      rw [hShort2] at hShort1
      have hShort : fib (m+4)*(2*basinBound j (k+4))≤1024*(C j*p^j*X) := Nat.le_trans hShort0 hShort1
      have hP1 : 1≤p^j := Nat.one_le_pow _ _ (by dsimp [p]; omega)
      have hCP : 1≤C j*p^j := by simpa using Nat.mul_le_mul (C_pos j) hP1
      have hLongPad : 264*X≤512*(C j*p^j*X) := by
        have h := Nat.mul_le_mul_right X (show 264≤512*(C j*p^j) by omega)
        rw [Nat.mul_assoc] at h
        exact h
      have hTotal : fib (m+4)*(2*diameter k m+1+2*basinBound j (k+4))≤1536*(C j*p^j*X) := by
        rw [Nat.mul_add]
        omega
      have hOuter : 2*(k+1)* (fib (m+4)*(2*diameter k m+1+2*basinBound j (k+4)))≤
          3072*(C j*p^(j+1)*X) := by
        have h := Nat.mul_le_mul (show 2*(k+1)≤2*p by dsimp [p]; omega) hTotal
        rw [show (2*p)*(1536*(C j*p^j*X))=3072*(C j*p^(j+1)*X) by
          rw [Nat.pow_succ]
          change (2*p)*(1536*(C j*p^j*X))=(2*1536)*(C j*(p^j*p)*X)
          ac_rfl] at h
        exact h
      have hImm := immediate_dyadic k
      have hqQuarter : q≤k/4 := gap_le_quarter _ _
      have hImmPow : 2^(k-k/4)≤X := Nat.pow_le_pow_right (by decide) (by omega)
      have hImm1 := Nat.le_trans hImm (Nat.mul_le_mul_left 1024 hImmPow)
      have hCP1 : 1≤C j*p^(j+1) := by
        have hp : 1≤p^(j+1) := Nat.one_le_pow _ _ (by dsimp [p]; omega)
        simpa using Nat.mul_le_mul (C_pos j) hp
      have hImm2 : 1024*X≤1024*(C j*p^(j+1)*X) := by
        have h := Nat.mul_le_mul_right X (show 1024≤1024*(C j*p^(j+1)) by omega)
        rw [Nat.mul_assoc] at h
        exact h
      change immediateBound k+2*(k+1)*fib (m+4)*(2*diameter k m+1+2*basinBound j (k+4))≤
        C (j+1)*p^(j+1)*X
      rw [C_succ, Nat.mul_assoc (2*(k+1))]
      rw [show 4096*C j*p^(j+1)*X=4096*(C j*p^(j+1)*X) by ac_rfl]
      omega

theorem basin_count_dyadic (j k : Nat) (hk : 2≤k) (xs : List (Nat×Nat))
    (hnd : xs.Nodup) (hall : ∀ p∈xs, p.1≤2^k ∧ Basin j p.1 p.2) :
    xs.length≤C j*scalePoly j k*2^(k-gap j k) :=
  Nat.le_trans (basin_count_bound j k hk xs hnd hall) (basin_dyadic j k hk)

#print axioms basin_count_bound
#print axioms fib_dyadic
#print axioms basin_dyadic
#print axioms basin_count_dyadic
end BB6.Agent2F321BasinDensity
