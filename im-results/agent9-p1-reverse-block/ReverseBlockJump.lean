import ReverseLagBlocks
import ReverseBlockDigitWeight

namespace BB6.Agent9ReverseBlock

open BB6.Agent45ReverseBlock
open BB6.Agent45.DelayedCarry
open BB6.Agent45WeightedDigitGap

/-- The modular first-jump condition used by prefix_parallel.cpp.
    The per-bit shifts sum to q*B + digitWeight k B. -/
def JumpMember (F k Y c : Nat) : Prop :=
  c < F-k ∧
  ∃ B, B < 2^k ∧
    c % 2^k =
      (Y % 2^k + 2^k - (((F-k)*B + digitWeight k B) % 2^k)) % 2^k

/-- Solve a modular subtraction using only the canonical remainders. -/
theorem mod_sub_residue (M a b y : Nat)
    (hM : 0 < M) (ha : a < M) (hb : b < M) (hy : y < M)
    (h : (a+b) % M = y) :
    a = (y+M-b) % M := by
  have hlt : a+b < M*2 := by omega
  have hq : (a+b)/M < 2 :=
    (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hlt)
  have hdiv := Nat.div_add_mod (a+b) M
  have hcases : (a+b)/M = 0 ∨ (a+b)/M = 1 := by
    have hnonneg : 0 ≤ (a+b)/M := Nat.zero_le _
    omega
  rcases hcases with h0 | h1
  · have hab : a+b=y := by
      rw [h0,h] at hdiv
      omega
    have heq : y+M-b=M+a := by omega
    rw [heq]
    simp [Nat.mod_eq_of_lt ha]
  · have hab : M+y=a+b := by
      rw [h1,h] at hdiv
      omega
    have heq : y+M-b=a := by omega
    rw [heq, Nat.mod_eq_of_lt ha]

/-- Every genuine fitted reverse walk is retained by the modular residue
    jump. This is the no-false-negative direction needed by the prefix-only
    algorithm; spurious residues are harmless. -/
theorem walk_mem_jump (F z : Nat) (ys : List Nat) (c : Nat)
    (h : Walk F z ys c) :
    JumpMember F ys.length (digits ys) c := by
  let k := ys.length
  let q := F-k
  let X := 2^k*z+digits ys
  have hc : c < q := by simpa [q,k] using walk_bound h
  obtain ⟨B,hB,he⟩ := eq_of_walk h
  have hF : q+k=F := by dsimp [q,k]; omega
  have he0 : X+corr k B=F*B+c := by simpa [X] using he
  have he' : X+corr k B=(q+k)*B+c := by
    calc
      X+corr k B = F*B+c := he0
      _ = (q+k)*B+c := by rw [← hF]
  have hvalid : (q+k)*B ≤ X+corr k B := by rw [he']; omega
  have hrem := candidate_remainder_eq q k X B hB hvalid
  have hcarry : c = X-q*B-digitWeight k B := by
    calc
      c = X+corr k B-(q+k)*B := by rw [he']; omega
      _ = X-q*B-digitWeight k B := hrem
  have hcorr := corr_le_mul k B hB
  have hprod : (q+k)*B=q*B+k*B := Nat.add_mul q k B
  have hDsum : q*B+digitWeight k B ≤ X := by
    dsimp [digitWeight]
    rw [hprod] at hvalid
    omega
  have hqB : q*B ≤ X := by omega
  have hD : digitWeight k B ≤ X-q*B := by omega
  have hsum : c+(q*B+digitWeight k B)=X := by
    rw [hcarry]
    omega
  have hdiv : 2^k ∣ 2^k*z := ⟨z,rfl⟩
  have hzmod : (2^k*z)%2^k=0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hXmod : X%2^k=digits ys%2^k := by
    dsimp [X]
    rw [Nat.add_mod,hzmod]
    simp
  let S := q*B+digitWeight k B
  have hsumEq : c+S=X := by simpa [S] using hsum
  have hsumMod : ((c%2^k)+(S%2^k))%2^k=digits ys%2^k := by
    calc
      ((c%2^k)+(S%2^k))%2^k = (c+S)%2^k := by rw [← Nat.add_mod]
      _ = X%2^k := by rw [hsumEq]
      _ = digits ys%2^k := hXmod
  have hM : 0<2^k := Nat.two_pow_pos _
  have ha : c%2^k<2^k := Nat.mod_lt _ hM
  have hb : S%2^k<2^k := Nat.mod_lt _ hM
  have hy : digits ys%2^k<2^k := Nat.mod_lt _ hM
  have hres := mod_sub_residue (2^k) (c%2^k) (S%2^k)
    (digits ys%2^k) hM ha hb hy hsumMod
  refine ⟨by simpa [q,k] using hc,B,hB,?_⟩
  simpa [q,k,S] using hres


/-- An endpoint list covers the modular first-jump candidates for a fixed
    suffix when it contains every carry satisfying the exact residue equation. -/
def JumpCover (F : Nat) (ys : List Nat) (ends : List Nat) : Prop :=
  ∀ c, JumpMember F ys.length (digits ys) c → c ∈ ends

/-- Specification of the complete modular first-jump set. The C++ implementation
    constructs this set by iterative subset-sum residues and interval lifting. -/
noncomputable def JumpCandidates (F : Nat) (ys : List Nat) : List Nat := by
  classical
  exact (List.range (F - ys.length)).filter
    (fun c => decide (JumpMember F ys.length (digits ys) c))

theorem jumpCandidates_cover (F : Nat) (ys : List Nat) :
    JumpCover F ys (JumpCandidates F ys) := by
  classical
  intro c hc
  exact List.mem_filter.mpr
    ⟨List.mem_range.mpr hc.1, decide_eq_true_eq.mpr hc⟩

/-- A genuine reverse walk survives the intersection used by the prefix-only
    algorithm: split off the final modular-jump suffix, retain its midpoint in
    the modular candidate cover, and rewind the earlier word by fitted blocks. -/
theorem walk_mem_prefix_live (F q z c : Nat) (bs : List (List Nat))
    (tail ends : List Nat)
    (hclock : F = q + bs.flatten.length + tail.length)
    (hbits : ∀ y ∈ bs.flatten ++ tail, y ≤ 1)
    (hfit : Fitted q bs)
    (hjump : JumpCover F tail ends)
    (h : Walk F z (bs.flatten ++ tail) c) :
    c ∈ blockFold q bs ends := by
  obtain ⟨d, htail, hprefix⟩ :=
    walk_split F z bs.flatten tail c h
  have hclock' : F - tail.length = q + bs.flatten.length := by omega
  have hprefix' : Walk (q + bs.flatten.length) d bs.flatten c := by
    simpa [hclock'] using hprefix
  have hbits' : ∀ y ∈ bs.flatten, y ≤ 1 := by
    intro y hy
    exact hbits y (List.mem_append.mpr (Or.inl hy))
  exact (mem_blockFold q c bs ends hbits' hfit).2
    ⟨d, hjump d (walk_mem_jump F z tail d htail), hprefix'⟩

/-- Original delayed-carry traces inherit the same prefix-only live property.
    This is source-connected: the trace rewind transports the authentic Trace
    prefix to the exact fixed-target Walk before applying the modular/block
    intersection theorem. -/
theorem trace_prefix_live (n m B a s : Nat)
    (hTrace : Trace n m B a) (hs : 1 ≤ s) (hm : s ≤ m) (hk : m - s ≤ n) :
    ∃ C c R, Trace n s C c ∧ B = C + 2^s * R ∧
      ∀ bs tail ends,
        bs.flatten ++ tail = targetWord n s C (m - s) →
        Fitted (n + s + 3) bs →
        JumpCover (n + m + 3) tail ends →
        c ∈ blockFold (n + s + 3) bs ends := by
  obtain ⟨C, c, R, htr, hB, hw⟩ :=
    trace_rewind hTrace s hs hm hk
  refine ⟨C, c, R, htr, hB, ?_⟩
  intro bs tail ends hparts hfit hjump
  have hlen : bs.flatten.length + tail.length = m - s := by
    have h := congrArg List.length hparts
    simpa [targetWord_length] using h
  have hclock : n + m + 3 =
      n + s + 3 + bs.flatten.length + tail.length := by omega
  have hbits : ∀ y ∈ bs.flatten ++ tail, y ≤ 1 := by
    intro y hy
    rw [hparts] at hy
    exact targetWord_bits n s C (m - s) y hy
  have hwalk : Walk (n + m + 3) a (bs.flatten ++ tail) c := by
    rw [hparts]
    exact hw
  exact walk_mem_prefix_live (n + m + 3) (n + s + 3) a c
    bs tail ends hclock hbits hfit hjump hwalk

/-- Concrete specification corollary using the full modular candidate set. -/
theorem trace_prefix_live_candidates (n m B a s : Nat)
    (hTrace : Trace n m B a) (hs : 1 ≤ s) (hm : s ≤ m) (hk : m - s ≤ n) :
    ∃ C c R, Trace n s C c ∧ B = C + 2^s * R ∧
      ∀ bs tail,
        bs.flatten ++ tail = targetWord n s C (m - s) →
        Fitted (n + s + 3) bs →
        c ∈ blockFold (n + s + 3) bs (JumpCandidates (n + m + 3) tail) := by
  obtain ⟨C, c, R, htr, hB, hlive⟩ :=
    trace_prefix_live n m B a s hTrace hs hm hk
  refine ⟨C, c, R, htr, hB, ?_⟩
  intro bs tail hparts hfit
  exact hlive bs tail (JumpCandidates (n + m + 3) tail)
    hparts hfit (jumpCandidates_cover (n + m + 3) tail)

#print axioms jumpCandidates_cover
#print axioms walk_mem_prefix_live
#print axioms trace_prefix_live
#print axioms trace_prefix_live_candidates

#print axioms mod_sub_residue
#print axioms walk_mem_jump

end BB6.Agent9ReverseBlock
