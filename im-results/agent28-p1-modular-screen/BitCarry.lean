import Lean
namespace BB6.Agent28BitCarry

-- A mask retaining the lower b bits of each of 2^r lanes of width 2b.
def laneMask (b : Nat) : Nat → Nat
  | 0 => 2^b-1
  | r+1 => let x := laneMask b r; x ||| (x <<< (2*b*2^r))

theorem laneMask_bit (b r q s : Nat) (hq : q<2^r) (hs : s<b) :
    (laneMask b r).testBit (2*b*q+s) = true := by
  induction r generalizing q with
  | zero =>
      have hq0 : q=0 := by simp at hq; omega
      simp [laneMask, hq0, hs]
  | succ r ih =>
      rw [laneMask, Nat.testBit_or]
      by_cases h : q<2^r
      · simp [ih q h]
      · let q' := q-2^r
        have hq' : q'<2^r := by
          rw [Nat.pow_succ] at hq
          dsimp [q']; omega
        have hqEq : q=2^r+q' := by dsimp [q']; omega
        have heq : 2*b*q+s=2*b*2^r+(2*b*q'+s) := by
          rw [hqEq, Nat.mul_add]
          omega
        rw [Nat.testBit_shiftLeft, heq]
        have hge : 2*b*2^r ≤ 2*b*2^r+(2*b*q'+s) := by omega
        have hs' : 2*b*2^r+(2*b*q'+s)-2*b*2^r=2*b*q'+s := by omega
        simp [hge, hs', ih q' hq']

-- Position of the original bit 2i after k packing stages.
def packedPos (k i : Nat) : Nat := 2*2^k*(i/2^k)+i%2^k

theorem packedPos_step (k i : Nat) :
    packedPos k i = packedPos (k+1) i ∨
    packedPos k i = packedPos (k+1) i + 2^k := by
  let b := 2^k
  have hdiv : i/b/2=i/(b*2) := Nat.div_div_eq_div_mul _ _ _
  have hmod : i%(b*2)=i%b+b*(i/b%2) := Nat.mod_mul
  have hdecomp : i/b = 2*(i/(b*2))+(i/b%2) := by
    rw [← hdiv]
    exact (Nat.div_add_mod _ _).symm
  have hpar : i/b%2=0 ∨ i/b%2=1 := by omega
  unfold packedPos
  rw [Nat.pow_succ]
  change 2*b*(i/b)+i%b=2*(b*2)*(i/(b*2))+i%(b*2) ∨
    2*b*(i/b)+i%b=2*(b*2)*(i/(b*2))+i%(b*2)+b
  rw [hdecomp, Nat.mul_add, hmod]
  have hmain : 2*b*(2*(i/(b*2)))=2*(b*2)*(i/(b*2)) := by ac_rfl
  rw [hmain]
  rcases hpar with h0 | h1
  · left
    simp [h0]
  · right
    simp [h1]
    omega

theorem packedPos_mask (k L i : Nat) (hk : k≤L) (hi : i<2^L) :
    (laneMask (2^k) (L-k)).testBit (packedPos k i) = true := by
  have hpow : 2^L=2^k*2^(L-k) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have hdiv : i/2^k < 2^(L-k) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2
    simpa [hpow, Nat.mul_comm] using hi
  exact laneMask_bit _ _ _ _ hdiv (Nat.mod_lt _ (Nat.two_pow_pos k))

def packStep (L k x : Nat) : Nat :=
  (x ||| (x >>> 2^k)) &&& laneMask (2^(k+1)) (L-(k+1))

theorem packStep_sound (L k x i : Nat) (hk : k<L) (hi : i<2^L)
    (h : x.testBit (packedPos k i)=true) :
    (packStep L k x).testBit (packedPos (k+1) i)=true := by
  rw [packStep, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
    packedPos_mask (k+1) L i (by omega) hi]
  rcases packedPos_step k i with he | he
  · rw [he] at h
    simp [h]
  · rw [he, Nat.add_comm] at h
    simp [h]

def packFrom (L k x : Nat) : Nat → Nat
  | 0 => x
  | r+1 => packFrom L (k+1) (packStep L k x) r

theorem packFrom_sound (L k x r i : Nat) (hk : k+r=L) (hi : i<2^L)
    (h : x.testBit (packedPos k i)=true) :
    (packFrom L k x r).testBit (packedPos L i)=true := by
  induction r generalizing k x with
  | zero => simpa [packFrom, show k=L by omega] using h
  | succ r ih =>
      exact ih (k+1) (packStep L k x) (by omega) (packStep_sound L k x i (by omega) hi h)

def packEven (L x : Nat) : Nat := packFrom L 0 (x &&& laneMask 1 L) L

theorem packEven_sound (L x i : Nat) (hi : i<2^L) (h : x.testBit (2*i)=true) :
    (packEven L x).testBit i=true := by
  have hpos0 : packedPos 0 i=2*i := by simp [packedPos]; omega
  have hposL : packedPos L i=i := by
    simp [packedPos, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  have hm := packedPos_mask 0 L i (by omega) hi
  rw [hpos0] at hm
  simp only [Nat.pow_zero, Nat.sub_zero] at hm
  have hstart : (x &&& laneMask 1 L).testBit (packedPos 0 i)=true := by
    simp [hpos0, h, hm]
  have hp := packFrom_sound L 0 (x &&& laneMask 1 L) L i (by omega) hi hstart
  simpa [packEven, hposL] using hp

-- A layer is a Nat bitset: index c is present iff its bit is set.
def step (L C states : Nat) : Nat := packEven L (states ||| (states <<< C))

theorem step_omit_sound (L C states c : Nat) (hc : c<2^L)
    (h : states.testBit (2*c)=true) : (step L C states).testBit c=true := by
  apply packEven_sound L _ c hc
  simp [h]

theorem step_select_sound (L C states c q : Nat) (hc : c<2^L)
    (h : states.testBit q=true) (he : q+C=2*c) :
    (step L C states).testBit c=true := by
  apply packEven_sound L _ c hc
  have hge : C≤2*c := by omega
  have hq : 2*c-C=q := by omega
  simp [hge,hq,h]

#print axioms packEven_sound
#print axioms step_omit_sound
#print axioms step_select_sound
end BB6.Agent28BitCarry

namespace BB6.Agent28BitCarry

def listStep (C : Nat) (cs : List Nat) : List Nat :=
  cs.flatMap fun c =>
    (if c%2=0 then [c/2] else []) ++
    (if (c+C)%2=0 then [(c+C)/2] else [])

def listRun (n j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k+1 => listRun n (j+1) (listStep (n+3+j) cs) k

def modRun (L n j states : Nat) : Nat → Nat
  | 0 => states
  | k+1 => if states=0 then 0 else modRun L n (j+1) (step L (n+3+j) states) k

theorem listStep_sound (L C states : Nat) (cs : List Nat)
    (hC : C<2^L) (hcs : ∀ c∈cs, c<2^L ∧ states.testBit c=true) :
    ∀ c∈listStep C cs, c<2^L ∧ (step L C states).testBit c=true := by
  intro c hc
  simp only [listStep, List.mem_flatMap] at hc
  obtain ⟨q,hq,hopt⟩ := hc
  obtain ⟨hqb,hbit⟩ := hcs q hq
  rw [List.mem_append] at hopt
  rcases hopt with h | h
  · by_cases he : q%2=0
    · simp [he] at h
      subst c
      have hbound : q/2<2^L := by omega
      refine ⟨hbound, step_omit_sound L C states _ hbound ?_⟩
      rw [show 2*(q/2)=q by omega]
      exact hbit
    · simp [he] at h
  · by_cases he : (q+C)%2=0
    · simp [he] at h
      subst c
      have hbound : (q+C)/2<2^L := by omega
      exact ⟨hbound, step_select_sound L C states _ q hbound hbit (by omega)⟩
    · simp [he] at h

theorem listRun_sound (L n j states k : Nat) (cs : List Nat)
    (hC : n+3+j+k<2^L)
    (hcs : ∀ c∈cs, c<2^L ∧ states.testBit c=true) :
    ∀ c∈listRun n j cs k, c<2^L ∧ (modRun L n j states k).testBit c=true := by
  induction k generalizing j states cs with
  | zero => simpa [listRun, modRun] using hcs
  | succ k ih =>
      intro c hc
      by_cases hz : states=0
      · have hnil : cs=[] := by
          cases cs with
          | nil => rfl
          | cons q qs =>
              have hbit := (hcs q (by simp)).2
              simp [hz] at hbit
        subst cs
        have hzero : ∀ j k, listRun n j [] k=[] := by
          intro j k
          induction k generalizing j with
          | zero => rfl
          | succ k ih => simpa [listRun, listStep] using ih (j+1)
        simp [hzero] at hc
      · have hcs' := listStep_sound L (n+3+j) states cs (by omega) hcs
        have hi := ih (j+1) (step L (n+3+j) states) (listStep (n+3+j) cs)
          (by omega) hcs' c (by simpa [listRun] using hc)
        simpa [modRun, hz] using hi

theorem empty_of_modRun_zero (L n k : Nat) (hC : n+4+k<2^L)
    (hz : modRun L n 1 (2^((n+2)/2)) k=0) :
    listRun n 1 [((n+2)/2)] k=[] := by
  have hstart : ∀ c∈[((n+2)/2)], c<2^L ∧ (2^((n+2)/2)).testBit c=true := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    exact ⟨by omega, Nat.testBit_two_pow_self⟩
  cases he : listRun n 1 [((n+2)/2)] k with
  | nil => rfl
  | cons c cs =>
      have hc : c∈listRun n 1 [((n+2)/2)] k := by rw [he]; exact List.mem_cons_self
      have hbit := (listRun_sound L n 1 (2^((n+2)/2)) k _ (by omega) hstart c hc).2
      rw [hz] at hbit
      simp at hbit

#print axioms listRun_sound
#print axioms empty_of_modRun_zero
end BB6.Agent28BitCarry
