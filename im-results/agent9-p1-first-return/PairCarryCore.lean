import Lean

namespace BB6.Agent9PairCarry

/-- Mask the first b bits of each of 2^s lanes of width 4b. -/
def lane4 (b : Nat) : Nat → Nat
  | 0 => 2^b-1
  | s+1 => let x := lane4 b s; x ||| (x <<< (4*b*2^s))

theorem lane4_sound (b s q i : Nat) (hq : q<2^s) (hi : i<b) :
    (lane4 b s).testBit (4*b*q+i)=true := by
  induction s generalizing q with
  | zero =>
    have hq0 : q=0 := by simp at hq; omega
    simp [lane4,hq0,hi]
  | succ s ih =>
    rw [lane4,Nat.testBit_or]
    by_cases h : q<2^s
    · simp [ih q h]
    · let q' := q-2^s
      have hq' : q'<2^s := by rw [Nat.pow_succ] at hq; dsimp [q']; omega
      have hqEq : q=2^s+q' := by dsimp [q']; omega
      have heq : 4*b*q+i=4*b*2^s+(4*b*q'+i) := by rw [hqEq,Nat.mul_add]; omega
      rw [Nat.testBit_shiftLeft,heq]
      simp [show 4*b*2^s≤4*b*2^s+(4*b*q'+i) by omega,
        show 4*b*2^s+(4*b*q'+i)-4*b*2^s=4*b*q'+i by omega,ih q' hq']

def pos4 (k i : Nat) : Nat := 4*2^k*(i/2^k)+i%2^k

theorem pos4_step (k i : Nat) : pos4 k i=pos4 (k+1) i ∨
    pos4 k i=pos4 (k+1) i+3*2^k := by
  let b := 2^k
  have hdiv : i/b/2=i/(b*2) := Nat.div_div_eq_div_mul _ _ _
  have hmod : i%(b*2)=i%b+b*(i/b%2) := Nat.mod_mul
  have hdecomp : i/b=2*(i/(b*2))+(i/b%2) := by
    rw [← hdiv]; exact (Nat.div_add_mod _ _).symm
  have hpar : i/b%2=0 ∨ i/b%2=1 := by omega
  unfold pos4
  rw [Nat.pow_succ]
  change 4*b*(i/b)+i%b=4*(b*2)*(i/(b*2))+i%(b*2) ∨
    4*b*(i/b)+i%b=4*(b*2)*(i/(b*2))+i%(b*2)+3*b
  rw [hdecomp,Nat.mul_add,hmod]
  have hmain : 4*b*(2*(i/(b*2)))=4*(b*2)*(i/(b*2)) := by ac_rfl
  rw [hmain]
  rcases hpar with h0|h1
  · left; simp [h0]
  · right; simp [h1]; omega

theorem pos4_mask (k L i : Nat) (hk : k≤L) (hi : i<2^L) :
    (lane4 (2^k) (L-k)).testBit (pos4 k i)=true := by
  have hpow : 2^L=2^k*2^(L-k) := by rw [← Nat.pow_add,Nat.add_sub_of_le hk]
  have hdiv : i/2^k<2^(L-k) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2
    simpa [hpow,Nat.mul_comm] using hi
  exact lane4_sound _ _ _ _ hdiv (Nat.mod_lt _ (Nat.two_pow_pos k))

/-- The fixed masks are computed once, then used by each paired clock. -/
def spreadPlan (L : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | k+1 => (3*2^k,lane4 (2^k) (L-k)) :: spreadPlan L k

def spreadWith (plan : List (Nat × Nat)) (x : Nat) : Nat :=
  plan.foldl (fun x (s,m) => (x ||| (x <<< s)) &&& m) x

theorem spreadWith_sound (L k x i : Nat) (hk : k≤L) (hi : i<2^L)
    (hx : x.testBit (pos4 k i)=true) :
    (spreadWith (spreadPlan L k) x).testBit (pos4 0 i)=true := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    simp only [spreadWith,spreadPlan,List.foldl_cons]
    apply ih _ (by omega)
    rw [Nat.testBit_and,Nat.testBit_or,pos4_mask k L i (by omega) hi]
    rcases pos4_step k i with h|h
    · rw [h]; simp [hx]
    · rw [h,Nat.testBit_shiftLeft]
      simp [show 3*2^k≤pos4 (k+1) i+3*2^k by omega,
        show pos4 (k+1) i+3*2^k-3*2^k=pos4 (k+1) i by omega,hx]

theorem spread4_sound (L x i : Nat) (hi : i<2^L) (hx : x.testBit i=true) :
    (spreadWith (spreadPlan L L) x).testBit (4*i)=true := by
  have h0 : pos4 0 i=4*i := by simp [pos4,Nat.mod_one]
  have hL : pos4 L i=i := by simp [pos4,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
  have h := spreadWith_sound L L x i (by omega) hi (by simpa [hL] using hx)
  simpa [h0] using h

/-- The scaled strict interior at an even clock 2r consists of 1,...,r-2. -/
def halfMask (r : Nat) : Nat := (2^(r-2)-1) <<< 1

theorem halfMask_sound (r i : Nat) (hi : 1≤i ∧ i+2≤r) :
    (halfMask r).testBit i=true := by
  unfold halfMask
  rw [Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
  simp [show 1≤i by omega,show i-1<r-2 by omega]

/-- Two ordinary reverse clocks, from 2r+2 to 2r, on even carries.
The four shifts encode the possible values of the intermediate quotients. -/
def pairBack (plan : List (Nat × Nat)) (r bits : Nat) : Nat :=
  let u := spreadWith plan bits
  (u ||| (u >>> r) ||| (u >>> (2*r+1)) ||| (u >>> (3*r+1))) &&& halfMask r

theorem four_cases (r a b : Nat) (ha : a+1≤r) (hb : 1≤b ∧ b+2≤r)
    (h : ((4*a)%(2*r+1))%r=b) :
    4*a=b ∨ 4*a=b+r ∨ 4*a=b+(2*r+1) ∨ 4*a=b+(3*r+1) := by
  have hmid : 4*a<2*(2*r+1) := by omega
  by_cases hlo : 4*a<2*r+1
  · rw [Nat.mod_eq_of_lt hlo] at h
    by_cases h1 : 4*a<r
    · rw [Nat.mod_eq_of_lt h1] at h; omega
    · by_cases h2 : 4*a<2*r
      · rw [Nat.mod_eq_sub_mod (by omega : r≤4*a),Nat.mod_eq_of_lt (by omega : 4*a-r<r)] at h
        omega
      · have he : 4*a=2*r := by omega
        rw [he,Nat.mul_mod_left] at h
        omega
  · rw [Nat.mod_eq_sub_mod (by omega : 2*r+1≤4*a),Nat.mod_eq_of_lt (by omega : 4*a-(2*r+1)<2*r+1)] at h
    by_cases h1 : 4*a-(2*r+1)<r
    · rw [Nat.mod_eq_of_lt h1] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega : r≤4*a-(2*r+1)),Nat.mod_eq_of_lt (by omega : 4*a-(2*r+1)-r<r)] at h
      omega

theorem pairBack_sound (L r bits a b : Nat) (ha : a+1≤r) (hcap : a<2^L)
    (hb : 1≤b ∧ b+2≤r) (h : ((4*a)%(2*r+1))%r=b)
    (hbit : bits.testBit a=true) :
    (pairBack (spreadPlan L L) r bits).testBit b=true := by
  have hu := spread4_sound L bits a hcap hbit
  unfold pairBack
  rw [Nat.testBit_and,halfMask_sound r b hb,Bool.and_true]
  simp only [Nat.testBit_or,Nat.testBit_shiftRight]
  rcases four_cases r a b ha hb h with h0|h1|h2|h3
  · rw [h0] at hu; simp [hu]
  · rw [h1] at hu
    rw [Nat.add_comm b r] at hu
    simp [hu]
  · rw [h2] at hu
    rw [show b+(2*r+1)=2*r+1+b by omega] at hu
    simp [hu]
  · rw [h3] at hu
    rw [show b+(3*r+1)=3*r+1+b by omega] at hu
    simp [hu]

/-- At even clock 2r, the center is r-1. It is automatically absent
when odd, and otherwise the compressed position is (r-1)/2. -/
def checkPair (r hi bits : Nat) : Bool :=
  !(decide (2*r-4≤hi ∧ (r-1)%2=0) && bits.testBit ((r-1)/2))

def pairScan (plan : List (Nat × Nat)) (hi r bits : Nat) : Nat → Bool
  | 0 => checkPair r hi bits
  | d+1 => checkPair r hi bits && pairScan plan hi (r-1) (pairBack plan (r-1) bits) d

/-- Begin one clock below an odd final clock 2R+1; its even predecessor
layer is covered by the full scaled strict interior. -/
def pairCheck (L R lo hi : Nat) : Bool :=
  pairScan (spreadPlan L L) hi R (halfMask R) (R-(lo+4)/2)

#print axioms spread4_sound
#print axioms four_cases
#print axioms pairBack_sound
end BB6.Agent9PairCarry
