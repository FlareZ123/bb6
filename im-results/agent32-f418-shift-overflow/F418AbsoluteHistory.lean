import Init

namespace BB6.Agent32F418.AbsoluteHistory

/-- The arithmetic summary of a normal-return prefix. The corrected numerator
    stays in the absolute coordinate system of the initial register. -/
structure History where
  shift : Nat
  width : Nat
  numerator : Int
  deriving Repr

def init (n : Nat) (w : Nat) : History := ⟨0, w, n⟩
def History.value (h : History) : Int := h.numerator / (2 : Int)^h.shift
def History.advance (h : History) (p c : Nat) : History :=
  let s := h.shift + 2*p + 1
  let w := h.width + 5*p + 3
  ⟨s, w, h.numerator + (2 : Int)^(s+w-1) - (c : Int)*(2 : Int)^s⟩

theorem shift_div (n : Int) (s l : Nat) :
    n / (2 : Int)^s / (2 : Int)^l = n / (2 : Int)^(s+l) := by
  rw [Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide)), Int.pow_add]

theorem advance_value (h : History) (p c : Nat) (hw : 0 < h.width) :
    (h.advance p c).value = h.value / (2 : Int)^(2*p+1) +
      (2 : Int)^(h.width+5*p+2) - (c : Int) := by
  unfold History.advance History.value
  dsimp only
  have e : h.shift+2*p+1+(h.width+5*p+3)-1 =
    (h.shift+(2*p+1))+(h.width+5*p+2) := by omega
  rw [e, Int.pow_add]
  have e' : h.shift+2*p+1 = h.shift+(2*p+1) := by omega
  rw [e']
  have hne : (2 : Int)^(h.shift+(2*p+1)) ≠ 0 := Int.pow_ne_zero (by decide)
  have hm : (2 : Int)^(h.shift+(2*p+1)) * (c : Int) =
      (c : Int) * (2 : Int)^(h.shift+(2*p+1)) := Int.mul_comm _ _
  rw [← hm, Int.sub_eq_add_neg, ← Int.mul_neg, Int.add_mul_ediv_left _ _ hne,
      Int.add_mul_ediv_left _ _ hne, ← shift_div]
  omega

end BB6.Agent32F418.AbsoluteHistory

namespace BB6.Agent32F418.AbsoluteHistory

/-- An affine repeat block in integer coordinates. W is encoded by 2^W,
    so both state updates are linear. -/
def defect (M R U K n w : Int) : Int :=
  (M-1)*(R-1)*n - (M-1)*U*w + (R-1)*K

theorem defect_step (M R Q U K n w n' w' : Int)
    (hR : R=M*Q) (hn : M*n'=n+U*w-K) (hw : w'=Q*w) :
    M*defect M R U K n' w' = defect M R U K n w := by
  unfold defect
  grind

theorem vanishing_of_divisible_powers (z : Int) (M : Nat) (hM : 2 ≤ M)
    (h : ∀ k : Nat, ∃ q : Int, z = (M : Int)^k*q) : z=0 := by
  by_cases hz : z = 0
  · exact hz
  exfalso
  let k := z.natAbs + 1
  obtain ⟨q, hq⟩ := h k
  have hqn : q ≠ 0 := by intro he; simp [he] at hq; exact hz hq
  have hqpos : 0 < q.natAbs := by
    by_cases he : q.natAbs = 0
    · exact False.elim (hqn (Int.natAbs_eq_zero.mp he))
    · omega
  have ha : z.natAbs = M^k*q.natAbs := by
    rw [hq, Int.natAbs_mul]
    simp
  have hle : 2^k ≤ M^k := Nat.pow_le_pow_left hM k
  have hgt : z.natAbs < 2^k := by
    have hh := Nat.lt_two_pow_self (n:=k)
    have hk : z.natAbs < k := by dsimp [k]; omega
    exact Nat.lt_trans hk hh
  have hle' := Nat.le_mul_of_pos_right (M^k) hqpos
  omega

theorem periodic_defect_zero (M : Nat) (R Q U K : Int)
    (n w : Nat → Int) (hM : 2 ≤ M) (hR : R=(M:Int)*Q)
    (hn : ∀ i, (M : Int)*n (i+1)=n i+U*w i-K)
    (hw : ∀ i, w (i+1)=Q*w i) : defect M R U K (n 0) (w 0)=0 := by
  apply vanishing_of_divisible_powers _ M hM
  intro k
  refine ⟨defect M R U K (n k) (w k), ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, Int.pow_succ, Int.mul_assoc,
      defect_step (M:Int) R Q U K (n k) (w k) (n (k+1)) (w (k+1)) hR (hn k) (hw k)]

#print axioms advance_value
#print axioms periodic_defect_zero

end BB6.Agent32F418.AbsoluteHistory

namespace BB6.Agent32F418.AbsoluteHistory

/-- A certified normal-return word summarized by its consumed bits, width
    growth, positive pulse coefficient, and total low-word/correction debit. -/
structure Block where
  l : Nat
  d : Nat
  u : Int
  k : Int
  deriving Repr

def Block.one (p c b : Nat) : Block :=
  ⟨2*p+1, 5*p+3, (2:Int)^(7*p+3), (b:Int)+(c:Int)*(2:Int)^(2*p+1)⟩

def Block.empty : Block := ⟨0,0,0,0⟩

def Block.append (a b : Block) : Block :=
  ⟨a.l+b.l,a.d+b.d,a.u+(2:Int)^(a.l+a.d)*b.u,a.k+(2:Int)^a.l*b.k⟩

def Block.rel (a : Block) (n w n' w' : Int) : Prop :=
  (2:Int)^a.l*n'=n+a.u*w-a.k ∧ w'=(2:Int)^a.d*w

theorem Block.rel_empty (n w : Int) : Block.empty.rel n w n w := by
  simp [Block.empty,Block.rel]

theorem Block.rel_append {a b : Block} {n w n' w' n'' w'' : Int}
    (ha : a.rel n w n' w') (hb : b.rel n' w' n'' w'') :
    (a.append b).rel n w n'' w'' := by
  rcases ha with ⟨ha,haw⟩
  rcases hb with ⟨hb,hbw⟩
  unfold Block.rel Block.append
  dsimp only
  rw [Int.pow_add,Int.pow_add,Int.pow_add]
  constructor <;> grind

theorem Block.rel_one (p c b : Nat) (n w q : Int)
    (h : n=(2:Int)^(2*p+1)*q+(b:Int)) :
    (Block.one p c b).rel n w
      ((2:Int)^(5*p+2)*w+q-(c:Int)) ((2:Int)^(5*p+3)*w) := by
  unfold Block.rel Block.one
  dsimp only
  have he : (2:Int)^(7*p+3)=(2:Int)^(2*p+1)*(2:Int)^(5*p+2) := by
    rw [←Int.pow_add]
    congr 1
    omega
  constructor
  · rw [he]
    grind
  · rfl

theorem Block.periodic_required (a : Block) (hl : 0<a.l)
    (n w : Nat → Int) (h : ∀ i, a.rel (n i) (w i) (n (i+1)) (w (i+1))) :
    defect ((2:Int)^a.l) ((2:Int)^(a.l+a.d)) a.u a.k (n 0) (w 0) = 0 := by
  have hm : 2 ≤ 2^a.l := by
    have hh := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤a.l by omega)
    simpa using hh
  have hr : (2:Int)^(a.l+a.d) = ((2^a.l:Nat):Int)*(2:Int)^a.d := by
    simp [Int.natCast_pow,Int.pow_add]
  have hn : ∀ i, ((2^a.l:Nat):Int)*n (i+1)=n i+a.u*w i-a.k := by
    intro i
    simpa [Int.natCast_pow] using (h i).1
  have hw : ∀ i, w (i+1)=(2:Int)^a.d*w i := fun i => (h i).2
  simpa [Int.natCast_pow] using periodic_defect_zero (2^a.l)
    ((2:Int)^(a.l+a.d)) ((2:Int)^a.d) a.u a.k n w hm hr hn hw

#print axioms Block.rel_append
#print axioms Block.rel_one
#print axioms Block.periodic_required

end BB6.Agent32F418.AbsoluteHistory

namespace BB6.Agent32F418.AbsoluteHistory

theorem odd_cancel_two {d a : Int} (hd : d % 2 = 1) (h : d ∣ a*2) : d ∣ a := by
  obtain ⟨q,hq⟩ := h
  have hp : q % 2 = 0 := by
    have hh := congrArg (fun t : Int => t % 2) hq
    rw [Int.mul_emod a 2 2, Int.mul_emod d q 2, hd] at hh
    simpa using hh.symm
  refine ⟨q/2, ?_⟩
  have he : q=2*(q/2) := by omega
  rw [he] at hq
  grind

theorem odd_cancel_power {d a : Int} (hd : d % 2=1) (j : Nat)
    (h : d ∣ a*(2:Int)^j) : d ∣ a := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Int.pow_succ,←Int.mul_assoc] at h
    exact ih (odd_cancel_two hd h)

theorem two_pow_sub_one_odd {h : Nat} (hh : 0<h) : ((2:Int)^h-1)%2=1 := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
  rw [Int.pow_succ, Int.sub_emod, Int.mul_emod]
  simp

/-- No fixed complete prefix can recur forever, at any initial register and
    width. This quantifies over every p and every correction and low word. -/
theorem no_constant_prefix (p c b W : Nat) (n w : Nat → Int)
    (hw : w 0=(2:Int)^W)
    (h : ∀ i, (Block.one p c b).rel (n i) (w i) (n (i+1)) (w (i+1))) : False := by
  let l := 2*p+1
  let g := 7*p+4
  let M : Int := (2:Int)^l
  let R : Int := (2:Int)^g
  let K : Int := (b:Int)+(c:Int)*(2:Int)^l
  have hL : 0<l := by dsimp [l]; omega
  have hG : l<g := by dsimp [l,g]; omega
  have hdef := Block.periodic_required (Block.one p c b) (by simp [Block.one]) n w h
  change defect M ((2:Int)^(2*p+1+(5*p+3))) ((2:Int)^(7*p+3)) K (n 0) (w 0)=0 at hdef
  rw [show 2*p+1+(5*p+3)=g by dsimp [g]; omega, hw] at hdef
  change defect M R ((2:Int)^(7*p+3)) K (n 0) ((2:Int)^W)=0 at hdef
  unfold defect at hdef
  have hd : R-1 ∣ (M-1)*(2:Int)^(7*p+3+W) := by
    refine ⟨(M-1)*n 0+K, ?_⟩
    rw [Int.pow_add]
    grind
  have ho : (R-1)%2=1 := two_pow_sub_one_odd (by omega : 0<g)
  have hdiv := odd_cancel_power ho _ hd
  have hm : 1<M := by
    have hh : 1 < 2^l := by
      simp only [← Nat.pow_zero 2]; exact Nat.pow_lt_pow_right (a:=2) (by decide) hL
    exact Int.ofNat_lt.mpr hh
  have hmr : M<R := by
    have hh : 2^l < 2^g := Nat.pow_lt_pow_right (by decide) hG
    exact Int.ofNat_lt.mpr hh
  have hle := Int.le_of_dvd (by omega : 0<M-1) hdiv
  omega

#print axioms no_constant_prefix

end BB6.Agent32F418.AbsoluteHistory
