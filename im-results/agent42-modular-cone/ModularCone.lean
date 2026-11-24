import Lean

namespace BB6.Agent42ModularCone

/-- A source-independent modular exclusion kernel. The machine-specific
    adapter supplies the complete inverse equations and the forbidden image. -/
def P (b : Nat) : Nat := 2^b
def I (b : Nat) : Int := (P b : Int)

theorem P_pos (b : Nat) : 0 < P b := Nat.pow_pos (by decide)
theorem I_pos (b : Nat) : 0 < I b := by
  have := P_pos b
  unfold I
  omega

theorem P_split {b d : Nat} (h : d ≤ b) : P b = P (b-d) * P d := by
  exact (Nat.pow_sub_mul_pow 2 h).symm

theorem I_split {b d : Nat} (h : d ≤ b) : I b = I (b-d) * I d := by
  unfold I
  rw [P_split h, Int.natCast_mul]

def Cong (b : Nat) (x r : Int) : Prop := I b ∣ x-r

theorem cong_weaken {b c : Nat} {x r : Int} (hcb : c ≤ b) (h : Cong b x r) : Cong c x r := by
  unfold Cong at *
  rw [I_split hcb] at h
  exact Int.dvd_trans (Int.dvd_mul_left _ _) h

theorem cong_add {b : Nat} {x y r s : Int} (hx : Cong b x r) (hy : Cong b y s) : Cong b (x+y) (r+s) := by
  unfold Cong at *
  rw [show x+y-(r+s)=x-r+(y-s) by omega]
  exact Int.dvd_add hx hy

theorem cong_sub {b : Nat} {x y r s : Int} (hx : Cong b x r) (hy : Cong b y s) : Cong b (x-y) (r-s) := by
  unfold Cong at *
  rw [show x-y-(r-s)=x-r-(y-s) by omega]
  exact Int.dvd_sub hx hy

theorem cong_refl (b : Nat) (x : Int) : Cong b x x := by
  simp [Cong]

theorem cong_mul_const {b : Nat} {x r : Int} (h : Cong b x r) (c : Int) : Cong b (c*x) (c*r) := by
  unfold Cong at *
  rw [← Int.mul_sub]
  exact Int.dvd_trans h (Int.dvd_mul_left _ _)

theorem cong_cancel {b d : Nat} {x r : Int} (hdb : d ≤ b)
    (h : Cong b (I d*x) (I d*r)) : Cong (b-d) x r := by
  unfold Cong at *
  rw [I_split hdb, Int.mul_comm (I (b-d)), ← Int.mul_sub] at h
  exact Int.dvd_of_mul_dvd_mul_left (by have := I_pos d; omega) h

theorem cong_mod {b : Nat} {x r : Int} (h : Cong b x r) : x % I b = r % I b :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)

theorem mod_cong {b : Nat} {x r : Int} (h : x % I b = r % I b) : Cong b x r :=
  Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)

theorem cong_nat_mod {b x : Nat} {r : Int} (h : Cong b (x:Int) r) : ((x % P b : Nat):Int) = r % I b := by
  rw [Int.natCast_emod]
  exact cong_mod h

/-- The right-coordinate lower bound is propagated along every inverse
    edge, independently of the signs or magnitudes of the representatives. -/
def Large (b y : Nat) : Prop := 3 * P b ≤ y+2

theorem large_direct {b y k : Nat} (hb : 1 ≤ b) (hl : Large b y) (he : 2*k+2=y) : Large (b-1) k := by
  unfold Large at *
  rw [P_split hb] at hl
  change 3*(P (b-1)*2) ≤ y+2 at hl
  omega

private theorem exp_linear (n : Nat) : 3*n+4 ≤ P (n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : P (n+1+2) = P (n+2)*2 := by
      unfold P
      rw [show n+1+2=n+2+1 by omega, Nat.pow_succ]
    rw [h]
    omega

theorem large_high {b n a k x y : Nat} (hb : n+2 ≤ b) (hl : Large b y)
    (hq : x+y+(x+y)%2=P (n+1)*(a+2+(x+y)%2))
    (hw : 2*k+a+7+3*n=x+2*y) : Large (b-(n+2)) k := by
  have hd : 2 ≤ P (n+1) := Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : 1 ≤ n+1)
  have hp : P (n+2) = P (n+1)*2 := by simp [P, Nat.pow_succ]
  have hm := Nat.mul_le_mul_right a hd
  have ho := Nat.mul_le_mul_right ((x+y)%2) hd
  rw [Nat.mul_add, Nat.mul_add] at hq
  have hh := exp_linear n
  have hxy : a + P (n+2) ≤ x+y := by omega
  have hk : y+1 ≤ 2*(k+2) := by omega
  have h0 : 2 ≤ P (n+2) := by omega
  have h1 := Nat.mul_le_mul_right (k+2) h0
  have h2 : 4 ≤ P (n+2) := by omega
  have h3 := Nat.mul_le_mul_right (k+2) h2
  have hs : y+2 ≤ P (n+2)*(k+2) := by omega
  unfold Large at *
  rw [P_split hb] at hl
  apply Nat.le_of_mul_le_mul_left (c := P (n+2)) _ (P_pos _)
  rw [Nat.mul_comm (P (n+2)) (3*P (b-(n+2))), Nat.mul_assoc]
  exact Nat.le_trans hl hs


structure Pair where
  x : Int
  y : Int
  deriving Repr, DecidableEq, BEq

def residue (b : Nat) (s : Pair) : Pair := ⟨s.x % I b, s.y % I b⟩
def Matches (b x y : Nat) (s : Pair) : Prop := Cong b (x:Int) s.x ∧ Cong b (y:Int) s.y

theorem matches_residue {b x y : Nat} {s : Pair} (h : Matches b x y s) : Matches b x y (residue b s) := by
  constructor <;> apply mod_cong
  · simpa [residue] using cong_mod h.1
  · simpa [residue] using cong_mod h.2

theorem nat_mod_eq {b x : Nat} {r : Int} (h : Cong b (x:Int) r) : ((x%P b:Nat):Int) = r%I b := cong_nat_mod h

def odd (s : Pair) : Int := (s.x+s.y)%2
def q (s : Pair) : Int := s.x+s.y+odd s
def w (s : Pair) : Int := s.x+2*s.y

theorem odd_matches {b x y : Nat} {s : Pair} (hb : 1≤b) (h : Matches b x y s) : ((x+y)%2:Nat) = (odd s) := by
  have h' := cong_nat_mod (cong_weaken hb (cong_add h.1 h.2))
  exact h'

theorem q_matches {b x y : Nat} {s : Pair} (hb : 1≤b) (h : Matches b x y s) : Cong b ((x+y+(x+y)%2:Nat):Int) (q s) := by
  have ho := odd_matches hb h
  simp only [Int.natCast_add]
  unfold q
  rw [←ho]
  exact cong_add (cong_add h.1 h.2) (cong_refl _ _)

theorem w_matches {b x y : Nat} {s : Pair} (h : Matches b x y s) : Cong b ((x+2*y:Nat):Int) (w s) := by
  simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int]
  exact cong_add h.1 (cong_mul_const h.2 2)

def direct (s : Pair) : Pair := ⟨s.x+s.y-2,(s.y-2)/2⟩
def high (s : Pair) (n : Nat) : Pair :=
  let a := q s / I (n+1) - 2 - odd s
  ⟨a,(w s-a-7-3*(n:Int))/2⟩

theorem direct_matches {b x y a k : Nat} {s : Pair} (hb : 1≤b) (hm : Matches b x y s)
    (ha : a+2=x+y) (hk : 2*k+2=y) (he : s.y%2=0) : Matches (b-1) a k (direct s) := by
  have h1 := cong_sub (cong_add hm.1 hm.2) (cong_refl b 2)
  have h2 := cong_sub hm.2 (cong_refl b 2)
  have ha' : (a:Int) = (x:Int)+(y:Int)-2 := by omega
  have hk' : I 1*(k:Int)=(y:Int)-2 := by change 2*(k:Int)=(y:Int)-2; omega
  have hkr : I 1*(direct s).y=s.y-2 := by
    change 2*((s.y-2)/2)=s.y-2
    omega
  constructor
  · rw [←ha'] at h1
    exact cong_weaken (by omega) h1
  · rw [←hk',←hkr] at h2
    exact cong_cancel hb h2

def HighValid (s : Pair) (n : Nat) : Prop :=
  q s = I (n+1)*((high s n).x+2+odd s) ∧
  2*(high s n).y+(high s n).x+7+3*(n:Int)=w s
instance (s : Pair) (n : Nat) : Decidable (HighValid s n) := inferInstanceAs (Decidable (_ ∧ _))

theorem high_matches {b n a k x y : Nat} {s : Pair} (hb : n+2≤b) (hm : Matches b x y s)
    (hq : x+y+(x+y)%2=P (n+1)*(a+2+(x+y)%2))
    (hw : 2*k+a+7+3*n=x+2*y) (hv : HighValid s n) : Matches (b-(n+2)) a k (high s n) := by
  let c := b-(n+1)
  have ho := odd_matches (by omega : 1≤b) hm
  have hqc := q_matches (by omega : 1≤b) hm
  have hq' : ((x+y+(x+y)%2:Nat):Int)=I (n+1)*((a:Int)+2+odd s) := by
    rw [hq]
    simp only [Int.natCast_mul, Int.natCast_add, Int.cast_ofNat_Int, I, ho]
  rw [hq',hv.1] at hqc
  have hac := cong_cancel (by omega : n+1≤b) hqc
  have ha := cong_sub hac (cong_refl c (odd s))
  have ha := cong_sub ha (cong_refl c 2)
  have ha' : Cong c (a:Int) (high s n).x := by
    simpa only [Int.add_sub_cancel, Int.add_sub_cancel] using ha
  have hwc := cong_weaken (by omega : c≤b) (w_matches hm)
  have hw' : ((x+2*y:Nat):Int)=2*(k:Int)+(a:Int)+7+3*(n:Int) := by omega
  rw [hw',←hv.2] at hwc
  have hk := cong_sub (cong_sub (cong_sub hwc (cong_refl c (3*(n:Int)))) (cong_refl c 7)) ha'
  have hk' : Cong c (I 1*(k:Int)) (I 1*(high s n).y) := by
    change Cong c (2*(k:Int)) (2*(high s n).y)
    simpa only [Int.add_sub_cancel] using hk
  have hk'' := cong_cancel (by omega : 1≤c) hk'
  have hc : c-1=b-(n+2) := by omega
  rw [hc] at hk''
  exact ⟨cong_weaken (by omega) ha',hk''⟩


/-- The complete source inverse interface, valid on the large-right region. -/
def Inverse (a k x y v : Nat) : Prop :=
  (y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
  ∃ n, n+2≤v ∧ n%2=(x+1+(x+y)%2)%2 ∧
    x+y+(x+y)%2=P (n+1)*(a+2+(x+y)%2) ∧
    2*k+a+7+3*n=x+2*y

def ParentLaw (reach : Nat → Nat → Prop) : Prop :=
  ∀ x y v, reach x y → 8≤y → (x+y+(x+y)%2)%P (v+1)=P v →
    P v < x+y+(x+y)%2 → ∃ a k, reach a k ∧ Inverse a k x y v

def ForbiddenLaw (reach : Nat → Nat → Prop) : Prop :=
  ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y

def Bad (s : Pair) : Prop := s.y%2=1 ∧ ((s.x+s.y)%4=1 ∨ (s.x+s.y)%4=2)
instance (s : Pair) : Decidable (Bad s) := inferInstanceAs (Decidable (_ ∧ _))

def valuation : Nat → Int → Nat
  | 0, _ => 0
  | f+1, z => if z%2=0 then 1+valuation f (z/2) else 0

def ValValid (b : Nat) (s : Pair) (v : Nat) : Prop := v+1≤b ∧ q s%I (v+1)=I v
instance (b : Nat) (s : Pair) (v : Nat) : Decidable (ValValid b s v) := inferInstanceAs (Decidable (_ ∧ _))

def Allowed (s : Pair) (v n : Nat) : Prop := n+2≤v ∧ (n:Int)%2=(s.x+1+odd s)%2
instance (s : Pair) (v n : Nat) : Decidable (Allowed s v n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The finite precision b is a resource; each inverse edge consumes bits.
    No raw-machine simulation or enumeration of actual counter magnitudes occurs. -/
def check : Nat → Nat → Pair → Bool
  | 0, b, s => decide (2≤b ∧ Bad s)
  | f+1, b, s =>
    if 2≤b then
      if Bad s then true else
        let v := valuation b (q s)
        if ValValid b s v then
          (if s.y%2=0 then check f (b-1) (residue (b-1) (direct s)) else true) &&
          (List.range (v+1)).all (fun n =>
            if Allowed s v n then
              decide (HighValid s n) && check f (b-(n+2)) (residue (b-(n+2)) (high s n))
            else true)
        else false
    else false

def excluded (b : Nat) (s : Pair) : Bool := check b b (residue b s)

theorem large_y {b y : Nat} (hb : 2≤b) (hl : Large b y) : 8≤y := by
  have h := Nat.pow_le_pow_right (by decide : 2>0) hb
  change 4≤P b at h
  unfold Large at hl
  omega

theorem bad_sound {reach : Nat → Nat → Prop} (hf : ForbiddenLaw reach) {b x y : Nat} {s : Pair}
    (hb : 2≤b) (hl : Large b y) (hm : Matches b x y s) (hs : Bad s) : ¬reach x y := by
  have hy := cong_nat_mod (cong_weaken (by omega : 1≤b) hm.2)
  have hxy := cong_nat_mod (cong_weaken hb (cong_add hm.1 hm.2))
  change ((y%2:Nat):Int)=s.y%2 at hy
  change ((((x+y)%4:Nat)):Int)=(s.x+s.y)%4 at hxy
  unfold Bad at hs
  exact hf x y (by have := large_y hb hl; omega) (by omega) (by omega)

theorem actual_val {b x y v : Nat} {s : Pair} (hb : 2≤b) (hl : Large b y)
    (hm : Matches b x y s) (hv : ValValid b s v) :
    (x+y+(x+y)%2)%P (v+1)=P v ∧ P v < x+y+(x+y)%2 := by
  have hq := cong_nat_mod (cong_weaken hv.1 (q_matches (by omega : 1≤b) hm))
  rw [hv.2] at hq
  constructor
  · exact Int.ofNat_inj.mp hq
  · have hvb := hv.1
    have hp : P v ≤ P b := Nat.pow_le_pow_right (by decide : 2>0) (by omega : v≤b)
    have hp0 := P_pos b
    unfold Large at hl
    have hp4 := Nat.pow_le_pow_right (by decide : 2>0) hb
    change 4≤P b at hp4
    omega

theorem allowed_actual {b x y n v : Nat} {s : Pair} (hb : 2≤b) (hm : Matches b x y s)
    (hn : n+2≤v) (hp : n%2=(x+1+(x+y)%2)%2) : Allowed s v n := by
  refine ⟨hn,?_⟩
  have ho := odd_matches (by omega : 1≤b) hm
  have hx := cong_nat_mod (cong_weaken (by omega : 1≤b) hm.1)
  change ((x%2:Nat):Int)=s.x%2 at hx
  omega

theorem check_sound (reach : Nat → Nat → Prop) (hp : ParentLaw reach) (hf : ForbiddenLaw reach)
    (f b : Nat) (s : Pair) (hc : check f b s=true) (x y : Nat)
    (hl : Large b y) (hm : Matches b x y s) : ¬reach x y := by
  induction f generalizing b s x y with
  | zero =>
    simp only [check,decide_eq_true_eq] at hc
    exact bad_sound hf hc.1 hl hm hc.2
  | succ f ih =>
    by_cases hb : 2≤b
    · by_cases hbad : Bad s
      · exact bad_sound hf hb hl hm hbad
      · let v := valuation b (q s)
        have hv : ValValid b s v := by
          by_cases h : ValValid b s v
          · exact h
          · have h' : ¬ ValValid b s (valuation b (q s)) := h
            simp [check,hb,hbad,h'] at hc
        have hh :
          (if s.y%2=0 then check f (b-1) (residue (b-1) (direct s)) else true) = true ∧
          (List.range (v+1)).all (fun n => if Allowed s v n then
            decide (HighValid s n) && check f (b-(n+2)) (residue (b-(n+2)) (high s n)) else true) = true := by
          simpa only [check,hb,ite_true,hbad,ite_false,show valuation b (q s)=v by rfl,hv,Bool.and_eq_true] using hc
        intro hr
        have hval := actual_val hb hl hm hv
        obtain ⟨a,k,hrp,he⟩ := hp x y v hr (large_y hb hl) hval.1 hval.2
        rcases he with ⟨he,ha,hk⟩ | ⟨n,hn,hpar,hq,hw⟩
        · have hye : s.y%2=0 := by
            have hh := cong_nat_mod (cong_weaken (by omega : 1≤b) hm.2)
            change ((y%2:Nat):Int)=s.y%2 at hh
            omega
          have hchild := hh.1
          simp only [hye,ite_true] at hchild
          exact ih _ _ hchild a k (large_direct (by omega) hl hk)
            (matches_residue (direct_matches (by omega) hm ha hk hye)) hrp
        · have hallowed := allowed_actual hb hm hn hpar
          have hn' : n ∈ List.range (v+1) := List.mem_range.mpr (by omega)
          have hchild := List.all_eq_true.mp hh.2 n hn'
          simp only [hallowed,ite_true,Bool.and_eq_true,decide_eq_true_eq] at hchild
          have hn'' : n+2≤b := by have := hv.1; omega
          exact ih _ _ hchild.2 a k (large_high hn'' hl hq hw)
            (matches_residue (high_matches hn'' hm hq hw hchild.1)) hrp
    · simp [check,hb] at hc

theorem excluded_sound (reach : Nat → Nat → Prop) (hp : ParentLaw reach) (hf : ForbiddenLaw reach)
    (b : Nat) (s : Pair) (hc : excluded b s=true) (x y : Nat)
    (hl : Large b y) (hm : Matches b x y s) : ¬reach x y :=
  check_sound reach hp hf b b (residue b s) hc x y hl (matches_residue hm)


/-- The low and high stopping targets share this parametrization:
    j=0 is the low family, j>=1 is the high family with index j-1. -/
def stopResidue (j m : Nat) : Pair := ⟨2*(j:Int)+1,-((j:Int)+3*(m:Int)+4)⟩

private theorem stop_power_bound (m : Nat) : 3*m+2 ≤ P (2*m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : P (2*(m+1)+1)=4*P (2*m+1) := by
      unfold P
      rw [show 2*(m+1)+1=2*m+1+2 by omega,Nat.pow_add]
      change 2^(2*m+1)*4=4*2^(2*m+1)
      omega
    rw [h]
    omega

theorem stop_size (j m y : Nat) (he : y+j+3*m+4=P (2*m+2)*(j+2)) : Large (2*m+1) y := by
  have hpow : P (2*m+2)=2*P (2*m+1) := by
    unfold P
    rw [show 2*m+2=2*m+1+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have hbound := stop_power_bound m
  have hp := P_pos (2*m+1)
  have hm := Nat.mul_le_mul_right j (show 1≤P (2*m+2) from P_pos _)
  rw [Nat.mul_add,hpow] at he
  rw [hpow] at hm
  unfold Large
  omega

theorem large_weaken {b c y : Nat} (hcb : c≤b) (h : Large b y) : Large c y := by
  have hp : P c≤P b := Nat.pow_le_pow_right (by decide : 2>0) hcb
  unfold Large at *
  omega

theorem stop_matches (b j m y : Nat) (hb : b≤2*m+2)
    (he : y+j+3*m+4=P (2*m+2)*(j+2)) : Matches b (2*j+1) y (stopResidue j m) := by
  constructor
  · simp [stopResidue,Cong]
  · unfold Cong stopResidue
    simp only
    have h : (y:Int)-(-((j:Int)+3*(m:Int)+4))=I (2*m+2)*((j:Int)+2) := by
      have he' := congrArg (fun z : Nat => (z:Int)) he
      simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at he'
      unfold I
      omega
    rw [h,I_split hb]
    exact Int.dvd_trans (Int.dvd_mul_left _ _) (Int.dvd_mul_right _ _)

/-- Every accepted residue represents a full, unbounded two-parameter
    stopping cylinder. This imposes no upper bound on j relative to m. -/
theorem stop_excluded (reach : Nat → Nat → Prop) (hp : ParentLaw reach) (hf : ForbiddenLaw reach)
    (b j m y : Nat) (hb : b≤2*m+1)
    (he : y+j+3*m+4=P (2*m+2)*(j+2))
    (hc : excluded b (stopResidue j m)=true) : ¬reach (2*j+1) y :=
  excluded_sound reach hp hf b (stopResidue j m) hc (2*j+1) y
    (large_weaken hb (stop_size j m y he)) (stop_matches b j m y (by omega) he)

theorem cong_trans {b : Nat} {x y z : Int} (hxy : Cong b x y) (hyz : Cong b y z) : Cong b x z := by
  unfold Cong at *
  rw [show x-z=x-y+(y-z) by omega]
  exact Int.dvd_add hxy hyz

theorem stop_cylinder_matches (b j0 m0 j m y : Nat) (hb : b≤2*m+2)
    (hj : Cong b (j:Int) j0) (hm : Cong b (m:Int) m0)
    (he : y+j+3*m+4=P (2*m+2)*(j+2)) : Matches b (2*j+1) y (stopResidue j0 m0) := by
  have h := stop_matches b j m y hb he
  have hx := cong_add (cong_mul_const hj 2) (cong_refl b 1)
  have hy := cong_sub (cong_refl b 0) (cong_add (cong_add hj (cong_mul_const hm 3)) (cong_refl b 4))
  refine ⟨cong_trans h.1 hx,?_⟩
  exact cong_trans h.2 (by simpa [stopResidue] using hy)

/-- For j>=2, the stopping equation supplies one additional precision bit. -/
theorem stop_size_high (j m y : Nat) (hj : 2≤j)
    (he : y+j+3*m+4=P (2*m+2)*(j+2)) : Large (2*m+2) y := by
  have hpow : P (2*m+2)=2*P (2*m+1) := by
    unfold P
    rw [show 2*m+2=2*m+1+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have hb := stop_power_bound m
  have hp : 3*m+4≤P (2*m+2) := by omega
  have hj' : j=2+(j-2) := by omega
  have he' : P (2*m+2)*(j+2)=P (2*m+2)*4+P (2*m+2)*(j-2) := by
    rw [←Nat.mul_add]
    congr 1
    omega
  have hm := Nat.mul_le_mul_right (j-2) (show 1≤P (2*m+2) from P_pos _)
  rw [he'] at he
  unfold Large
  omega

theorem stop_cylinder_excluded (reach : Nat → Nat → Prop) (hp : ParentLaw reach) (hf : ForbiddenLaw reach)
    (b j0 m0 j m y : Nat) (hb : b≤2*m+1 ∨ (2≤j ∧ b≤2*m+2))
    (hj : Cong b (j:Int) j0) (hm : Cong b (m:Int) m0)
    (he : y+j+3*m+4=P (2*m+2)*(j+2))
    (hc : excluded b (stopResidue j0 m0)=true) : ¬reach (2*j+1) y := by
  have hsize : Large b y := by
    rcases hb with h | ⟨hj,hb⟩
    · exact large_weaken h (stop_size j m y he)
    · exact large_weaken hb (stop_size_high j m y hj he)
  have hb' : b≤2*m+2 := by rcases hb with h|h <;> omega
  exact excluded_sound reach hp hf b (stopResidue j0 m0) hc (2*j+1) y hsize
    (stop_cylinder_matches b j0 m0 j m y hb' hj hm he)

/-- Explicit certificate outside the previous small-negative-shadow domain. -/
theorem example_certificate : excluded 5 (stopResidue 10 2)=true := by decide

theorem example_family (reach : Nat → Nat → Prop) (hp : ParentLaw reach) (hf : ForbiddenLaw reach)
    (u v y : Nat)
    (he : y+(10+32*u)+3*(2+32*v)+4=P (2*(2+32*v)+2)*((10+32*u)+2)) :
    ¬reach (2*(10+32*u)+1) y := by
  apply stop_cylinder_excluded reach hp hf 5 10 2 (10+32*u) (2+32*v) y
  · left; omega
  · unfold Cong I P
    refine ⟨(u:Int),?_⟩
    simp <;> omega
  · unfold Cong I P
    refine ⟨(v:Int),?_⟩
    simp <;> omega
  · exact he
  · exact example_certificate

end BB6.Agent42ModularCone
#print axioms BB6.Agent42ModularCone.excluded_sound
#print axioms BB6.Agent42ModularCone.stop_excluded
#print axioms BB6.Agent42ModularCone.stop_cylinder_excluded
#print axioms BB6.Agent42ModularCone.example_family
