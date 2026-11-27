import Lean

namespace BB429.CoarseExit

def lead (r a : Int) (e : Nat → Bool) : Nat → Int
  | 0 => a
  | i+1 => 4*lead r a e i - (if e i then 2*r else 0)

def cap (B : Int) : Nat → Int
  | 0 => B
  | i+1 => 5*cap B i

theorem cap_ge (B : Int) (h : 0 ≤ B) (i : Nat) : B ≤ cap B i := by
  induction i with
  | zero => exact Int.le_refl _
  | succ i ih => simp only [cap]; omega

theorem cap_mono (B : Int) (h : 0 ≤ B) (i j : Nat) (hij : i ≤ j) : cap B i ≤ cap B j := by
  induction j with
  | zero =>
    have : i=0 := by omega
    subst i
    exact Int.le_refl _
  | succ j ih =>
    by_cases he : i=j+1
    · subst i; exact Int.le_refl _
    · have hh := ih (by omega)
      have hg := cap_ge B h j
      simp only [cap]; omega

def Blocks (U V : Nat → Int) (e : Nat → Bool) (n : Nat) : Prop :=
  ∀ i, i<n → ∃ c δ : Int, 0≤c ∧ c≤54 ∧ 0≤δ ∧ δ≤42 ∧
    U (i+1)=4*U i-(if e i then 2*V i else 0)+c ∧ V (i+1)=V i+δ

def Physical (U V : Nat → Int) (n : Nat) : Prop :=
  ∀ i, i≤n → 18≤U i ∧ U i≤V i+18

def budget (x y : Int) (L : Nat) : Int := x+2*y+84*L+54

theorem errors (P r a x y : Int) (L n : Nat) (U V : Nat → Int) (e : Nat → Bool)
    (hx : 0≤x) (hy : 0≤y) (hn : n≤L)
    (hU : U 0=a*P+x) (hV : V 0=r*P+y) (hs : Blocks U V e n) :
    ∀ i, i≤n →
      -cap (budget x y L) i ≤ U i-lead r a e i*P ∧
      U i-lead r a e i*P ≤ cap (budget x y L) i ∧
      0≤V i-r*P ∧ V i-r*P≤y+42*i := by
  intro i hi
  induction i with
  | zero => simp only [lead,cap,hU,hV,budget,Int.natCast_zero,Int.mul_zero]; omega
  | succ i ih =>
    have hprev := ih (by omega)
    obtain ⟨c,δ,hc0,hc1,hd0,hd1,hu,hv⟩ := hs i (by omega)
    have hb : 0≤budget x y L := by unfold budget; omega
    have hg := cap_ge (budget x y L) hb i
    have hcast : (i:Int)≤L := by omega
    change x+2*y+84*L+54≤cap (budget x y L) i at hg
    simp only [lead,cap,hu,hv,Int.natCast_succ]
    cases he : e i <;> simp [he,Int.sub_mul,Int.mul_assoc] at * <;> omega

theorem leading_bounds (P r a x y : Int) (L n : Nat) (U V : Nat → Int) (e : Nat → Bool)
    (hx : 0≤x) (hy : 0≤y) (hn : n≤L)
    (hU : U 0=a*P+x) (hV : V 0=r*P+y) (hs : Blocks U V e n)
    (hp : Physical U V n) (hsep : 3*cap (budget x y L) L+39<P) :
    ∀ i, i≤n → 0≤lead r a e i ∧ lead r a e i≤r := by
  intro i hi
  have he := errors P r a x y L n U V e hx hy hn hU hV hs i hi
  have hb : 0≤budget x y L := by unfold budget; omega
  have hm := cap_mono (budget x y L) hb i L (by omega)
  have hg := cap_ge (budget x y L) hb L
  have hP : 0≤P := by omega
  have hphys := hp i hi
  have hη : V i-r*P≤cap (budget x y L) L := by
    change x+2*y+84*L+54≤cap (budget x y L) L at hg
    omega
  constructor
  · by_cases hneg : 0≤lead r a e i
    · exact hneg
    · exfalso
      have hmul := Int.mul_le_mul_of_nonneg_right (show lead r a e i≤-1 by omega) hP
      simp at hmul
      omega
  · by_cases hbig : lead r a e i≤r
    · exact hbig
    · exfalso
      have hmul := Int.mul_le_mul_of_nonneg_right (show r+1≤lead r a e i by omega) hP
      simp only [Int.add_mul,Int.one_mul] at hmul
      omega

theorem leading_halt (P r a x y : Int) (L n : Nat) (U V : Nat → Int) (e : Nat → Bool)
    (hx : 0≤x) (hy : 0≤y) (hn : n≤L)
    (hU : U 0=a*P+x) (hV : V 0=r*P+y) (hs : Blocks U V e n)
    (hsep : 3*cap (budget x y L) L+39<P)
    (hh : 2*U n=V n+39) : 2*lead r a e n=r := by
  have he := errors P r a x y L n U V e hx hy hn hU hV hs n (by omega)
  have hb : 0≤budget x y L := by unfold budget; omega
  have hm := cap_mono (budget x y L) hb n L hn
  have hg := cap_ge (budget x y L) hb L
  have hP : 0≤P := by omega
  have hη : V n-r*P≤cap (budget x y L) L := by
    change x+2*y+84*L+54≤cap (budget x y L) L at hg
    omega
  by_cases heq : 2*lead r a e n=r
  · exact heq
  · exfalso
    rcases (show 2*lead r a e n+1≤r ∨ r+1≤2*lead r a e n by omega) with h|h
    · have hmul := Int.mul_le_mul_of_nonneg_right h hP
      simp only [Int.add_mul,Int.mul_assoc,Int.one_mul] at hmul
      omega
    · have hmul := Int.mul_le_mul_of_nonneg_right h hP
      simp only [Int.add_mul,Int.mul_assoc,Int.one_mul] at hmul
      omega

theorem lead_mod27 (r a : Int) (e : Nat → Bool) (hr : r%27=0) (ha : a%27≠0) (i : Nat) : lead r a e i%27≠0 := by
  induction i with
  | zero => exact ha
  | succ i ih =>
    simp only [lead]
    cases e i <;> simp <;> omega

theorem lead_form (r a : Int) (e : Nat → Bool) (i : Nat) : ∃ q : Int, lead r a e i=4^i*a+r*q := by
  induction i with
  | zero => exact ⟨0,by simp [lead]⟩
  | succ i ih =>
    obtain ⟨q,hq⟩ := ih
    simp only [lead,hq,Int.pow_succ]
    cases h : e i
    · refine ⟨4*q,?_⟩
      simp [h,Int.mul_add,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    · refine ⟨4*q-2,?_⟩
      simp only [h,if_true,Int.mul_add,Int.mul_sub,Int.mul_assoc]
      rw [Int.mul_left_comm 4 (4^i) a,Int.mul_left_comm 4 r q,Int.mul_comm 2 r]
      omega

theorem four_edges (z0 z1 z2 z3 z4 : Int)
    (h0 : 0≤z0 ∧ z0≤27) (h1 : 0≤z1 ∧ z1≤27) (h2 : 0≤z2 ∧ z2≤27)
    (h3 : 0≤z3 ∧ z3≤27) (h4 : 0≤z4 ∧ z4≤27)
    (e0 : z1=4*z0 ∨ z1=4*z0-54) (e1 : z2=4*z1 ∨ z2=4*z1-54)
    (e2 : z3=4*z2 ∨ z3=4*z2-54) (e3 : z4=4*z3 ∨ z4=4*z3-54) : z0=0 ∨ z0=18 := by omega

theorem scaled_bounds (H z : Int) (hH : 0<H) (h : 0≤H*z ∧ H*z≤27*H) : 0≤z ∧ z≤27 := by
  constructor
  · apply Int.le_of_mul_le_mul_left _ hH
    simpa using h.1
  · apply Int.le_of_mul_le_mul_left _ hH
    simpa [Int.mul_comm] using h.2

theorem scaled_step (H a r z : Int) (e : Bool) (hr : r=27*H) (ha : a=H*z) :
    4*a-(if e then 2*r else 0)=H*(4*z-(if e then 54 else 0)) := by
  subst r a
  cases e <;> simp [Int.mul_sub,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] <;> omega

theorem four_scaled (H r a : Int) (e : Nat → Bool) (i : Nat) (z : Int)
    (hH : 0<H) (hr : r=27*H) (hz : lead r a e i=H*z)
    (hb : ∀ j, j≤i+4 → 0≤lead r a e j ∧ lead r a e j≤r) : z=0 ∨ z=18 := by
  let z1 := 4*z-(if e i then 54 else 0)
  let z2 := 4*z1-(if e (i+1) then 54 else 0)
  let z3 := 4*z2-(if e (i+2) then 54 else 0)
  let z4 := 4*z3-(if e (i+3) then 54 else 0)
  have h1 : lead r a e (i+1)=H*z1 := scaled_step H _ _ z (e i) hr hz
  have h2 : lead r a e (i+2)=H*z2 := scaled_step H _ _ z1 (e (i+1)) hr h1
  have h3 : lead r a e (i+3)=H*z3 := scaled_step H _ _ z2 (e (i+2)) hr h2
  have h4 : lead r a e (i+4)=H*z4 := scaled_step H _ _ z3 (e (i+3)) hr h3
  have b0 := hb i (by omega); rw [hz,hr] at b0
  have b1 := hb (i+1) (by omega); rw [h1,hr] at b1
  have b2 := hb (i+2) (by omega); rw [h2,hr] at b2
  have b3 := hb (i+3) (by omega); rw [h3,hr] at b3
  have b4 := hb (i+4) (by omega); rw [h4,hr] at b4
  apply four_edges z z1 z2 z3 z4 (scaled_bounds _ _ hH b0) (scaled_bounds _ _ hH b1) (scaled_bounds _ _ hH b2) (scaled_bounds _ _ hH b3) (scaled_bounds _ _ hH b4)
  · dsimp only [z1]; split <;> omega
  · dsimp only [z2]; split <;> omega
  · dsimp only [z3]; split <;> omega
  · dsimp only [z4]; split <;> omega

theorem pow16_mod3 (s : Nat) : (16:Int)^s%3=1 := by
  induction s with
  | zero => decide
  | succ s ih => rw [Int.pow_succ,Int.mul_emod,ih]; decide

theorem low_coeff_mod (s : Nat) (d : Int) :
    (144*(16:Int)^s-2*d)%27=(9-2*d)%27 := by
  have h := pow16_mod3 s
  omega

def lowA (s : Nat) (d : Int) : Int := 144*(16:Int)^s-2*d
def lowR (s : Nat) : Int := 216*(16:Int)^s
def lowL (s : Nat) : Nat := 2*s+6

theorem low_no_halt (s : Nat) (d P x y : Int) (n : Nat) (U V : Nat → Int) (e : Nat → Bool)
    (hd : d%27≠18) (hx : 0≤x) (hy : 0≤y) (hn : n≤lowL s)
    (hU : U 0=lowA s d*P+x) (hV : V 0=lowR s*P+y) (hs : Blocks U V e n)
    (hsep : 3*cap (budget x y (lowL s)) (lowL s)+39<P) : 2*U n≠V n+39 := by
  intro hh
  have he := leading_halt P (lowR s) (lowA s d) x y (lowL s) n U V e hx hy hn hU hV hs hsep hh
  have hR : lowR s%27=0 := by unfold lowR; omega
  have hA : lowA s d%27≠0 := by unfold lowA; rw [low_coeff_mod]; omega
  have hm := lead_mod27 (lowR s) (lowA s d) e hR hA n
  omega

theorem low_no_full (s : Nat) (d P x y : Int) (U V : Nat → Int) (e : Nat → Bool)
    (hd0 : d%27≠0) (hd18 : d%27≠18) (hx : 0≤x) (hy : 0≤y)
    (hU : U 0=lowA s d*P+x) (hV : V 0=lowR s*P+y) (hs : Blocks U V e (lowL s))
    (hp : Physical U V (lowL s))
    (hsep : 3*cap (budget x y (lowL s)) (lowL s)+39<P) : False := by
  let H : Int := 8*16^s
  let i : Nat := 2*s+2
  have hH : 0<H := Int.mul_pos (by decide) (Int.pow_pos (by decide))
  have hr : lowR s=27*H := by simp [lowR,H]; omega
  have hpow : (4:Int)^i=2*H := by
    dsimp [i,H]
    rw [Int.pow_add,Int.pow_mul]
    change (16:Int)^s*16=2*(8*16^s)
    omega
  obtain ⟨q,hq⟩ := lead_form (lowR s) (lowA s d) e i
  rw [hpow] at hq
  have hz : lead (lowR s) (lowA s d) e i=H*(2*lowA s d+27*q) := by
    rw [hq,hr,Int.mul_add,Int.mul_left_comm H 2,Int.mul_assoc,Int.mul_left_comm H 27,Int.mul_assoc 27 H q]
  have hb := leading_bounds P (lowR s) (lowA s d) x y (lowL s) (lowL s) U V e hx hy (by omega) hU hV hs hp hsep
  have h := four_scaled H (lowR s) (lowA s d) e i (2*lowA s d+27*q) hH hr hz (by simpa [i,lowL] using hb)
  have hm : lowA s d%27=(9-2*d)%27 := low_coeff_mod s d
  omega

#print axioms low_no_halt
#print axioms low_no_full

end BB429.CoarseExit
