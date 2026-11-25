import DrainImageGates

namespace BB6.Agent41DrainImageDecoder

/-- The other fixed local gap of the parity-sorted image. -/
theorem image_gap_eight {E : Nat → Nat} (he : ExcessLaws E)
    (b : Nat) (hb : b%3=2) : image E (b+2)= image E b+8 := by
  let q := b/3
  have h0 : b=3*q+2 := by omega
  have h1 : b+2=3*(q+1)+1 := by omega
  unfold image
  rw [h1,h0,he.r1,he.r2]
  omega

theorem image_order {E : Nat → Nat} (he : ExcessLaws E)
    (b c : Nat) (hp : b%2= c%2) (h : b≤ c) :
    image E b≤ image E c := by
  have hh : c= b+2*((c-b)/2) := by omega
  have hm := image_progression he b ((c-b)/2)
  rw [←hh] at hm
  omega

theorem image_strict_order {E : Nat → Nat} (he : ExcessLaws E)
    (b c : Nat) (hp : b%2= c%2) (h : image E b < image E c) : b+2≤ c := by
  by_cases h' : c≤ b
  · have hh := image_order he c b hp.symm h'
    omega
  · omega

/-- No three image points in an arithmetic progression with positive even
step below eight. In particular the same conclusion holds on each residue
class modulo six, which is needed for actual terminal configurations. -/
theorem no_three_short_AP {E : Nat → Nat} (he : ExcessLaws E)
    (y s b c d : Nat) (hs : 0 < s) (hs2 : s%2=0) (hs8 : s < 8)
    (hb : image E b= y) (hc : image E c= y+s) (hd : image E d= y+2*s) :
    False := by
  have hbp := image_parity he b
  have hcp := image_parity he c
  have hdp := image_parity he d
  have hbc := image_strict_order he b c (by omega) (by omega)
  have hcd := image_strict_order he c d (by omega) (by omega)
  have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases hr with h0|h1|h2
  · by_cases hbig : b+4≤ c
    · have hgap := image_gap_eight he (b+2) (by omega)
      rw [show b+2+2= b+4 by omega] at hgap
      have hmin := (image_min_gap he b).1
      have hmono := image_order he (b+4) c (by omega) hbig
      omega
    · have heq : c= b+2 := by omega
      have hgap := image_gap_eight he c (by omega)
      have hmono := image_order he (c+2) d (by omega) hcd
      omega
  · by_cases hbig : b+4≤ c
    · have hgap := image_gap_eight he (b+4) (by omega)
      rw [show b+4+2= b+6 by omega] at hgap
      have hcc : c= b+4 ∨ b+6≤ c := by omega
      rcases hcc with hce|hce
      · have hmono := image_order he (c+2) d (by omega) hcd
        rw [show b+6= c+2 by omega,←hce] at hgap
        omega
      · have hm := image_order he (b+6) c (by omega) hce
        have hm' := image_order he b (b+4) (by omega) (by omega)
        omega
    · have heq : c= b+2 := by omega
      have hmin := (image_min_gap he b).2.mpr h1
      rw [←heq] at hmin
      have hs' : s=2 := by omega
      have hdc : d= c+2 := image_adjacent he c d (by omega)
      have hmin' := (image_min_gap he c).2.mp (show image E (c+2)= image E c+2 by rw [←hdc]; omega)
      omega
  · have hgap := image_gap_eight he b h2
    have hmono := image_order he (b+2) c (by omega) hbc
    omega

theorem inverse_no_three_six {E : Nat → Nat} (he : ExcessLaws E) (y : Nat) :
    inverse y= none ∨ inverse (y+6)= none ∨ inverse (y+12)= none := by
  cases hb : inverse y with
  | none => exact Or.inl rfl
  | some b =>
    cases hc : inverse (y+6) with
    | none => exact Or.inr (Or.inl rfl)
    | some c =>
      cases hd : inverse (y+12) with
      | none => exact Or.inr (Or.inr rfl)
      | some d =>
        exact False.elim (no_three_short_AP he y 6 b c d (by decide) (by decide) (by decide)
          (inverse_sound he _ _ hb) (inverse_sound he _ _ hc) (inverse_sound he _ _ hd))

/-- Within each long same-parity image gap, choose any congruence
class modulo six: among its next three rows one has both shifts absent. -/
theorem blocked_band_six {E : Nat → Nat} (he : ExcessLaws E)
    (k j : Nat) (hk : 2≤ k) (hj : 1≤ j) (hj' : j+6≤ k+5) :
    let y := 9*tau k+2*j+(if k%2=0 then 2 else 0)
    blocked y ∨ blocked (y+6) ∨ blocked (y+12) := by
  dsimp
  have hp := tau_parity k
  have hg0 := band_gap he k j hj (by omega)
  have hg1 := band_gap he k (j+3) (by omega) (by omega)
  have hg2 := band_gap he k (j+6) (by omega) (by omega)
  have ht := tau_mono (show 2≤ k by omega)
  have ht' : tau 2=4 := by decide
  rw [ht'] at ht
  by_cases h : k%2=0
  · rw [if_pos h]
    let y := 9*tau k+2*j+2
    change blocked y ∨ blocked (y+6) ∨ blocked (y+12)
    have hy : y%2=0 := by dsimp [y]; omega
    have h0 : y-2=9*tau k+2*j := by dsimp [y]; omega
    have h1 : y+6-2=9*tau k+2*(j+3) := by dsimp [y]; omega
    have h2 : y+12-2=9*tau k+2*(j+6) := by dsimp [y]; omega
    have hn := inverse_no_three_six he (y-3)
    have hn1 : y-3+6= y+6-3 := by dsimp [y]; omega
    have hn2 : y-3+12= y+12-3 := by dsimp [y]; omega
    rw [hn1,hn2] at hn
    have hy1 : (y+6)%2=0 := by omega
    have hy2 : (y+12)%2=0 := by omega
    unfold blocked
    simp only [if_pos hy, if_pos hy1, if_pos hy2, h0,h1,h2,hg0,hg1,hg2,true_and]
    exact hn
  · rw [if_neg h]
    let y := 9*tau k+2*j
    change blocked y ∨ blocked (y+6) ∨ blocked (y+12)
    have hy : y%2≠0 := by dsimp [y]; omega
    have hy1 : (y+6)%2≠0 := by omega
    have hy2 : (y+12)%2≠0 := by omega
    have h0 : y=9*tau k+2*j := rfl
    have h1 : y+6=9*tau k+2*(j+3) := by dsimp [y]; omega
    have h2 : y+12=9*tau k+2*(j+6) := by dsimp [y]; omega
    have hn := inverse_no_three_six he (y-5)
    have hn1 : y-5+6= y+6-5 := by dsimp [y]; omega
    have hn2 : y-5+12= y+12-5 := by dsimp [y]; omega
    rw [hn1,hn2] at hn
    have g0 : inverse y= none := by rw [h0]; exact hg0
    have g1 : inverse (y+6)= none := by rw [h1]; exact hg1
    have g2 : inverse (y+12)= none := by rw [h2]; exact hg2
    rcases hn with hn|hn|hn
    · exact Or.inl (by unfold blocked; rw [if_neg hy]; exact ⟨hn,g0⟩)
    · exact Or.inr (Or.inl (by unfold blocked; rw [if_neg hy1]; exact ⟨hn,g1⟩))
    · exact Or.inr (Or.inr (by unfold blocked; rw [if_neg hy2]; exact ⟨hn,g2⟩))


/-- A zero-residue descent adds exactly two to the parity-image gap. -/
theorem image_r0_gap {E : Nat → Nat} (he : ExcessLaws E) (b : Nat) :
    image E (3*(b+1)+2)+image E b =
      image E (3*(b+1))+image E (b+2)+2 := by
  unfold image
  rw [he.r2,he.r0 _ (by omega)]
  have h1 : b+1-1= b := by omega
  have h2 : b+1+1= b+2 := by omega
  rw [h1,h2]
  omega

def liftZero : Nat → Nat → Nat
  | 0,b => b
  | m+1,b => 3*(liftZero m b+1)

theorem liftZero_closed (m b : Nat) :
    liftZero m b=3^m*b+3*tau m := by
  induction m with
  | zero => simp [liftZero,tau]
  | succ m ih =>
    rw [liftZero,ih,tau,Nat.pow_succ]
    rw [Nat.mul_right_comm (3^m) 3 b]
    rw [Nat.mul_comm (3^m*b) 3]
    omega

theorem liftZero_gap {E : Nat → Nat} (he : ExcessLaws E) (m b : Nat) :
    image E (liftZero m b)+2*m+2≤ image E (liftZero m b+2) := by
  induction m with
  | zero => simpa [liftZero] using (image_min_gap he b).1
  | succ m ih =>
    have h := image_r0_gap he (liftZero m b)
    rw [liftZero]
    omega

theorem inverse_missing_between {E : Nat → Nat} (he : ExcessLaws E)
    (b v : Nat) (hp : v%2= b%2)
    (hl : image E b < v) (hu : v < image E (b+2)) :
    inverse v= none := by
  cases hv : inverse v with
  | none => rfl
  | some c =>
    have h := inverse_sound he v c hv
    change image E c= v at h
    have hc := image_parity he c
    have hbc := image_strict_order he b c (by omega) (by omega)
    have hm := image_order he (b+2) c (by omega) hbc
    omega


def pickThree (y : Nat) : Nat :=
  if blocked y then y else if blocked (y+6) then y+6 else y+12

theorem pickThree_spec (y : Nat)
    (h : blocked y ∨ blocked (y+6) ∨ blocked (y+12)) :
    blocked (pickThree y) ∧
      (pickThree y= y ∨ pickThree y= y+6 ∨ pickThree y= y+12) := by
  unfold pickThree
  by_cases h0 : blocked y
  · simp [h0]
  · by_cases h1 : blocked (y+6)
    · simp [h0,h1]
    · have h2 : blocked (y+12) := by rcases h with h|h|h; exact False.elim (h0 h); exact False.elim (h1 h); exact h
      simp [h0,h1,h2]

def pickGap (v : Nat) : Nat :=
  pickThree (v+2*(3-(v%6)/2)+(if v%2=0 then 2 else 0))

/-- Any sufficiently wide single gap in a parity-sorted image contains,
after the appropriate shift, a genuinely predecessor-free terminal row.
The congruence is precisely the immediate failure congruence. -/
theorem pick_gap_spec {E : Nat → Nat} (he : ExcessLaws E)
    (b : Nat) (hbig : 14 < image E b)
    (hgap : image E b+20≤ image E (b+2)) :
    let z := if b%2=0 then 2 else 0
    let d := pickGap (image E b)
    image E b+z < d ∧ d < image E (b+2)+z ∧
      d≤ image E b+20 ∧ d%2= b%2 ∧ (d%6=1 ∨ d%6=2) ∧ blocked d := by
  dsimp
  let v := image E b
  let j := 3-(v%6)/2
  have hj : 1≤ j ∧ j≤3 := by dsimp [j]; omega
  have hp := image_parity he b
  have hg0 := inverse_missing_between he b (v+2*j) (by dsimp [v]; omega)
    (by dsimp [v]; omega) (by dsimp [v]; omega)
  have hg1 := inverse_missing_between he b (v+2*j+6) (by dsimp [v]; omega)
    (by dsimp [v]; omega) (by dsimp [v]; omega)
  have hg2 := inverse_missing_between he b (v+2*j+12) (by dsimp [v]; omega)
    (by dsimp [v]; omega) (by dsimp [v]; omega)
  by_cases h : b%2=0
  · rw [if_pos h]
    let y := v+2*j+2
    have hmod : y%6=2 := by dsimp [y,j,v]; omega
    have hy : y%2=0 := by omega
    have h0 : y-2= v+2*j := by dsimp [y]; omega
    have h1 : y+6-2= v+2*j+6 := by dsimp [y]; omega
    have h2 : y+12-2= v+2*j+12 := by dsimp [y]; omega
    have hn := inverse_no_three_six he (y-3)
    have hn1 : y-3+6= y+6-3 := by dsimp [y,v]; omega
    have hn2 : y-3+12= y+12-3 := by dsimp [y,v]; omega
    rw [hn1,hn2] at hn
    have hy1 : (y+6)%2=0 := by omega
    have hy2 : (y+12)%2=0 := by omega
    have hb : blocked y ∨ blocked (y+6) ∨ blocked (y+12) := by
      unfold blocked
      simp only [if_pos hy,if_pos hy1,if_pos hy2,h0,h1,h2,hg0,hg1,hg2,true_and]
      exact hn
    have hd : pickGap (image E b)= pickThree y := by
      have hv : v%2=0 := by dsimp [v]; omega
      simp [pickGap,y,j,v,show image E b%2=0 by omega]
    rw [hd]
    obtain ⟨hb',hh⟩ := pickThree_spec y hb
    rcases hh with hh|hh|hh <;> rw [hh] at hb' ⊢ <;>
      refine ⟨?_,?_,?_,?_,Or.inr (by omega),hb'⟩ <;> dsimp [y,v] <;> omega
  · rw [if_neg h]
    let y := v+2*j
    have hmod : y%6=1 := by dsimp [y,j,v]; omega
    have hy : y%2≠0 := by omega
    have hy1 : (y+6)%2≠0 := by omega
    have hy2 : (y+12)%2≠0 := by omega
    have hn := inverse_no_three_six he (y-5)
    have hn1 : y-5+6= y+6-5 := by dsimp [y,v]; omega
    have hn2 : y-5+12= y+12-5 := by dsimp [y,v]; omega
    rw [hn1,hn2] at hn
    have g0 : inverse y= none := hg0
    have g1 : inverse (y+6)= none := hg1
    have g2 : inverse (y+12)= none := hg2
    have hb : blocked y ∨ blocked (y+6) ∨ blocked (y+12) := by
      rcases hn with hn|hn|hn
      · exact Or.inl (by unfold blocked; rw [if_neg hy]; exact ⟨hn,g0⟩)
      · exact Or.inr (Or.inl (by unfold blocked; rw [if_neg hy1]; exact ⟨hn,g1⟩))
      · exact Or.inr (Or.inr (by unfold blocked; rw [if_neg hy2]; exact ⟨hn,g2⟩))
    have hd : pickGap (image E b)= pickThree y := by
      have hv : v%2≠0 := by dsimp [v]; omega
      simp [pickGap,y,j,v,show image E b%2≠0 by omega]
    rw [hd]
    obtain ⟨hb',hh⟩ := pickThree_spec y hb
    rcases hh with hh|hh|hh <;> rw [hh] at hb' ⊢ <;>
      refine ⟨?_,?_,?_,?_,Or.inl (by omega),hb'⟩ <;> dsimp [y,v] <;> omega


theorem excess_le_binary {E : Nat → Nat} (he : ExcessLaws E)
    (n : Nat) : ∀ b, b < 2^n → E b≤4*n := by
  induction n with
  | zero =>
    intro b hb
    have hb0 : b=0 := by simp at hb; exact hb
    subst b
    rw [he.zero]; omega
  | succ n ih =>
    intro b hb
    by_cases h : b=0
    · subst b; rw [he.zero]; omega
    · have hp : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
      have hp0 : 0 < 2^n := Nat.pow_pos (by decide)
      let q := b/3
      have hrep : b=3*q+b%3 := by dsimp [q]; omega
      have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
      rcases hr with h0|h1|h2
      · have hq : 0 < q := by omega
        have hq' : q-1 < 2^n := by omega
        have hh := ih (q-1) hq'
        rw [show b=3*q by omega,he.r0 _ hq]
        omega
      · have hq' : q < 2^n := by omega
        have hh := ih q hq'
        rw [show b=3*q+1 by omega,he.r1]
        omega
      · have hq' : q+1 < 2^n := by omega
        have hh := ih (q+1) hq'
        rw [show b=3*q+2 by omega,he.r2]
        omega

theorem excess_log_bound {E : Nat → Nat} (he : ExcessLaws E) (b : Nat) :
    E b≤4*(b.log2+1) := by
  by_cases hb : b=0
  · subst b; rw [he.zero]; omega
  · apply excess_le_binary he
    exact (Nat.log2_lt hb).mp (by omega)

theorem liftZero_parity (m b : Nat) : (liftZero m b)%2=(m+b)%2 := by
  induction m with
  | zero => simp [liftZero]
  | succ m ih => rw [liftZero]; omega

/-- A computable injection from natural indices to blocked terminal rows.
Nine initial zero-residue steps create gaps of at least twenty.
The image interval for each index is disjoint within its parity. -/
def terminalRow (E : Nat → Nat) (c : Nat) : Nat :=
  pickGap (image E (liftZero 9 c))

theorem terminalRow_spec {E : Nat → Nat} (he : ExcessLaws E) (c : Nat) :
    let b := 19683*c+29523
    let d := terminalRow E c
    let z := if b%2=0 then 2 else 0
    image E b+z < d ∧ d < image E (b+2)+z ∧
      d≤3*b+4*(b.log2+1)+20 ∧ d%2=(c+1)%2 ∧
      (d%6=1 ∨ d%6=2) ∧ blocked d := by
  dsimp
  have hb : liftZero 9 c=19683*c+29523 := by
    rw [liftZero_closed]
    have h1 : 3^9=19683 := by decide
    have h2 : 3*tau 9=29523 := by decide
    rw [h1,h2]
  have hg := liftZero_gap he 9 c
  have hbig : 14 < image E (liftZero 9 c) := by rw [hb]; unfold image; omega
  have hgap : image E (liftZero 9 c)+20≤ image E (liftZero 9 c+2) := by omega
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := pick_gap_spec he _ hbig hgap
  have hp := liftZero_parity 9 c
  have he' := excess_log_bound he (19683*c+29523)
  unfold terminalRow
  rw [hb] at h0 h1 h2 h3 h4 h5 hp ⊢
  refine ⟨h0,h1,?_,?_,h4,h5⟩
  · have hF : image E (19683*c+29523)=3*(19683*c+29523)+E (19683*c+29523) := rfl
    omega
  · omega

theorem terminalRow_injective {E : Nat → Nat} (he : ExcessLaws E) :
    ∀ c c', terminalRow E c= terminalRow E c' → c= c' := by
  intro c c' h
  obtain ⟨h0,h1,_,hpar,_,_⟩ := terminalRow_spec he c
  obtain ⟨h0',h1',_,hpar',_,_⟩ := terminalRow_spec he c'
  have hcc : c%2= c'%2 := by omega
  let b := 19683*c+29523
  let b' := 19683*c'+29523
  have hp : b%2= b'%2 := by dsimp [b,b']; omega
  have hz : (if b%2=0 then 2 else 0)=(if b'%2=0 then 2 else 0) := by rw [hp]
  change image E b+(if b%2=0 then 2 else 0) < terminalRow E c at h0
  change terminalRow E c < image E (b+2)+(if b%2=0 then 2 else 0) at h1
  change image E b'+(if b'%2=0 then 2 else 0) < terminalRow E c' at h0'
  change terminalRow E c' < image E (b'+2)+(if b'%2=0 then 2 else 0) at h1'
  by_cases hlt : c < c'
  · have hbb : b+2≤ b' := by dsimp [b,b']; omega
    have hm := image_order he (b+2) b' (by omega) hbb
    rw [hz] at h1
    omega
  · by_cases hgt : c' < c
    · have hbb : b'+2≤ b := by dsimp [b,b']; omega
      have hm := image_order he (b'+2) b (by omega) hbb
      rw [hz] at h0
      omega
    · omega

#print axioms terminalRow_spec
#print axioms terminalRow_injective

#print axioms liftZero_gap
#print axioms pick_gap_spec

#print axioms no_three_short_AP
#print axioms blocked_band_six
end BB6.Agent41DrainImageDecoder
