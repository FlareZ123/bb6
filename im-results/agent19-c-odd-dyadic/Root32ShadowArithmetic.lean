import Lean

namespace BB6.Agent19Shadow

abbrev C : Nat := 22155

def lift (p u v x y : Nat) : Prop := 2^p ∣ C*x+u ∧ 2^p ∣ C*y+v

def oddMass (u v : Nat) : Nat := (u+v)%2

def shadowMass (u v : Nat) : Nat := u+v-C*oddMass u v

def v2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | f+1, n => if n%2=0 then 1+v2Aux f (n/2) else 0

def valuation (q : Nat) : Nat := v2Aux (q.log2+1) q

def hiU (u v n : Nat) : Nat := shadowMass u v / 2^(n+1)+C*(2+oddMass u v)
def hiV (u v n : Nat) : Nat := (u+2*v+C*(7+3*n)-hiU u v n)/2

def leaf (u v : Nat) : Bool := v%2 == 1 && ((u+v)%4 == 1 || (u+v)%4 == 2)

def branchGuard (p u v w : Nat) : Bool :=
  decide (0<u ∧ 0<v ∧ 2≤p ∧ C*oddMass u v<u+v ∧ w+1≤p ∧
    shadowMass u v % 2^(w+1)=2^w ∧ (u+v+C*(2^w+16)).log2<p)

def depthGuard (u v w n : Nat) : Bool := decide (n+2≤w ∧ n%2=(u+1+oddMass u v)%2)

def hiGuard (u v n : Nat) : Bool := decide (2^(n+1)*hiU u v n=shadowMass u v+2^(n+1)*(C*(2+oddMass u v)) ∧
  2*hiV u v n+hiU u v n=u+2*v+C*(7+3*n))

def excluded : Nat → Nat → Nat → Nat → Bool
  | 0,p,u,v => leaf u v && decide (0<v ∧ 2≤p ∧ (v+5*C).log2<p)
  | f+1,p,u,v =>
    if leaf u v then decide (0<v ∧ 2≤p ∧ (v+5*C).log2<p)
    else
      let w := valuation (shadowMass u v)
      branchGuard p u v w &&
      (if v%2 == 0 then excluded f (p-1) (u+v+2*C) ((v+2*C)/2) else true) &&
      (List.range w).all (fun n => if depthGuard u v w n then
        hiGuard u v n && excluded f (p-(n+2)) (hiU u v n) (hiV u v n) else true)

private theorem lift_lower {p q u v x y : Nat} (h : lift p u v x y) (hq : q≤p) : lift q u v x y :=
  ⟨Nat.dvd_trans (Nat.pow_dvd_pow 2 hq) h.1, Nat.dvd_trans (Nat.pow_dvd_pow 2 hq) h.2⟩

private theorem residue4 {p u v x y : Nat} (h : lift p u v x y) (hp : 2≤p) : x%4=u%4 ∧ y%4=v%4 := by
  have h' := lift_lower h hp
  have hx := Nat.mod_eq_zero_of_dvd h'.1
  have hy := Nat.mod_eq_zero_of_dvd h'.2
  change (22155*x+u)%4=0 at hx
  change (22155*y+v)%4=0 at hy
  omega

private theorem residue2 {p u v x y : Nat} (h : lift p u v x y) (hp : 2≤p) : x%2=u%2 ∧ y%2=v%2 ∧ (x+y)%2=oddMass u v := by
  obtain ⟨hx,hy⟩ := residue4 h hp
  unfold oddMass
  omega

private theorem size_bound {p u x b : Nat} (hu : 0<u) (h : 2^p ∣ C*x+u) (hb : (u+C*b).log2<p) : b<x := by
  have hpos : 0<C*x+u := by omega
  have hbig := Nat.le_of_dvd hpos h
  have hsmall := (Nat.log2_lt (show u+C*b≠0 by omega)).mp hb
  simp only [C] at *
  omega

private theorem dvd_cancel_pow {p d z : Nat} (hd : d≤p) (h : 2^p ∣ 2^d*z) : 2^(p-d) ∣ z := by
  have he : p=d+(p-d) := by omega
  rw [he, Nat.pow_add] at h
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos d) h

private theorem valuation_transfer {p w u v x y : Nat} (h : lift p u v x y)
    (hp : 2≤p) (hw : w+1≤p) (hpos : C*oddMass u v≤u+v)
    (hv : shadowMass u v % 2^(w+1)=2^w) : (x+y+(x+y)%2)%2^(w+1)=2^w := by
  let q := x+y+(x+y)%2
  let Q := shadowMass u v
  have ho := (residue2 h hp).2.2
  have hsum : C*q+Q=(C*x+u)+(C*y+v) := by
    dsimp [q,Q,shadowMass]
    rw [ho]
    simp only [C] at *
    omega
  have hsumD : 2^(w+1) ∣ C*q+Q := by
    rw [hsum]
    exact Nat.dvd_add (lift_lower h hw).1 (lift_lower h hw).2
  have hd : 2^w ∣ 2^(w+1) := Nat.pow_dvd_pow 2 (by omega)
  have hQD : 2^w ∣ Q := by
    apply Nat.dvd_of_mod_eq_zero
    rw [←Nat.mod_mod_of_dvd Q hd]
    change shadowMass u v % 2^(w+1) % 2^w=0
    rw [hv,Nat.mod_self]
  have hCq : 2^w ∣ C*q := (Nat.dvd_add_iff_left hQD).mpr (Nat.dvd_trans hd hsumD)
  have hq : 2^w ∣ q := (Nat.Coprime.pow_left w (by decide : Nat.Coprime 2 C)).dvd_of_dvd_mul_left hCq
  have hnot : ¬ 2^(w+1) ∣ q := by
    intro hq'
    have hQD' := (Nat.dvd_add_iff_right (Nat.dvd_trans hq' (Nat.dvd_mul_left q C))).mpr hsumD
    have hz := Nat.mod_eq_zero_of_dvd hQD'
    change Q % 2^(w+1)=2^w at hv
    rw [hv] at hz
    exact (Nat.ne_of_gt (Nat.two_pow_pos w)) hz
  obtain ⟨k,hk⟩ := hq
  have hmod : q%2^(w+1)=2^w*(k%2) := by
    rw [hk,Nat.pow_succ,Nat.mul_mod_mul_left]
  have hkodd : k%2=1 := by
    by_cases hn : k%2=1
    · exact hn
    · exfalso
      have hz : k%2=0 := by omega
      apply hnot
      apply Nat.dvd_of_mod_eq_zero
      rw [hmod,hz,Nat.mul_zero]
  change q%2^(w+1)=2^w
  rw [hmod,hkodd,Nat.mul_one]

private theorem direct_lift {p u v x y a k : Nat} (h : lift p u v x y) (hp : 2≤p)
    (hy : y%2=0) (ha : a+2=x+y) (hk : 2*k+2=y) :
    lift (p-1) (u+v+2*C) ((v+2*C)/2) a k := by
  have hv : v%2=0 := by have := (residue2 h hp).2.1; omega
  have h1 : C*a+(u+v+2*C)=(C*x+u)+(C*y+v) := by simp only [C] at *; omega
  have h2 : 2*(C*k+(v+2*C)/2)=C*y+v := by simp only [C] at *; omega
  constructor
  · rw [h1]
    exact Nat.dvd_add (lift_lower h (by omega : p-1≤p)).1 (lift_lower h (by omega : p-1≤p)).2
  · apply dvd_cancel_pow (p:=p) (d:=1) (by omega)
    simpa [h2] using h.2

private theorem high_lift {p u v x y a k n : Nat} (h : lift p u v x y) (hp : 2≤p) (hn : n+2≤p)
    (hpos : C*oddMass u v≤u+v)
    (ha : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2))
    (hk : 2*k+a+7+3*n=x+2*y)
    (hu : 2^(n+1)*hiU u v n=shadowMass u v+2^(n+1)*(C*(2+oddMass u v)))
    (hv : 2*hiV u v n+hiU u v n=u+2*v+C*(7+3*n)) :
    lift (p-(n+2)) (hiU u v n) (hiV u v n) a k := by
  have ho := (residue2 h hp).2.2
  rw [ho] at ha
  have he1 : 2^(n+1)*(C*a+hiU u v n)=(C*x+u)+(C*y+v) := by
    rw [Nat.mul_add,hu]
    have he : C*(x+y+oddMass u v)=2^(n+1)*(C*a)+2^(n+1)*(C*(2+oddMass u v)) := by
      rw [ha]
      simp only [Nat.mul_left_comm C, Nat.mul_add]
      simp only [←Nat.mul_add, Nat.add_assoc]
    unfold shadowMass
    simp only [C] at *
    omega
  have he2 : 2*(C*k+hiV u v n)+(C*a+hiU u v n)=(C*x+u)+2*(C*y+v) := by simp only [C] at *; omega
  have hA : 2^(p-(n+1)) ∣ C*a+hiU u v n := by
    apply dvd_cancel_pow (p:=p) (d:=n+1) (by omega)
    rw [he1]
    exact Nat.dvd_add h.1 h.2
  have hB : 2^(p-(n+1)) ∣ 2*(C*k+hiV u v n) := by
    apply (Nat.dvd_add_iff_left hA).mpr
    rw [he2]
    have h' := lift_lower h (show p-(n+1)≤p by omega)
    exact Nat.dvd_add h'.1 (Nat.dvd_trans h'.2 (Nat.dvd_mul_left _ 2))
  constructor
  · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hA
  · have h' := dvd_cancel_pow (p:=p-(n+1)) (d:=1) (by omega) (show 2^(p-(n+1)) ∣ 2^1*(C*k+hiV u v n) from hB)
    rwa [show p-(n+1)-1=p-(n+2) by omega] at h'

/-- Soundness of the shadow search, quantified over any reachability relation
whose large targets have the ordinary predecessor equations and whose
odd-image forbidden classes are unreachable. -/
theorem excluded_sound (reach : Nat→Nat→Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (parent : ∀ x y w, 5<x → 8≤y → (x+y+(x+y)%2)%2^(w+1)=2^w → 2^w<x+y+(x+y)%2 → reach x y →
      (∃ a k, reach a k ∧ y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
      (∃ a k n, reach a k ∧ n+2≤w ∧ n%2=(x+1+(x+y)%2)%2 ∧
      x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧ 2*k+a+7+3*n=x+2*y)) :
    ∀ f p u v x y, excluded f p u v=true → lift p u v x y → ¬reach x y := by
  have leafSound : ∀ p u v x y, leaf u v=true → 0<v → 2≤p → (v+5*C).log2<p → lift p u v x y → ¬reach x y := by
    intro p u v x y hl hv hp hb h
    have hy := size_bound (b:=5) hv h.2 (by simpa [Nat.mul_comm] using hb)
    obtain ⟨h4x,h4y⟩ := residue4 h hp
    simp [leaf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    exact forbid x y (by omega) (by omega) (by omega)
  intro f
  induction f with
  | zero =>
    intro p u v x y he h
    simp only [excluded,Bool.and_eq_true,decide_eq_true_eq] at he
    exact leafSound p u v x y he.1 he.2.1 he.2.2.1 he.2.2.2 h
  | succ f ih =>
    intro p u v x y he h hr
    simp only [excluded] at he
    split at he
    · rename_i hl
      simp only [decide_eq_true_eq] at he
      exact leafSound p u v x y hl he.1 he.2.1 he.2.2 h hr
    · simp only [Bool.and_eq_true] at he
      obtain ⟨⟨hg,hd⟩,hh⟩ := he
      let w := valuation (shadowMass u v)
      change branchGuard p u v w=true at hg
      simp only [branchGuard,decide_eq_true_eq] at hg
      obtain ⟨hu,hv,hp,hpos,hw,hval,hsize⟩ := hg
      have hb := (Nat.log2_lt (show u+v+C*(2^w+16)≠0 by omega)).mp hsize
      have hx : 5<x := by
        have hm := Nat.le_of_dvd (show 0<C*x+u by omega) h.1
        simp only [C] at *
        omega
      have hy : 8≤y := by
        have hm := Nat.le_of_dvd (show 0<C*y+v by omega) h.2
        simp only [C] at *
        omega
      have hqbig : 2^w<x+y+(x+y)%2 := by
        have ho := (residue2 h hp).2.2
        have hsum : C*(x+y+(x+y)%2)+shadowMass u v=(C*x+u)+(C*y+v) := by
          rw [ho]
          unfold shadowMass
          simp only [C] at *
          omega
        have hm := Nat.le_of_dvd (show 0<(C*x+u)+(C*y+v) by omega) (Nat.dvd_add h.1 h.2)
        simp only [C] at *
        omega
      have hval' := valuation_transfer h hp hw (by omega) hval
      rcases parent x y w hx hy hval' hqbig hr with ⟨a,k,hr',hy',ha,hk⟩ | ⟨a,k,n,hr',hn,hpar,ha,hk⟩
      · have hv' : v%2=0 := by have := (residue2 h hp).2.1; omega
        simp [hv'] at hd
        exact ih _ _ _ _ _ hd (direct_lift h hp hy' ha hk) hr'
      · have hnmem : n ∈ List.range w := List.mem_range.mpr (by omega)
        have hpar' : n%2=(u+1+oddMass u v)%2 := by
          obtain ⟨h2x,_,ho⟩ := residue2 h hp
          omega
        have hh' := List.all_eq_true.mp hh n hnmem
        change (if depthGuard u v w n then hiGuard u v n && excluded f (p-(n+2)) (hiU u v n) (hiV u v n) else true)=true at hh'
        have hg' : depthGuard u v w n=true := by simp [depthGuard,hn,hpar']
        simp only [hg',ite_true] at hh'
        simp only [hiGuard,Bool.and_eq_true,decide_eq_true_eq] at hh'
        obtain ⟨⟨hU,hV⟩,hrec⟩ := hh'
        exact ih _ _ _ _ _ hrec (high_lift h hp (by omega) (by omega) ha hk hU hV) hr'


/-- Independent size exponent for the actual right coordinate. -/
def RightLarge (q y : Nat) : Prop := 2^q ≤ y+2

private theorem rightLarge_direct {q y k : Nat} (h : RightLarge q y)
    (hq : 4≤q) (hk : 2*k+2=y) : RightLarge (q-1) k := by
  unfold RightLarge at *
  have he : 2^(q-1)*2=2^q := by
    simpa using Nat.pow_sub_mul_pow 2 (by omega : 1≤q)
  omega

private theorem rightLarge_high {q x y a k n : Nat} (h : RightLarge q y)
    (hq : n+6≤q) (ha : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2))
    (hk : 2*k+a+7+3*n=x+2*y) : RightLarge (q-(n+2)) k := by
  unfold RightLarge at *
  have he : 2^(q-(n+2))*2^(n+2)=2^q := Nat.pow_sub_mul_pow 2 (by omega)
  have hd : 2≤2^(n+1) := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n+1)
  have hd' : 4≤2^(n+2) := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤n+2)
  have hp : 4*2^(q-(n+2))≤2^q := by
    rw [←he]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2^(q-(n+2))) hd'
  have hn : 16+6*n≤2^q := by
    have h1 : 2^(n+6)≤2^q := Nat.pow_le_pow_right (by decide) hq
    have h2 : n<2^n := Nat.lt_pow_self (by decide)
    rw [Nat.pow_add,show (2:Nat)^6=64 by decide] at h1
    omega
  have ha2 : 2*a≤x+y+(x+y)%2 := by
    have h1 := Nat.mul_le_mul_right (a+2+(x+y)%2) hd
    rw [←ha] at h1
    omega
  omega

/-- Congruence-only branch guard: actual coordinate sizes are proved independently. -/
def modGuard (p u v w : Nat) : Bool :=
  decide (2≤p ∧ C*oddMass u v≤u+v ∧ w+1≤p ∧
    shadowMass u v % 2^(w+1)=2^w)

/-- Fuel bounds tree depth. Precision is spent only on exact residues, never on
    proving a lower bound for the true section coordinates. -/
def modExcluded : Nat → Nat → Nat → Nat → Bool
  | 0,p,u,v => leaf u v && decide (2≤p)
  | f+1,p,u,v =>
    if leaf u v then decide (2≤p)
    else
      let w := valuation (shadowMass u v)
      modGuard p u v w &&
      (if v%2 == 0 then modExcluded f (p-1) (u+v+2*C) ((v+2*C)/2) else true) &&
      (List.range w).all (fun n => if depthGuard u v w n then
        hiGuard u v n && modExcluded f (p-(n+2)) (hiU u v n) (hiV u v n) else true)

/-- Sound congruence-only shadow search with separate size exponent. -/
theorem modExcluded_sound (reach : Nat→Nat→Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (parent : ∀ x y w, 8≤y → (x+y+(x+y)%2)%2^(w+1)=2^w → 2^w<x+y+(x+y)%2 → reach x y →
      (∃ a k, reach a k ∧ y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
      (∃ a k n, reach a k ∧ n+2≤w ∧ n%2=(x+1+(x+y)%2)%2 ∧
      x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧ 2*k+a+7+3*n=x+2*y)) :
    ∀ f p u v q x y, modExcluded f p u v=true → lift p u v x y →
      p+4≤q → RightLarge q y → ¬reach x y := by
  have leafSound : ∀ p u v q x y, leaf u v=true → 2≤p → lift p u v x y → p+4≤q → RightLarge q y → ¬reach x y := by
    intro p u v q x y hl hp h hq hL
    have hsize : 16≤2^q := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (by omega : 4≤q)
    have hy : 2^q≤y+2 := hL
    obtain ⟨h4x,h4y⟩ := residue4 h hp
    simp [leaf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    exact forbid x y (by omega) (by omega) (by omega)
  intro f
  induction f with
  | zero =>
    intro p u v q x y he h hq hL
    simp only [modExcluded,Bool.and_eq_true,decide_eq_true_eq] at he
    exact leafSound p u v q x y he.1 he.2 h hq hL
  | succ f ih =>
    intro p u v q x y he h hq hL hr
    simp only [modExcluded] at he
    split at he
    · rename_i hl
      simp only [decide_eq_true_eq] at he
      exact leafSound p u v q x y hl he h hq hL hr
    · simp only [Bool.and_eq_true] at he
      obtain ⟨⟨hg,hd⟩,hh⟩ := he
      let w := valuation (shadowMass u v)
      change modGuard p u v w=true at hg
      simp only [modGuard,decide_eq_true_eq] at hg
      obtain ⟨hp,hpos,hw,hval⟩ := hg
      have hsize : 16≤2^q := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (by omega : 4≤q)
      have hlarge : 2^(w+1)≤2^q := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at hlarge
      have hy' : 2^q≤y+2 := hL
      have hy : 8≤y := by omega
      have hqbig : 2^w<x+y+(x+y)%2 := by omega
      have hval' := valuation_transfer h hp hw hpos hval
      rcases parent x y w hy hval' hqbig hr with ⟨a,k,hr',hy',ha,hk⟩ | ⟨a,k,n,hr',hn,hpar,ha,hk⟩
      · have hv' : v%2=0 := by have := (residue2 h hp).2.1; omega
        simp [hv'] at hd
        exact ih _ _ _ (q-1) _ _ hd (direct_lift h hp hy' ha hk) (by omega)
          (rightLarge_direct hL (by omega) hk) hr'
      · have hnmem : n ∈ List.range w := List.mem_range.mpr (by omega)
        have hpar' : n%2=(u+1+oddMass u v)%2 := by
          obtain ⟨h2x,_,ho⟩ := residue2 h hp
          omega
        have hh' := List.all_eq_true.mp hh n hnmem
        change (if depthGuard u v w n then hiGuard u v n && modExcluded f (p-(n+2)) (hiU u v n) (hiV u v n) else true)=true at hh'
        have hg' : depthGuard u v w n=true := by simp [depthGuard,hn,hpar']
        simp only [hg',ite_true] at hh'
        simp only [hiGuard,Bool.and_eq_true,decide_eq_true_eq] at hh'
        obtain ⟨⟨hU,hV⟩,hrec⟩ := hh'
        exact ih _ _ _ (q-(n+2)) _ _ hrec (high_lift h hp (by omega) hpos ha hk hU hV)
          (by omega) (rightLarge_high hL (by omega) ha hk) hr'

#print axioms modExcluded_sound

end BB6.Agent19Shadow
