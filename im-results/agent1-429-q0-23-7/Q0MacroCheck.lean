import Q0MacroCore
namespace BB429Q0Macro
set_option maxHeartbeats 2000000

def dead : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | k+1, p, y =>
    ((num .zero p y % 16 != 0) || dead k (nextP .zero p) (nextY .zero p y)) &&
    ((num .one p y % 16 != 0) || dead k (nextP .one p) (nextY .one p y)) &&
    ((num .four p y % 16 != 0) || dead k (nextP .four p) (nextY .four p y)) &&
    ((num .five p y % 16 != 0) || dead k (nextP .five p) (nextY .five p y))

theorem dead_sound {m p y : Nat} (h : dead m p y = true) : ¬ Path m p y := by
  intro hpath
  induction hpath with
  | nil p y => simp [dead] at h
  | cons d hdiv tail ih =>
    cases d <;> simp [dead,hdiv] at h
    · exact ih h.1.1.1
    · exact ih h.1.1.2
    · exact ih h.1.2
    · exact ih h.2

theorem path_take {m p y : Nat} (h : Path m p y) (k : Nat) (hk : k≤m) : Path k p y := by
  induction h generalizing k with
  | nil p y =>
    have : k=0 := by omega
    subst k
    exact .nil p y
  | cons d hd tail ih =>
    cases k with
    | zero => exact .nil _ _
    | succ k => exact .cons d hd (ih k (by omega))

/-- Congruent positive lifts have exactly the same permitted initial words. -/
theorem path_lower (m p y P Q : Nat)
    (h : Path m (p+16^m*P) (y+16^m*Q)) : Path m p y := by
  induction m generalizing p y P Q with
  | zero => exact .nil p y
  | succ k ih =>
    cases h with
    | cons d hdiv tail =>
      have hnum : num d (p+16^(k+1)*P) (y+16^(k+1)*Q) =
          num d p y + 16*(16^k*(Q+digit d*P)) := by
        unfold num; rw [Nat.pow_succ]; simp only [Nat.mul_add, Nat.add_mul]; ac_rfl
      have hd : num d p y%16=0 := by rw [hnum] at hdiv; omega
      have hp : nextP d (p+16^(k+1)*P) = nextP d p+16^k*(16*P) := by
        unfold nextP; rw [Nat.pow_succ,Nat.mul_assoc]; omega
      have hy : nextY d (p+16^(k+1)*P) (y+16^(k+1)*Q) =
          nextY d p y+16^k*(Q+digit d*P) := by
        unfold nextY; rw [hnum]; omega
      rw [hp,hy] at tail
      exact .cons d hd (ih _ _ _ _ tail)

def depth (e r : Nat) := min ((e+1)/4) (8*r+5)
def cut (e r : Nat) : Bool := dead (depth e r) (24*r+22) (6*r+4)

theorem cut_sound (e r u : Nat) (hr : r<2^e) (hu : u%2^e=r)
    (h : cut e r=true) : ¬ Path (8*u+5) (24*u+22) (6*u+4) := by
  intro hp
  have hru : r≤u := by rw [←hu]; exact Nat.mod_le _ _
  let k := depth e r
  have hk : k≤8*u+5 := by dsimp [k,depth]; omega
  have h4 : 4*k≤e+1 := by dsimp [k,depth]; omega
  have hpow : 2^(e+1)=16^k*2^(e+1-4*k) := by
    have hs : e+1=4*k+(e+1-4*k) := by omega
    calc
      2^(e+1) = 2^(4*k+(e+1-4*k)) := congrArg (2^·) hs
      _ = _ := by rw [Nat.pow_add,Nat.pow_mul]
  have hsplit : u=r+2^e*(u/2^e) := by have hh := Nat.mod_add_div u (2^e); omega
  let t := 2^(e+1-4*k)*(u/2^e)
  have hdiff : 2*u=2*r+16^k*t := by
    dsimp [t]; rw [←Nat.mul_assoc, ←hpow,Nat.pow_succ]
    calc
      2*u = 2*(r+2^e*(u/2^e)) := congrArg (2*·) hsplit
      _ = _ := by rw [Nat.mul_add]; ac_rfl
  have hp1 : 24*u+22=(24*r+22)+16^k*(12*t) := by
    have hh : 12*(2*u)=12*(2*r+16^k*t) := congrArg (12*·) hdiff
    rw [Nat.mul_add] at hh
    have hh1 : 12*(2*u)=24*u := by omega
    have hh2 : 12*(2*r)=24*r := by omega
    have hh3 : 12*(16^k*t)=16^k*(12*t) := by ac_rfl
    omega
  have hy1 : 6*u+4=(6*r+4)+16^k*(3*t) := by
    have hh : 3*(2*u)=3*(2*r+16^k*t) := congrArg (3*·) hdiff
    rw [Nat.mul_add] at hh
    have hh1 : 3*(2*u)=6*u := by omega
    have hh2 : 3*(2*r)=6*r := by omega
    have hh3 : 3*(16^k*t)=16^k*(3*t) := by ac_rfl
    omega
  have htake := path_take hp k hk
  rw [hp1,hy1] at htake
  exact dead_sound h (path_lower k _ _ _ _ htake)

def cover : Nat → Nat → Nat → Nat → Bool
  | 0,e,r,N => (N≤r) || cut e r
  | f+1,e,r,N => (N≤r) || cut e r || (cover f (e+1) r N && cover f (e+1) (r+2^e) N)

theorem cover_sound (f e r N u : Nat) (hr : r<2^e) (hu : u%2^e=r) (hN : u<N)
    (h : cover f e r N=true) : ¬ Path (8*u+5) (24*u+22) (6*u+4) := by
  have hru : r≤u := by rw [←hu]; exact Nat.mod_le _ _
  induction f generalizing e r with
  | zero => simp [cover,show ¬N≤r by omega] at h; exact cut_sound e r u hr hu h
  | succ f ih =>
    simp [cover,show ¬N≤r by omega] at h
    rcases h with hcut|⟨hl,hh⟩
    · exact cut_sound e r u hr hu hcut
    · have hpow : 2^(e+1)=2*2^e := by rw [Nat.pow_succ]; omega
      have hmod : (u%2^(e+1))%2^e=r := by
        rw [Nat.mod_mod_of_dvd u (by rw [hpow]; exact ⟨2,by omega⟩),hu]
      have hlt : u%2^(e+1)<2^(e+1) := Nat.mod_lt _ (Nat.pow_pos (by decide))
      have hpowpos : 0<2^e := Nat.pow_pos (by decide)
      have hcases : u%2^(e+1)=r ∨ u%2^(e+1)=r+2^e := by
        have hd := Nat.mod_add_div (u%2^(e+1)) (2^e)
        have hquot : (u%2^(e+1))/2^e≤1 := by
          have hlt2 : u%2^(e+1)<2*2^e := by simpa only [←hpow] using hlt
          have hlt3 := (Nat.div_lt_iff_lt_mul hpowpos).mpr hlt2
          omega
        have hzero := Nat.zero_le ((u%2^(e+1))/2^e)
        rcases (show (u%2^(e+1))/2^e=0 ∨ (u%2^(e+1))/2^e=1 by omega) with hz|hone
        · rw [hz,Nat.mul_zero,Nat.add_zero,hmod] at hd; exact Or.inl hd.symm
        · rw [hone,Nat.mul_one,hmod] at hd; exact Or.inr hd.symm
      rcases hcases with h0|h1
      · exact ih (e+1) r (by omega) h0 hl (by rw [←h0]; exact Nat.mod_le _ _)
      · exact ih (e+1) (r+2^e) (by omega) h1 hh (by rw [←h1]; exact Nat.mod_le _ _)

#print axioms dead_sound
#print axioms cut_sound
#print axioms cover_sound
end BB429Q0Macro
