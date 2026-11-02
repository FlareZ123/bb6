import PosEvenForm
namespace BB6.Agent45Deep2
open BB6.Agent1

/-- Two genuine original-map transitions realizing the upper inverse step. -/
theorem upper_pair (b d : Nat) (hb : b % 4 = 0) :
    T b (d+b+10) = some (b+3,d+b+8) ∧
    T (b+3) (d+b+8) = some (2*b+12,d) := by
  have hbe : b % 2 = 0 := by omega
  have hfirst : T b (d+b+10) = some (b+3,d+b+8) := by
    simp only [T, show d+b+10≠0 by omega,
      show d+b+10≠1 by omega, if_false, if_pos hbe]
    congr 1 <;> omega
  have hG : G (b/2+2) (d+b+6) = (2*b+12,d) := by
    rw [G]
    have hlow : ¬ (d+b+6 < 2*(b/2+2)) := by omega
    have hmid : ¬ (d+b+6 ≤ 2*(b/2+2)+1) := by omega
    simp only [hlow, dite_false, hmid, ite_false]
    congr 1 <;> omega
  have hsecond : T (b+3) (d+b+8) = some (2*b+12,d) := by
    have hodd : (b+3)%2≠0 := by omega
    have hthree : d+b+8≠3 := by omega
    have htwo : d+b+8≠2 := by omega
    have hz : d+b+8≠0 := by omega
    have hone : d+b+8≠1 := by omega
    simp only [T,hz,hone,htwo,hthree,hodd,if_false]
    have hp : (b+3)/2+1=b/2+2 := by omega
    have hc : d+b+8-2=d+b+6 := by omega
    rw [hp,hc,hG]
  exact ⟨hfirst,hsecond⟩

/-- Root's non-upper, depth-one G inverse is a genuine two-step transition. -/
theorem middle_pair (u : Nat) (hu : 1≤u) :
    T (6*u-2) (2*u+5) = some (6*u+1,2*u+3) ∧
    T (6*u+1) (2*u+3) = some (8*u+4,3) := by
  have he : (6*u-2)%2=0 := by omega
  have hG : G (3*u+1) (2*u+1)=(8*u+4,3) := by
    rw [G]
    have hlow : 2*u+1<2*(3*u+1) := by omega
    simp only [hlow,dite_true]
    have heq : 3*u+1 - ((2*u+1)/2+1)=2*u := by omega
    have hc : 2*(2*u+1)+3=4*u+5 := by omega
    rw [heq,hc,G]
    have hnot : ¬(4*u+5 < 2*(2*u)) := by omega
    have hmid : ¬(4*u+5 ≤ 2*(2*u)+1) := by omega
    simp only [hnot,dite_false,hmid,ite_false]
    congr 1 <;> omega
  have hfirst : T (6*u-2) (2*u+5) = some (6*u+1,2*u+3) := by
    simp only [T,show 2*u+5≠0 by omega,show 2*u+5≠1 by omega,
      if_false,if_pos he]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hsecond : T (6*u+1) (2*u+3)=some (8*u+4,3) := by
    have hodd : (6*u+1)%2≠0 := by omega
    have hthree : 2*u+3≠3 := by omega
    have htwo : 2*u+3≠2 := by omega
    have hz : 2*u+3≠0 := by omega
    have hone : 2*u+3≠1 := by omega
    simp only [T,hz,hone,htwo,hthree,hodd,if_false]
    have hp : (6*u+1)/2+1=3*u+1 := by omega
    have hc : 2*u+3-2=2*u+1 := by omega
    rw [hp,hc,hG]
  exact ⟨hfirst,hsecond⟩

/-- The index class always lies in the surviving n = 2 (mod 16) sector. -/
def q : Nat → Nat
  | 0 => 1
  | r+1 => 4*q r+1

def index (r:Nat) : Nat := 16*q r+2

def z (r:Nat) : Nat := 2^(index r-(2*r+6))
def a (r:Nat) : Nat := 2^(2*r+2)
def y (r:Nat) : Nat := 2^(index r-4)
def u (r:Nat) : Nat := 28*y r-4*q r-3
def root (r:Nat) : Nat := 14*2^(index r)-2*(index r)-16

theorem q_bound (r:Nat) : r+1 ≤ q r := by
  induction r with
  | zero => decide
  | succ r ih => simp only [q]; omega

theorem q_power (r:Nat) : 3*q r+1 = a r := by
  induction r with
  | zero => decide
  | succ r ih =>
    have he : 2*(r+1)+2=(2*r+2)+2 := by omega
    rw [show a (r+1)=2^(2*(r+1)+2) by rfl,he, Nat.pow_add]
    simp only [q,a] at *
    omega

theorem index_bound (r:Nat) : 2*r+6≤index r := by
  have hb := q_bound r
  simp only [index]
  omega

theorem z_pos (r:Nat) : 1 ≤ z r := by
  simp only [z]
  exact Nat.one_le_pow _ _ (by decide)

theorem y_factor (r:Nat) : y r = a r * z r := by
  have hb := index_bound r
  have he : index r-4 = (2*r+2)+(index r-(2*r+6)) := by omega
  simp only [y,a,z,he,Nat.pow_add]

theorem pow_root (r:Nat) : 2^(index r)=16*y r := by
  have hb:=index_bound r
  have he:index r=4+(index r-4) := by omega
  calc
    2^(index r) = 2^(4+(index r-4)) := congrArg (fun k:Nat => 2^k) he
    _ = 16*2^(index r-4) := by simp [Nat.pow_add]
    _ = 16*y r := rfl

theorem u_identity (r:Nat) :
    1 ≤ u r ∧ u r+4*q r+3=28*a r*z r := by
  have hA := q_power r
  have hfac := y_factor r
  have hz := z_pos r
  have hmul : a r ≤ a r*z r := by
    have hh := Nat.mul_le_mul_left (a r) hz
    simpa using hh
  have hpos : 4*q r+4 ≤ 28*y r := by
    calc
      4*q r+4 ≤ 28*a r := by omega
      _ ≤ 28*(a r*z r) := Nat.mul_le_mul_left 28 hmul
      _ = 28*y r := by rw [hfac]
  have hY : 28*y r =28*a r*z r := by
    rw [hfac]
    simp only [Nat.mul_assoc]
  simp only [u]
  omega

theorem root_identity (r:Nat) : root r=8*u r+4 := by
  have hu := (u_identity r).2
  have hu' : u r+4*q r+3=28*y r := by
    rw [y_factor]
    simpa only [Nat.mul_assoc] using hu
  have hp := pow_root r
  have hn : index r=16*q r+2 := rfl
  simp only [root]
  omega

theorem b0_identity (r:Nat) : 6*u r+10 = 8*a r*(21*z r-1) := by
  have hu := (u_identity r).2
  have hA := q_power r
  have hz := z_pos r
  have hL : 21*z r-1+1=21*z r := by omega
  have hfactor : 8*a r*(21*z r-1)+8*a r=168*a r*z r := by
    calc
      8*a r*(21*z r-1)+8*a r = 8*a r*((21*z r-1)+1) := by simp [Nat.mul_add]
      _ = 8*a r*(21*z r) := by rw [hL]
      _ = 168*a r*z r := by
        calc
          8*a r*(21*z r) = (8*21)*(a r*z r) := by ac_rfl
          _ = 168*a r*z r := by simp [Nat.mul_assoc]
  have hu6 : 6*u r+24*q r+18 =168*a r*z r := by
    calc
      6*u r+24*q r+18 = 6*(u r+4*q r+3) := by omega
      _ = 6*(28*a r*z r) := by rw [hu]
      _ = 168*a r*z r := by
        calc
          6*(28*a r*z r) = (6*28)*(a r*z r) := by ac_rfl
          _ = 168*a r*z r := by simp [Nat.mul_assoc]
  omega

/-- Full-length path, each link consists of two actual T transitions. -/
inductive PairPath : Nat → (Nat × Nat) → (Nat × Nat) → Prop where
  | refl (s : Nat × Nat) : PairPath 0 s s
  | extend {k : Nat} {s x mid fin : Nat × Nat}
      (h : PairPath k s x)
      (h1 : T x.1 x.2 = some mid)
      (h2 : T mid.1 mid.2 = some fin) : PairPath (k+1) s fin

def upper : Nat → Nat → Nat
  | b, 0 => b
  | b, h+1 => 2*upper b h+12

theorem upper_mod (b h:Nat) (hb:b%4=0) : (upper b h)%4=0 := by
  induction h with
  | zero => simpa [upper] using hb
  | succ h ih => simp only [upper]; omega

theorem upper_size (b h:Nat) : upper b h+12=2^h*(b+12) := by
  induction h with
  | zero => simp [upper]
  | succ h ih =>
    calc
      upper b (h+1)+12=2*(upper b h+12) := by simp only [upper]; omega
      _ = 2*(2^h*(b+12)) := by rw [ih]
      _ = 2^(h+1)*(b+12) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem upper_chain (b h d:Nat) (hb:b%4=0) :
    ∃ s : Nat × Nat, PairPath h s (upper b h,d) := by
  induction h generalizing d with
  | zero => exact ⟨(b,d), by simpa [upper] using PairPath.refl (b,d)⟩
  | succ h ih =>
    let v := upper b h
    have hm : v%4=0 := upper_mod b h hb
    obtain ⟨s,hs⟩ := ih (d+v+10)
    obtain ⟨h1,h2⟩ := upper_pair v d hm
    refine ⟨s,?_⟩
    have hpath : PairPath (h+1) s (2*v+12,d) :=
      PairPath.extend hs h1 h2
    simpa [upper,v] using hpath

def coeff (r:Nat) : Nat := 21*z r-1
def seed (r:Nat) : Nat := 4*coeff r-12

theorem seed_properties (r:Nat) :
    seed r%4=0 ∧ seed r+12=4*coeff r := by
  have hZ := z_pos r
  have hcoeff : 20 ≤ coeff r := by simp only [coeff]; omega
  simp only [seed]
  omega

theorem align (r:Nat) : upper (seed r) (2*r+3) = 6*u r-2 := by
  have hseed := (seed_properties r).2
  have hu := (u_identity r).1
  have hb0 := b0_identity r
  have hsz := upper_size (seed r) (2*r+3)
  have hexp : 2^(2*r+3)=2*a r := by
    simp only [a]
    have he:2*r+3=(2*r+2)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  rw [hexp,hseed] at hsz
  have hgoal : upper (seed r) (2*r+3)+12=6*u r+10 := by
    calc
      upper (seed r) (2*r+3)+12 = 2*a r*(4*coeff r) := hsz
      _ = 8*a r*(21*z r-1) := by
        simp only [coeff]
        calc
          2*a r*(4*(21*z r-1)) = (2*4)*(a r*(21*z r-1)) := by ac_rfl
          _ = 8*a r*(21*z r-1) := by simp [Nat.mul_assoc]
      _ = 6*u r+10 := hb0.symm
  omega

/-- Arbitrarily long physically genuine T-predecessor chains in n ≡ 2 (mod 16). -/
theorem critical_two_sector_unbounded (r:Nat) :
    ∃ s : Nat × Nat, PairPath (2*r+4) s (root r,3) := by
  let b := seed r
  let h := 2*r+3
  let d := 2*u r+5
  obtain ⟨s,hs⟩ := upper_chain b h d (seed_properties r).1
  have halign := align r
  have hm := middle_pair (u r) (u_identity r).1
  have hr := root_identity r
  refine ⟨s,?_⟩
  have hpath : PairPath (h+1) s (8*u r+4,3) := by
    have hs' : PairPath h s (6*u r-2,2*u r+5) := by
      simpa only [b,h,d,halign] using hs
    exact PairPath.extend hs' hm.1 hm.2
  simpa only [h,hr] using hpath

#print axioms upper_pair
#print axioms middle_pair
#print axioms critical_two_sector_unbounded
end BB6.Agent45Deep2
