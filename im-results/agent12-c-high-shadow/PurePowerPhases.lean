import PurePowerStopData
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12PureFan

private theorem pow_ge_linear (n : Nat) : n+2≤2^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- Closed right coordinate and uniform height bound for every power-fan
    branch, including the exceptional a=1 member. -/
theorem bounce_geometry (j y v d a k : Nat)
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (hv : v%2=1-(2*j+3+y)%2)
    (hd : 1≤d) (hdv : 2*d+1≤v)
    (ha : a+2+(2*j+3+y)%2=4^d)
    (hw : 2*k+a+7+3*(v-1-2*d)=2*j+3+2*y) :
    let o := (2*j+3+y)%2
    let h := (v-1-2*d)/2
    k+j+4+2*o+3*h+2^(2*d-1)=2^v ∧ y≤2*k+1 := by
  dsimp only
  let o := (2*j+3+y)%2
  let n := v-1-2*d
  let p := 4^d
  let h := n/2
  change 2*j+3+y+o=2^v at hQ
  change v%2=1-o at hv
  change a+2+o=p at ha
  change 2*k+a+7+3*n=2*j+3+2*y at hw
  have hn : n=2*h+o := by dsimp [n,h]; omega
  have hp : 4≤p := Nat.pow_le_pow_right (by decide : 0<4) hd
  have hp2 : p=2*2^(2*d-1) := by
    dsimp [p]
    calc
      4^d = 2^(2*d) := by rw [Nat.pow_mul]
      _ = 2^(2*d-1+1) := by congr 1; omega
      _ = 2*2^(2*d-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  have hpow : 2^v=2^(n+1)*p := by
    dsimp [p]
    rw [←show 2^2=4 by decide,←Nat.pow_mul,←Nat.pow_add]
    congr 1
    dsimp [n]
    omega
  have hgap := Nat.mul_le_mul_right p (pow_ge_linear n)
  rw [←hpow,Nat.add_mul] at hgap
  have hgap2 := Nat.mul_le_mul_left n hp
  have hi : 2*p+3*n≤2^v := by omega
  change k+j+4+2*o+3*h+2^(2*d-1)=2^v ∧ y≤2*k+1
  constructor <;> omega

/-- Truncated binary powers avoid constructing a 2^e with e itself
    exponentially large in the pure-power stopping parameter. -/
def powResidue (b e : Nat) : Nat := if b≤e then 0 else 2^e

def phaseA (b o d : Nat) : Int := (powResidue b (2*d):Int)-2-o

def phaseK (b : Nat) (J : Int) (o d h : Nat) : Int := -(J+1+2*(o:Int)+3*(h%2^b:Nat)+powResidue b (2*d-1))

private theorem residue_dvd (b e : Nat) :
    ((2^b:Nat):Int) ∣ ((2^e:Nat):Int)-(powResidue b e:Int) := by
  unfold powResidue
  by_cases h : b≤e
  · simp only [ite_eq_left h,Int.natCast_zero,Int.sub_zero]
    exact Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 h)
  · simp [h]

private theorem mod_dvd (b h : Nat) :
    ((2^b:Nat):Int) ∣ (h:Int)-(h%2^b:Nat) := by
  have ht := Nat.mod_add_div h (2^b)
  have he : (h:Int)-(h%2^b:Nat)=((2^b:Nat):Int)*(h/2^b:Nat) := by
    have he2 : ((2^b*(h/2^b):Nat):Int)=((2^b:Nat):Int)*(h/2^b:Nat) := by push_cast; rfl
    omega
  rw [he]
  exact Int.dvd_mul_right _ _

/-- The phase is an exact signed modular shadow of any bounce parent.
    Its computation depends only on b, parity, and bounded phase data. -/
theorem bounce_phase (b j y v d a k : Nat) (J : Int)
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (hv : v%2=1-(2*j+3+y)%2)
    (hd : 1≤d) (hdv : 2*d+1≤v)
    (ha : a+2+(2*j+3+y)%2=4^d)
    (hw : 2*k+a+7+3*(v-1-2*d)=2*j+3+2*y)
    (hb : b≤v) (hJ : ((2^b:Nat):Int)∣(j:Int)+3-J) :
    let o := (2*j+3+y)%2
    let h := (v-1-2*d)/2
    ((2^b:Nat):Int)∣(a:Int)-phaseA b o d ∧
      ((2^b:Nat):Int)∣(k:Int)-phaseK b J o d h := by
  dsimp only
  let o := (2*j+3+y)%2
  let h := (v-1-2*d)/2
  have hh := (bounce_geometry j y v d a k hQ hv hd hdv ha hw).1
  change k+j+4+2*o+3*h+2^(2*d-1)=2^v at hh
  have hdivQ : 2^b∣2^v := Nat.pow_dvd_pow 2 hb
  have hiQ : ((2^b:Nat):Int)∣((2^v:Nat):Int) := Int.ofNat_dvd.mpr hdivQ
  have hdivK := Int.dvd_sub hiQ hJ
  have hiK : ((2^b:Nat):Int)∣(k:Int)+J+1+2*(o:Int)+3*(h:Int)+((2^(2*d-1):Nat):Int) := by
    have he : ((2^v:Nat):Int)-((j:Int)+3-J) = (k:Int)+J+1+2*(o:Int)+3*(h:Int)+((2^(2*d-1):Nat):Int) := by omega
    rwa [he] at hdivK
  have hrK := residue_dvd b (2*d-1)
  have hhK := Int.dvd_mul_of_dvd_right (b:=3) (mod_dvd b h)
  have hK := Int.dvd_sub (Int.dvd_sub hiK hrK) hhK
  have hA := residue_dvd b (2*d)
  change a+2+o=4^d at ha
  have hap : 4^d=2^(2*d) := by rw [Nat.pow_mul]
  rw [hap] at ha
  constructor
  · have he : (a:Int)-phaseA b o d=((2^(2*d):Nat):Int)-(powResidue b (2*d):Int) := by unfold phaseA; omega
    rw [he]; exact hA
  · have he : (k:Int)-phaseK b J o d h =
      ((k:Int)+J+1+2*(o:Int)+3*(h:Int)+((2^(2*d-1):Nat):Int)-
        (((2^(2*d-1):Nat):Int)-(powResidue b (2*d-1):Int)))-
        3*((h:Int)-(h%2^b:Nat)) := by unfold phaseK; omega
    rw [he]; exact hK

/-- Every high-exponent branch shares one of at most 2^b tail phases. -/
theorem tail_phase (b o d h : Nat) (J : Int) (hd : b+1≤2*d) :
    phaseA b o d= -2-(o:Int) ∧
    phaseK b J o d h= -(J+1+2*(o:Int)+3*(h%2^b:Nat)) := by
  simp [phaseA,phaseK,powResidue,show b≤2*d by omega,show b≤2*d-1 by omega]

/-- Positive-index pure stops supply a shifted low-bit shadow at precision
    as high as r+2m+2. This is exponentially larger than r. -/
theorem high_shift (b j m y v : Nat) (hm : 1≤m)
    (hs : y+j+3*m+5=2^(2*m+2)*(j+3))
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (hb : b≤v%(2*m+2)+(2*m+2)) (hbv : b+4≤v) :
    ((2^b:Nat):Int)∣(j:Int)+3-(powResidue b (v%(2*m+2)):Int) ∧
    6*2^b≤y := by
  let r := v%(2*m+2)
  obtain ⟨_,_,_,_,_,hheight,hJ,hdvd⟩ := high_pure_data j m y v hm hs hQ
  change 2^r≤j+3 at hJ
  change 2^(r+(2*m+2))∣j+3-2^r at hdvd
  have hdvd' := Nat.dvd_trans (Nat.pow_dvd_pow 2 hb) hdvd
  have hi : ((2^b:Nat):Int)∣(j:Int)+3-((2^r:Nat):Int) := by
    have hh : ((j+3-2^r:Nat):Int)=(j:Int)+3-((2^r:Nat):Int) := by omega
    rw [←hh]
    exact Int.ofNat_dvd.mpr hdvd'
  have hp := residue_dvd b r
  have he : (j:Int)+3-(powResidue b r:Int) = ((j:Int)+3-((2^r:Nat):Int))+(((2^r:Nat):Int)-(powResidue b r:Int)) := by omega
  constructor
  · change ((2^b:Nat):Int)∣(j:Int)+3-(powResidue b r:Int)
    rw [he]
    exact Int.dvd_add hi hp
  · have hle : 2^(b+3)≤2^(v-1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_add] at hle
    omega

private theorem power_ge_triple (v : Nat) (hv : 4≤v) : 3*v≤2^v := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases h : 4≤v
    · rw [Nat.pow_succ]; have := ih h; omega
    · have hv4 : v=3 := by omega
      subst v; decide

/-- Exact signed phase of the exceptional zero-left parent. -/
theorem zero_phase (b j y v k : Nat) (J : Int)
    (hQ : 2*j+3+y=2^v) (hv : v%2=1) (hv4 : 4≤v)
    (hw : 2*k+3*v=2*j+3+2*y)
    (hb : b≤v) (hJ : ((2^b:Nat):Int)∣(j:Int)+3-J) :
    ((2^b:Nat):Int)∣(k:Int)+J+3*(v/2%2^b:Nat) ∧ y≤2*k := by
  have he : k+j+3+3*(v/2)=2^v := by omega
  have hiQ : ((2^b:Nat):Int)∣((2^v:Nat):Int) := Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 hb)
  have hiK := Int.dvd_sub hiQ hJ
  have hmod := Int.dvd_mul_of_dvd_right (b:=3) (mod_dvd b (v/2))
  have hh := Int.dvd_sub hiK hmod
  have he' : (k:Int)+J+3*(v/2%2^b:Nat) = ((2^v:Nat):Int)-((j:Int)+3-J)-3*((v/2:Nat):Int)+3*(v/2%2^b:Nat) := by omega
  constructor
  · rw [he']
    have hx : ((2^v:Nat):Int)-((j:Int)+3-J)-3*((v/2:Nat):Int)+3*(v/2%2^b:Nat) = ((2^v:Nat):Int)-((j:Int)+3-J)-3*(((v/2:Nat):Int)-(v/2%2^b:Nat)) := by omega
    rw [hx]
    exact hh
  · have hpow := power_ge_triple v hv4
    omega

#print axioms bounce_geometry
#print axioms bounce_phase
#print axioms tail_phase
#print axioms high_shift
#print axioms zero_phase
end BB6.Agent12PureFan
