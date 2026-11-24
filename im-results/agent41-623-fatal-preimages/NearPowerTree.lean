import NearPowerCertificate

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

structure NearState where
  C : Nat
  D : Nat
  k : Nat
  u : Int
  v : Int
  deriving Repr, DecidableEq

def Represents (s : NearState) (x y : Nat) : Prop :=
  2*(x:Int)=(s.C:Int)*3^s.k+s.u ∧ 2*(y:Int)=(s.D:Int)*3^s.k+s.v

def budget (s : NearState) : Nat := 2*s.k+s.D.log2+s.v.natAbs.log2+3

def guarded (s : NearState) : Bool :=
  decide (0<s.k) && lowerBound s.C s.k s.u (2*budget s) && lowerBound s.D s.k s.v 15

private theorem three_le (k : Nat) : 3^k≤2^(2*k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ,show 2*(k+1)=2*k+2 by omega,Nat.pow_add]
    omega

private theorem bit_bound (a : Nat) : a<2^(a.log2+1) := by
  by_cases hz : a=0
  · subst a; decide
  · exact (Nat.log2_lt hz).mp (by omega)

theorem budget_sound (s : NearState) (x y : Nat) (h : Represents s x y) : y<2^(budget s) := by
  have hd := bit_bound s.D
  have hv := bit_bound s.v.natAbs
  have hk := three_le s.k
  have hprod := Nat.mul_le_mul (Nat.le_of_lt hd) hk
  rw [←Nat.pow_add] at hprod
  have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show s.D.log2+1+2*s.k≤budget s-1 by unfold budget; omega)
  have hp' := Nat.pow_le_pow_right (show 0<2 by decide) (show s.v.natAbs.log2+1≤budget s-1 by unfold budget; omega)
  have he : 2^(budget s)=2*2^(budget s-1) := by
    have hpos : 0<budget s := by unfold budget; omega
    conv => lhs; rw [show budget s=budget s-1+1 by omega,Nat.pow_succ]
    omega
  have hcast : ((s.D*3^s.k:Nat):Int)=(s.D:Int)*3^s.k := by rw [Int.natCast_mul,Int.natCast_pow]; rfl
  unfold Represents at h
  rw [←hcast] at h
  omega

theorem guarded_sound {s : NearState} {x y : Nat} (hr : Represents s x y) (h : guarded s=true) :
    0<s.k ∧ 0<s.C ∧ 0<s.D ∧ 2*(y.log2+1)≤x ∧ 14<y := by
  simp only [guarded,Bool.and_eq_true,decide_eq_true_eq] at h
  have hx := lowerBound_sound h.1.2
  have hy := lowerBound_sound h.2
  have hc : 0<s.C := by simp [lowerBound] at h; exact h.1.2.1
  have hd : 0<s.D := by simp [lowerBound] at h; exact h.2.1
  have hy0 : y≠0 := by unfold Represents at hr; omega
  have hlog := (Nat.log2_lt hy0).mpr (budget_sound s x y hr)
  unfold Represents at hr
  exact ⟨h.1.1,hc,hd,by omega,by omega⟩

inductive Sector where
  | LO | LE | RO | RE
  deriving Repr, DecidableEq

def z : Sector → Nat | .LO => 5 | .LE => 2 | .RO => 3 | .RE => 0
def bp : Sector → Nat | .LO | .LE => 0 | .RO | .RE => 1
def dp : Sector → Nat | .LO | .RO => 1 | .LE | .RE => 0
def targetParity : Sector → Nat | .LO | .RE => 1 | .LE | .RO => 0

def leftSector (s : NearState) : Sector := if parityOK s.D s.k s.v 0 then .LE else .LO
def rightSector (s : NearState) : Sector := if parityOK s.D s.k s.v 0 then .RO else .RE

theorem target_sector {s : NearState} {x y : Nat} (hr : Represents s x y) (q : Sector)
    (hp : y%2=targetParity q) : q=leftSector s ∨ q=rightSector s := by
  have hmod : ((s.D:Int)*powMod4 s.k+s.v)%4=2*(y%2:Nat) := by
    have hh := hr.2
    have hmod := congrArg (fun t : Int => t%4) hh
    rw [Int.add_emod,Int.mul_emod (s.D:Int) ((3:Int)^s.k) 4,powMod4_correct] at hmod
    rw [Int.add_emod,Int.mul_emod]
    have hm : powMod4 s.k%4=powMod4 s.k := by unfold powMod4; split <;> decide
    rw [hm]
    omega
  have he : parityOK s.D s.k s.v 0=true ↔ y%2=0 := by
    unfold parityOK
    simp [hmod]
    omega
  cases q <;> unfold targetParity at hp <;> unfold leftSector rightSector <;>
    by_cases hh : parityOK s.D s.k s.v 0=true <;> simp [hh] at * <;> omega

/-- Exact affine reconstruction in compressed coordinates. -/
def restore (s : NearState) (q : Sector) (w : Int) : NearState :=
  let k := s.k-1
  let j := (fastStats s.D k w).1
  let a := s.u-2*j+w
  match q with
  | .LO => ⟨3*s.C+s.D,s.D,k,a+4,w-6⟩
  | .LE => ⟨3*s.C+s.D,s.D,k,a,w-4⟩
  | .RO => ⟨s.D,3*s.C+s.D,k,w+2,a-6⟩
  | .RE => ⟨s.D,3*s.C+s.D,k,w-2,a-4⟩

def affine (q : Sector) (A b a d : Nat) : Prop :=
  match q with
  | .LO => a=A+b+2 ∧ d+3=b
  | .LE => a=A+b ∧ d+2=b
  | .RO => a=b+1 ∧ d+3=A+b
  | .RE => a+1=b ∧ d+2=A+b

theorem restore_sound {s : NearState} {x y A b a d : Nat} {q : Sector} {w : Int}
    (hr : Represents s x y) (hk : 0<s.k) (hD : 0<s.D)
    (hb : 2*(b:Int)=(s.D:Int)*3^(s.k-1)+w) (hj : (x:Int)=(A:Int)+drift b)
    (ha : affine q A b a d) : Represents (restore s q w) a d := by
  have hs := fastStats_correct s.D (s.k-1) b w hD hb
  have hx := hr.1
  have he : (s.C:Int)*3^s.k=3*((s.C:Int)*3^(s.k-1)) := by
    conv => lhs; rw [show s.k=s.k-1+1 by omega,Int.pow_succ,←Int.mul_assoc,Int.mul_comm _ (3:Int)]
  rw [he] at hx
  cases q <;> simp only [affine] at ha <;>
    simp only [restore,hs,Prod.fst,Represents,Int.natCast_add,Int.natCast_mul,Int.add_mul,Int.mul_assoc] <;>
    omega

def rejectParity (s : NearState) (q : Sector) : Bool :=
  parityOK s.C s.k s.u 1 || parityOK s.D s.k s.v (1-dp q)

theorem rejectParity_sound {s : NearState} {a d : Nat} {q : Sector}
    (hr : Represents s a d) (ha : a%2=0) (hd : d%2=dp q) : rejectParity s q≠true := by
  intro h
  simp only [rejectParity,Bool.or_eq_true] at h
  rcases h with h|h
  · have hp := parityOK_sound h
    rw [←hr.1] at hp
    omega
  · have hp := parityOK_sound h
    rw [←hr.2] at hp
    cases q <;> simp [dp] at * <;> omega

/-- A fork supplies one residual per parity-compatible sector. A stop can
only serve as an unused child of a gap or parity contradiction. -/
inductive Cert where
  | stop
  | fork (wl wr : Int) (l r : Cert)
  deriving Repr

def sectorOK (s : NearState) (q : Sector) (w : Int) (childOK : Bool) : Bool :=
  gapOK s.D (s.k-1) (z q) (bp q) w s.v ||
    (hitOK s.D (s.k-1) (z q) (bp q) w s.v && (rejectParity (restore s q w) q || childOK))

def check (s : NearState) : Cert → Bool
  | .stop => false
  | .fork wl wr l r => guarded s &&
      sectorOK s (leftSector s) wl (check (restore s (leftSector s) wl) l) &&
      sectorOK s (rightSector s) wr (check (restore s (rightSector s) wr) r)

#print axioms guarded_sound
#print axioms target_sector
#print axioms restore_sound
#print axioms rejectParity_sound
end BB6.Agent41NearPower
