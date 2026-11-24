import Std
import Lean.Elab.Tactic.Omega

namespace CapSieve

def P (k : Nat) : Nat := 5 * 2^k

/-- Uniform separation between dyadic band scale and the affine correction. -/
theorem guard_base (t : Nat) : (8*t+29)*3^t < 5120*8^t := by
  induction t with
  | zero => decide
  | succ t ih =>
    have h : 3*(8*(t+1)+29) ≤ 8*(8*t+29) := by omega
    have h1 := Nat.mul_le_mul_right (3^t) h
    have h2 := Nat.mul_lt_mul_of_pos_left ih (by decide : 0<8)
    calc
      (8*(t+1)+29)*3^(t+1) = (3*(8*(t+1)+29))*3^t := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ (8*(8*t+29))*3^t := h1
      _ = 8*((8*t+29)*3^t) := by ac_rfl
      _ < 8*(5120*8^t) := h2
      _ = 5120*8^(t+1) := by rw [Nat.pow_succ]; ac_rfl

theorem guard_extra (t h : Nat) : (8*t+29+2*h)*3^t < 5120*8^t*2^h := by
  induction h with
  | zero => simpa using guard_base t
  | succ h ih =>
    have h0 : 8*t+29+2*(h+1) ≤ 2*(8*t+29+2*h) := by omega
    have hh := Nat.mul_le_mul_right (3^t) h0
    calc
      (8*t+29+2*(h+1))*3^t ≤ (2*(8*t+29+2*h))*3^t := hh
      _ = 2*((8*t+29+2*h)*3^t) := by ac_rfl
      _ < 2*(5120*8^t*2^h) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = 5120*8^t*2^(h+1) := by rw [Nat.pow_succ]; ac_rfl

theorem pow8 (t : Nat) : 2^(3*t)=8^t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 3*(t+1)=3*t+3 by omega,Nat.pow_add,ih,Nat.pow_succ]
    rfl

theorem guard (i t : Nat) (h : 4*t+10≤i) : (2*i+9)*3^t < P (i-t) := by
  let a := i-(4*t+10)
  have hi : i=4*t+10+a := by dsimp [a]; omega
  have hsub : i-t=3*t+10+a := by omega
  have hcoef : 2*i+9=8*t+29+2*a := by omega
  rw [hcoef,hsub,P,Nat.pow_add,Nat.pow_add,pow8]
  calc
    (8*t+29+2*a)*3^t < 5120*8^t*2^a := guard_extra t a
    _ = 5*(8^t*2^10*2^a) := by change (5*2^10)*8^t*2^a = _; ac_rfl

structure Packet where
  A : Nat
  D : Nat
  d : Nat
  O : Nat
  deriving Repr

def initial (i : Nat) : Packet := ⟨2,1,0,i+6⟩
def choose (e : Bool) : Nat := if e then 1 else 0

def child (i : Nat) (p : Packet) (e : Bool) : Packet :=
  let d := p.d+choose e
  ⟨2^(choose e)*p.A+2*p.D,3*p.D,d,p.O+3*p.D*(i-d+4)⟩

def Good (i t : Nat) (p : Packet) : Prop :=
  p.D=3^t ∧ p.D<p.A ∧ p.A≤2*p.D ∧ p.d≤t ∧ 9*p.D≤p.O ∧ p.O≤p.D*(2*i+6)

def Rep (i : Nat) (p : Packet) (y : Nat) : Prop := p.D*y+p.O=p.A*P (i-p.d)

theorem initial_good (i : Nat) (hi : 10≤i) : Good i 0 (initial i) := by
  simp [Good,initial]; omega

theorem initial_rep (i y : Nat) (h : y+i+6=10*2^i) : Rep i (initial i) y := by
  simp [Rep,initial,P]; omega

theorem child_good {i t : Nat} {p : Packet} (hg : Good i t p) (hi : t+10≤i) (e : Bool) :
    Good i (t+1) (child i p e) := by
  rcases hg with ⟨hD,hA,hA2,hd,hO,hO2⟩
  have he : choose e≤1 := by cases e <;> decide
  have hlo : 9≤i-(p.d+choose e)+4 := by omega
  have hhi : i-(p.d+choose e)+4≤i+4 := by omega
  have hlow := Nat.mul_le_mul_left (3*p.D) hlo
  have hhigh := Nat.mul_le_mul_left (3*p.D) hhi
  have haux : p.D*(2*i+6)+(3*p.D)*(i+4) ≤ (3*p.D)*(2*i+6) := by
    have h : (2*i+6)+3*(i+4)≤3*(2*i+6) := by omega
    calc
      p.D*(2*i+6)+(3*p.D)*(i+4) = p.D*((2*i+6)+3*(i+4)) := by simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ ≤ p.D*(3*(2*i+6)) := Nat.mul_le_mul_left _ h
      _ = (3*p.D)*(2*i+6) := by ac_rfl
  unfold Good child
  dsimp
  refine ⟨?_,?_,?_,by omega,?_,by omega⟩
  · rw [hD,Nat.pow_succ]; ac_rfl
  · cases e <;> simp [choose] <;> omega
  · cases e <;> simp [choose] <;> omega
  · have heq : 9*(3*p.D)=(3*p.D)*9 := Nat.mul_comm ..
    omega

theorem packet_range {i t : Nat} {p : Packet} {y : Nat}
    (hg : Good i t p) (hr : Rep i p y) (hi : 4*t+10≤i) :
    P (i-p.d)+3<y ∧ y+9≤2*P (i-p.d) := by
  rcases hg with ⟨hD,hA,hA2,hd,hO,hO2⟩
  let Q := P (i-p.d)
  have hpos : 0<p.D := by rw [hD]; exact Nat.pow_pos (by decide)
  have hpow : P (i-t)≤Q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  have hguard := guard i t hi
  have hgap : p.D*(2*i+9)<Q := by rw [hD,Nat.mul_comm]; omega
  have hmul : (p.D+1)*Q≤p.A*Q := Nat.mul_le_mul_right _ (by omega)
  have hupper := Nat.mul_le_mul_right Q hA2
  change p.D*y+p.O=p.A*Q at hr
  change Q+3<y ∧ y+9≤2*Q
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a:=p.D)
    have h : p.D*(Q+3)+p.O ≤ p.D*Q+p.D*(2*i+9) := by
      rw [Nat.mul_add,show 2*i+9=3+(2*i+6) by omega,Nat.mul_add]
      omega
    rw [Nat.add_mul] at hmul
    omega
  · apply Nat.le_of_mul_le_mul_left (c:=p.D) _ hpos
    rw [Nat.mul_add,show p.D*9=9*p.D by ac_rfl,show p.D*(2*Q)=(2*p.D)*Q by ac_rfl]
    omega

theorem child_rep {i : Nat} {p : Packet} {y x : Nat} (e : Bool)
    (hindex : p.d+choose e≤i) (hr : Rep i p y)
    (he : 3*x+3*(i-(p.d+choose e))+12=y+2*P (i-(p.d+choose e))) :
    Rep i (child i p e) x := by
  let k := i-(p.d+choose e)
  have hh : i-p.d=k+choose e := by dsimp [k]; omega
  have hp : P (i-p.d)=2^(choose e)*P k := by rw [hh,P,Nat.pow_add,P]; ac_rfl
  change p.D*y+p.O=p.A*P (i-p.d) at hr
  rw [hp] at hr
  change 3*x+3*k+12=y+2*P k at he
  change (3*p.D)*x+(p.O+3*p.D*(k+4))=(2^(choose e)*p.A+2*p.D)*P k
  have hmul := congrArg (p.D*·) he
  simp only [Nat.mul_add, Nat.add_mul] at hmul ⊢
  rw [show p.D*(3*x)=(3*p.D)*x by ac_rfl,show p.D*(3*k)=(3*p.D)*k by ac_rfl,
    show p.D*12=(3*p.D)*4 by omega,show p.D*(2*P k)=(2*p.D)*P k by ac_rfl] at hmul
  rw [show p.A*(2^(choose e)*P k)=(2^(choose e)*p.A)*P k by ac_rfl] at hr
  omega

#print axioms guard
#print axioms child_good
#print axioms packet_range
#print axioms child_rep
end CapSieve
