import CapSieveCore
namespace CapSieve

/-- Words are recorded newest branch first. -/
def packetFor (i : Nat) : List Bool → Packet
  | [] => initial i
  | e::w => child i (packetFor i w) e

theorem shape (i j : Nat) (w : List Bool) :
    (packetFor i w).A=(packetFor j w).A ∧
    (packetFor i w).D=(packetFor j w).D ∧
    (packetFor i w).d=(packetFor j w).d := by
  induction w with
  | nil => simp [packetFor,initial]
  | cons e w ih =>
    rcases ih with ⟨hA,hD,hd⟩
    simp [packetFor,child,hA,hD,hd]

theorem word_depth (i : Nat) (w : List Bool) : (packetFor i w).D=3^w.length := by
  induction w with
  | nil => rfl
  | cons e w ih => simp [packetFor,child,ih,Nat.pow_succ,Nat.mul_comm]

theorem word_index (i : Nat) (w : List Bool) : (packetFor i w).d≤w.length := by
  induction w with
  | nil => simp [packetFor,initial]
  | cons e w ih =>
    have h : choose e≤1 := by cases e <;> decide
    simp [packetFor,child]; omega

theorem word_good (i : Nat) (w : List Bool) (hi : w.length+10≤i) : Good i w.length (packetFor i w) := by
  induction w with
  | nil => exact initial_good i (by simpa using hi)
  | cons e w ih =>
    have h : w.length+10≤i := by simp at hi; omega
    exact child_good (ih h) h e

def weight : Nat → Nat
  | 0 => 1
  | t+1 => weight t+3^(t+1)

theorem weight_mod3 (t : Nat) : weight t%3=1 := by
  induction t with
  | zero => decide
  | succ t ih => rw [weight,Nat.pow_succ,Nat.add_mod,ih]; simp

theorem weight_formula (t : Nat) : 2*weight t+1=3*3^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [weight,Nat.pow_succ]; omega

theorem offset_shift (i m : Nat) (w : List Bool) (hi : w.length≤i) :
    (packetFor (i+m) w).O=(packetFor i w).O+weight w.length*m := by
  induction w with
  | nil => simp [packetFor,initial,weight]; omega
  | cons e w ih =>
    have hlen : w.length≤i := by simp at hi; omega
    have ih' := ih hlen
    have ⟨_,hD,hd⟩ := shape (i+m) i w
    have hw := word_index i w
    have he : choose e≤1 := by cases e <;> decide
    have hsub : i+m-((packetFor i w).d+choose e)+4 = (i-((packetFor i w).d+choose e)+4)+m := by
      simp at hi; omega
    simp only [packetFor,child,hD,hd,ih',hsub,Nat.mul_add,List.length_cons,weight]
    rw [word_depth i w,Nat.pow_succ]
    grind

theorem pow_period_witness (t : Nat) : ∃ k : Nat, 2^(2*3^t)=1+3^(t+1)*k := by
  induction t with
  | zero => exact ⟨1,by decide⟩
  | succ t ih =>
    obtain ⟨k,hk⟩ := ih
    refine ⟨k+3*3^t*k*k+3*3^t*3^t*k*k*k,?_⟩
    rw [show 2*3^(t+1)=(2*3^t)*3 by rw [Nat.pow_succ,Nat.mul_assoc],Nat.pow_mul,hk]
    simp only [Nat.pow_succ (n:=3)]
    grind

theorem pow_period (t : Nat) : 2^(2*3^t) % (3^(t+1))=1 := by
  obtain ⟨k,hk⟩ := pow_period_witness t
  rw [hk,Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; have := Nat.pow_pos (a:=3) (by decide) (n:=t); omega)

def numerator (i : Nat) (w : List Bool) : Int :=
  ((packetFor i w).A : Int)*(P (i-(packetFor i w).d) : Int)-(packetFor i w).O

theorem numerator_shift (i s : Nat) (w : List Bool) (hw : w.length=s+1) (hi : w.length≤i) :
    numerator (i+2*3^s) w % (3^(s+1) : Nat) =
      (numerator i w+(3^s : Nat)) % (3^(s+1) : Nat) := by
  let M := 2*3^s
  let p := packetFor i w
  have ⟨hA,_,hd⟩ := shape (i+M) i w
  have hO := offset_shift i M w hi
  have hp := word_index i w
  have hindex : i+M-(packetFor i w).d=i-(packetFor i w).d+M := by omega
  have hP : P (i+M-(packetFor i w).d)=P (i-(packetFor i w).d)*2^M := by rw [hindex,P,Nat.pow_add,P,Nat.mul_assoc]
  obtain ⟨q,hq⟩ := pow_period_witness s
  have hq' : 2^M=1+3^(s+1)*q := hq
  let b := weight w.length/3
  have hb : weight w.length=1+3*b := by
    have hm := weight_mod3 w.length
    have hdv := Nat.mod_add_div (weight w.length) 3
    dsimp [b]; omega
  change numerator (i+M) w % (3^(s+1) : Nat) = _
  unfold numerator
  rw [hA,hd,hP,hq',hO,hb]
  simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_pow]
  let d : Int := (3:Int)^s
  let Q : Int := (packetFor i w).A * (P (i-(packetFor i w).d) : Int) * q
  have hM : (M:Int)=2*d := by simp [M,d,Int.natCast_mul,Int.natCast_pow]
  rw [hM]
  simp only [Int.pow_succ]
  change ((packetFor i w).A * ((P (i-(packetFor i w).d) : Int)*(1+(d*3)*q)) -
    ((packetFor i w).O+(1+3*(b:Int))*(2*d))) % (d*3) = _
  have h : (packetFor i w).A * ((P (i-(packetFor i w).d) : Int)*(1+(d*3)*q)) -
      ((packetFor i w).O+(1+3*(b:Int))*(2*d)) =
      ((packetFor i w).A*(P (i-(packetFor i w).d) : Int)-(packetFor i w).O+d)+(d*3)*(Q-2*b-1) := by
    dsimp [Q]; grind
  rw [h,Int.add_mul_emod_self_left]
  rfl

/-- Every multiple of D has exactly one of its three lifts divisible by 3D. -/
theorem lift_unique (D : Nat) (n : Int) (hD : 0<D) (hn : (D:Int)∣n) :
    ∃ l : Nat, l<3 ∧ (n+(D:Int)*l)%(3*(D:Int))=0 ∧
      ∀ k : Nat, k<3 → (n+(D:Int)*k)%(3*(D:Int))=0 → k=l := by
  obtain ⟨q,rfl⟩ := hn
  have hp : (0:Int)<D := by omega
  have equiv (l : Nat) : ((D:Int)*q+(D:Int)*l)%(3*(D:Int))=0 ↔ (q+l)%3=0 := by
    rw [←Int.mul_add,Int.mul_comm 3,Int.mul_emod_mul_of_pos _ _ hp]
    constructor
    · intro h
      exact (Int.mul_eq_zero.mp h).resolve_left (by omega)
    · intro h; rw [h,Int.mul_zero]
  let l : Nat := ((3-q%3)%3).toNat
  have hlt : l<3 := by
    have h1 := Int.emod_nonneg (3-q%3) (by decide : (3:Int)≠0)
    have h2 := Int.emod_lt_of_pos (3-q%3) (by decide : (0:Int)<3)
    dsimp [l]; omega
  have hl : (q+(l:Int))%3=0 := by dsimp [l]; omega
  refine ⟨l,hlt,(equiv l).mpr hl,?_⟩
  intro k hk he
  have hk' := (equiv k).mp he
  omega

#print axioms offset_shift
#print axioms pow_period
#print axioms numerator_shift
#print axioms lift_unique
end CapSieve
