import CapSieveLift
namespace CapSieve

def L (k : Nat) := P k-k-3

def T (k : Nat) := 2*P k-k-6

theorem p_succ (k : Nat) : P (k+1)=2*P k := by simp [P,Nat.pow_succ,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
theorem p_mono {j k : Nat} (h : j≤k) : P j≤P k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)
theorem p_ge (k : Nat) : k+5≤P k := by
  induction k with
  | zero => decide
  | succ k ih => rw [p_succ]; omega

theorem l_add (k : Nat) : L k+k+3=P k := by unfold L; have := p_ge k; omega

theorem t_add (k : Nat) : T k+k+6=10*2^k := by unfold T P; have := p_ge k; unfold P at this; omega

theorem p_nonzero (k : Nat) : P k%3=1 ∨ P k%3=2 := by
  induction k with
  | zero => decide
  | succ k ih => rw [p_succ,Nat.mul_mod]; rcases ih with h|h <;> rw [h] <;> decide

theorem p_adjacent (k : Nat) : P (k+1)%3≠P k%3 := by
  rw [p_succ,Nat.mul_mod]
  rcases p_nonzero k with h|h <;> rw [h] <;> decide

inductive Arc : Nat → Nat → Prop where
  | one : Arc 1 5
  | regular (k r : Nat) (h : r+4≤P k) : Arc (L k+r) (3*r+P k+3)
  | special (k : Nat) : Arc (L k+(P k-2)) (2*P k)

def Safe (j y : Nat) := P j+3<y ∧ y+9≤2*P j

theorem regular_eq (k r : Nat) : 3*(L k+r)+3*k+12=(3*r+P k+3)+2*P k := by
  have := l_add k; omega

theorem safe_arc {j y x : Nat} (hs : Safe j y) (h : Arc x y) :
    ∃ k r, (k=j ∨ k+1=j) ∧ r+4≤P k ∧ x=L k+r ∧ y=3*r+P k+3 := by
  rcases hs with ⟨hl,hh⟩
  cases h with
  | one => have := p_ge j; omega
  | regular k r hr =>
    have hkj : k≤j := by
      by_cases he : k≤j
      · exact he
      · exfalso
        have hm := p_mono (show j+1≤k by omega)
        rw [p_succ] at hm
        omega
    have hjk : j≤k+1 := by
      by_cases he : j≤k+1
      · exact he
      · exfalso
        have hm := p_mono (show k+2≤j by omega)
        rw [show k+2=(k+1)+1 by omega,p_succ,p_succ] at hm
        omega
    exact ⟨k,r,by omega,hr,rfl,rfl⟩
  | special k =>
    by_cases hk : k<j
    · have hm := p_mono (show k+1≤j by omega)
      rw [p_succ] at hm; omega
    · have hm := p_mono (show j≤k by omega); omega

theorem safe_regular {j k y : Nat} (hs : Safe j y) (hk : k=j ∨ k+1=j)
    (hm : y%3=P k%3) : ∃ x, Arc x y ∧ 3*x+3*k+12=y+2*P k := by
  rcases hs with ⟨hl,hh⟩
  have hrange : P k+3≤y ∧ y+9≤4*P k := by
    rcases hk with he|he
    · subst k; omega
    · rw [←he,p_succ] at hl hh; omega
  let r := (y-(P k+3))/3
  have heq : y=3*r+P k+3 := by dsimp [r]; omega
  have hr : r+4≤P k := by omega
  refine ⟨L k+r,?_,?_⟩
  · rw [heq]; exact .regular k r hr
  · rw [heq]; exact regular_eq k r

theorem safe_mod3 {j y : Nat} (hj : 0<j) (hs : Safe j y) :
    (∃ x, Arc x y) ↔ y%3≠0 := by
  constructor
  · rintro ⟨x,h⟩
    obtain ⟨k,r,_,_,_,he⟩ := safe_arc hs h
    rcases p_nonzero k with hm|hm <;> omega
  · intro hm
    let k := j-1
    have hk : k+1=j := by dsimp [k]; omega
    by_cases he : y%3=P j%3
    · obtain ⟨x,h,_⟩ := safe_regular hs (Or.inl rfl) he
      exact ⟨x,h⟩
    · have hneq := p_adjacent k
      rw [hk] at hneq
      have hp := p_nonzero j
      have hq := p_nonzero k
      have he' : y%3=P k%3 := by omega
      obtain ⟨x,h,_⟩ := safe_regular hs (Or.inr hk) he'
      exact ⟨x,h⟩

theorem packet_numerator {i : Nat} {w : List Bool} {y : Nat} (hr : Rep i (packetFor i w) y) :
    numerator i w=(3^w.length : Nat)*(y:Int) := by
  unfold numerator Rep at *
  have h := congrArg (fun n : Nat => (n:Int)) hr
  simp only [Int.natCast_add,Int.natCast_mul] at h
  rw [←h,word_depth]; omega

theorem child_numerator {i : Nat} {w : List Bool} {y : Nat} (hr : Rep i (packetFor i w) y)
    (hi : w.length+1≤i) (e : Bool) :
    numerator i (e::w) = (3^w.length : Nat)*((y:Int)+2*(P (i-((packetFor i w).d+choose e)):Int)-3*((i-((packetFor i w).d+choose e):Nat):Int)-12) := by
  let p := packetFor i w
  let k := i-(p.d+choose e)
  have hd := word_index i w
  have he : choose e≤1 := by cases e <;> decide
  have hh : i-p.d=k+choose e := by dsimp [k,p]; omega
  have hp : P (i-p.d)=2^(choose e)*P k := by rw [hh,P,Nat.pow_add,P]; ac_rfl
  change p.D*y+p.O=p.A*P (i-p.d) at hr
  rw [hp] at hr
  have h := congrArg (fun n : Nat => (n:Int)) hr
  simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow] at h
  change numerator i (e::w) = (3^w.length : Nat)*((y:Int)+2*(P k:Int)-3*(k:Int)-12)
  change ((2^(choose e)*p.A+2*p.D:Nat):Int)*(P k:Int)-((p.O+3*p.D*(k+4):Nat):Int)=_
  simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow]
  have hD : p.D=3^w.length := word_depth i w
  have hDI := congrArg (fun n : Nat => (n:Int)) hD
  simp only [Int.natCast_pow] at hDI
  rw [←hDI]
  grind

theorem child_integral {i : Nat} {w : List Bool} {y : Nat} (hr : Rep i (packetFor i w) y)
    (hi : w.length+1≤i) (e : Bool) :
    numerator i (e::w) % (3^((e::w).length):Nat)=0 ↔ y%3=P (i-((packetFor i w).d+choose e))%3 := by
  rw [child_numerator hr hi e,List.length_cons,Nat.pow_succ,Int.natCast_mul]
  have hp : (0:Int)<(3^w.length:Nat) := by exact_mod_cast Nat.pow_pos (by decide : 0<3)
  rw [Int.mul_emod_mul_of_pos _ _ hp]
  have h := (show (3^w.length:Nat)≠0 from Nat.ne_of_gt (Nat.pow_pos (by decide)))
  constructor
  · intro h0
    have h1 := (Int.mul_eq_zero.mp h0).resolve_left (by omega)
    omega
  · intro h0
    have h1 : ((y:Int)+2*(P (i-((packetFor i w).d+choose e)):Int)-3*((i-((packetFor i w).d+choose e):Nat):Int)-12)%3=0 := by omega
    change (↑(3^w.length) : Int)*(( (y:Int)+2*(P (i-((packetFor i w).d+choose e)):Int)-3*((i-((packetFor i w).d+choose e):Nat):Int)-12)%3)=0
    rw [h1,Int.mul_zero]

inductive Back (i : Nat) : Nat → Nat → Prop where
  | zero : Back i 0 (T i)
  | step {t y x : Nat} : Back i t y → Arc x y → Back i (t+1) x

def Valid (i : Nat) : List Bool → Prop
  | [] => True
  | e::w => Valid i w ∧ numerator i (e::w)%(3^((e::w).length):Nat)=0

theorem back_packet {i t y : Nat} (h : Back i t y) (hi : 4*t+10≤i) :
    ∃ w : List Bool, w.length=t ∧ Valid i w ∧ Rep i (packetFor i w) y := by
  induction h with
  | zero => exact ⟨[],rfl,True.intro,initial_rep i _ (t_add i)⟩
  | @step t y x hb ha ih =>
    obtain ⟨w,hw,hv,hr⟩ := ih (by omega)
    have hg := word_good i w (by omega)
    have hs : Safe (i-(packetFor i w).d) y := packet_range hg hr (by omega)
    obtain ⟨k,r,hk,hrange,hx,hy⟩ := safe_arc hs ha
    have hidx := word_index i w
    have hchoose : ∃ e : Bool, k=i-((packetFor i w).d+choose e) := by
      rcases hk with he|he
      · exact ⟨false,by simpa [choose] using he⟩
      · exact ⟨true,by simp [choose]; omega⟩
    obtain ⟨e,he⟩ := hchoose
    have hre : 3*x+3*(i-((packetFor i w).d+choose e))+12=y+2*P (i-((packetFor i w).d+choose e)) := by
      rw [←he,hx,hy]; exact regular_eq k r
    have hce : choose e≤1 := by cases e <;> decide
    have hRep := child_rep e (by omega) hr hre
    have hNum := packet_numerator (w:=e::w) hRep
    have hz : numerator i (e::w) % (3^((e::w).length):Nat)=0 := by rw [hNum,Int.mul_emod_right]
    exact ⟨e::w,by simp [hw],⟨hv,hz⟩,hRep⟩

theorem valid_packet {i : Nat} {w : List Bool} (hv : Valid i w) (hi : 4*w.length+10≤i) :
    ∃ y, Back i w.length y ∧ Rep i (packetFor i w) y := by
  induction w with
  | nil => exact ⟨T i,Back.zero,initial_rep i _ (t_add i)⟩
  | cons e w ih =>
    rcases hv with ⟨hv,hInt⟩
    have hlen : 4*w.length+10≤i := by simp at hi; omega
    obtain ⟨y,hy,hr⟩ := ih hv hlen
    have hg := word_good i w (by omega)
    have hs : Safe (i-(packetFor i w).d) y := packet_range hg hr hlen
    let k := i-((packetFor i w).d+choose e)
    have hd := word_index i w
    have hchoose : choose e≤1 := by cases e <;> decide
    have hk : k=i-(packetFor i w).d ∨ k+1=i-(packetFor i w).d := by
      dsimp [k]; omega
    have hm := (child_integral hr (by simp at hi; omega) e).mp hInt
    obtain ⟨x,hx,he⟩ := safe_regular hs hk hm
    have hRep := child_rep e (by simp at hi; omega) hr he
    exact ⟨x,Back.step hy hx,hRep⟩

theorem back_iff_valid (i t : Nat) (hi : 4*t+10≤i) :
    (∃ y, Back i t y) ↔ ∃ w : List Bool, w.length=t ∧ Valid i w := by
  constructor
  · rintro ⟨y,h⟩
    obtain ⟨w,hw,hv,_⟩ := back_packet h hi
    exact ⟨w,hw,hv⟩
  · rintro ⟨w,rfl,hv⟩
    obtain ⟨y,hy,_⟩ := valid_packet hv hi
    exact ⟨y,hy⟩

#print axioms safe_mod3
#print axioms child_integral
#print axioms back_iff_valid
end CapSieve
