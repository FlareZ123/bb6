import BB429LowGeneral

namespace BB429.LowEvenTerminal
open LowZeroCycle
set_option maxHeartbeats 2000000

def geom (j : Nat) := (16^j-1)/3

theorem geom_eq (j : Nat) : 3*geom j+1=16^j := by
  have h : 16^j%3=1 := by rw [Nat.pow_mod]; simp
  have hp : 0<16^j := Nat.pow_pos (by decide)
  unfold geom
  omega

def total (m j : Nat) := 24*16^m+8*j

def offset (t : Nat) := 16+3*t

def modulus (j t : Nat) := 4*2^t*geom j+1

def parameters (m j t d v : Nat) : Prop :=
  6≤d ∧ d%4=2 ∧ 18≤v ∧ v+geom j*d=total m j ∧
    4*2^t*v=3*total m j+offset t+d

/-- Terminal F burst directly after j complete Oe,F,Oo,F cycles. -/
def TerminalHalt (m j t : Nat) : Prop :=
  ∃ d u, 6≤d ∧ d%4=2 ∧ 15≤u ∧
    3*u+d*16^j+9=72*16^m+d+24*j ∧
    ∃ a b, firstRun t (u,u+12+d*16^j)=some (a,b) ∧ next (a,b)=none

theorem terminal_parameters (m j t : Nat) :
    TerminalHalt m j t ↔ ∃ d v, parameters m j t d v := by
  constructor
  · rintro ⟨d,u,hd,hd4,hu,hcoord,a,b,hfirst,hhalt⟩
    let v := u+3
    have hK := congrArg (fun n : Nat => n*d) (geom_eq j)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm (16^j) d] at hK
    have hlin : v+geom j*d=total m j := by dsimp [v,total]; omega
    obtain ⟨ha,hb⟩ := first_coordinates t _ _ a b hfirst
    have hhalt' := (next_none_iff_halt_line a b).mp hhalt
    have hclock : 4*2^t*v=3*total m j+offset t+d := by
      rw [Nat.mul_assoc,Nat.mul_comm (2^t) v]
      dsimp [v,total,offset]
      omega
    exact ⟨d,v,hd,hd4,by dsimp [v]; omega,hlin,hclock⟩
  · rintro ⟨d,v,hd,hd4,hv,hlin,hclock⟩
    let u := v-3
    have hu : u+3=v := by dsimp [u]; omega
    have hK := congrArg (fun n : Nat => n*d) (geom_eq j)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm (16^j) d] at hK
    have hcoord : 3*u+d*16^j+9=72*16^m+d+24*j := by unfold total at hlin; omega
    have hpos : 0<2^t := Nat.pow_pos (by decide)
    have hvp : v≤2^t*v := by
      simpa using Nat.mul_le_mul_right v (show 1≤2^t by omega)
    let a := 2^t*v-3
    let b := 2*a-1
    have ha : a+3=2^t*v := by dsimp [a]; omega
    have hb : b+1=2*a := by dsimp [b]; omega
    have hfirst : firstRun t (u,u+12+d*16^j)=some (a,b) := by
      apply first_of_coordinates
      · rw [hu,Nat.mul_comm]; exact ha
      · rw [Nat.mul_assoc] at hclock
        unfold total offset at hclock
        omega
    exact ⟨d,u,hd,hd4,by omega,hcoord,a,b,hfirst,(next_none_iff_halt_line a b).mpr hb⟩

theorem burst_mod4 (m j t d v : Nat) (h : parameters m j t d v) : t%4=2 := by
  obtain ⟨hd,hd4,hv,hlin,hclock⟩ := h
  rw [Nat.mul_assoc] at hclock
  unfold total offset at hclock
  omega

theorem parameter_equation (m j t d v : Nat) (h : parameters m j t d v) :
    modulus j t*d+(3*total m j+offset t)=4*2^t*total m j := by
  obtain ⟨hd,hd4,hv,hlin,hclock⟩ := h
  have hm := congrArg (fun n : Nat => (4*2^t)*n) hlin
  rw [Nat.mul_add,← Nat.mul_assoc,hclock] at hm
  unfold modulus
  rw [Nat.add_mul,Nat.one_mul]
  omega

/-- A single generic arithmetic reconstruction for either phase. -/
theorem linear_reconstruction (L K C H : Nat) (hL : 4≤L) (hL4 : L%4=0)
    (hK : 1≤K) (hC : (3*C+H)%4=2)
    (hlarge : (L*K+1)*(H+28)≤C)
    (hmod : ((L-3)*C)%(L*K+1)=H%(L*K+1)) :
    ∃ d v, 6≤d ∧ d%4=2 ∧ 28≤v ∧ v+K*d=C ∧ L*v=3*C+H+d := by
  let M := L*K+1
  let A := (L-3)*C
  have hM : 0<M := by dsimp [M]; omega
  have hLM : L≤M := by
    have hh := Nat.le_mul_of_pos_right L (show 0<K by omega)
    dsimp [M]; omega
  have hCA : C≤A := by exact Nat.le_mul_of_pos_left C (by omega)
  change M*(H+28)≤C at hlarge
  have hbig : H+28*M≤C := by
    rw [Nat.mul_add] at hlarge
    have hh := Nat.le_mul_of_pos_left H hM
    omega
  have hHA : H≤A := by omega
  have hdiv : M*(H/M)≤M*(A/M) := by
    exact Nat.mul_le_mul_left M (Nat.div_le_div_right hHA)
  let d := A/M-H/M
  have hd : M*d+H=A := by
    dsimp [d]; rw [Nat.mul_sub_left_distrib]
    have h1 := Nat.mod_add_div A M
    have h2 := Nat.mod_add_div H M
    change A%M=H%M at hmod
    omega
  have hd6 : 6≤d := by
    by_cases hn : 6≤d
    · exact hn
    · have hm := Nat.mul_le_mul_left M (show d≤5 by omega)
      omega
  have hAC : A+3*C=L*C := by
    have h := congrArg (fun n : Nat => n*C) (show L-3+3=L by omega)
    rw [Nat.add_mul] at h
    exact h
  have hdEq : M*d+3*C+H=L*C := by omega
  have hMeq : M=L*K+1 := rfl
  have hKd : K*d≤C := by
    apply Nat.le_of_mul_le_mul_left (c:=L) _ (by omega)
    rw [hMeq,Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at hdEq
    omega
  let v := C-K*d
  have hv : v+K*d=C := by dsimp [v]; omega
  have hclock : L*v=3*C+H+d := by
    have h := congrArg (fun n : Nat => L*n) hv
    rw [Nat.mul_add] at h
    rw [hMeq,Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at hdEq
    omega
  have hv28 : 28≤v := by
    by_cases hn : 28≤v
    · exact hn
    · have h1 := Nat.mul_le_mul_left L (show v≤27 by omega)
      omega
  have hd4 : d%4=2 := by
    have hM4 : M%4=1 := by unfold M; rw [Nat.add_mod,Nat.mul_mod,hL4]; simp
    have hl : (L*C)%4=0 := by rw [Nat.mul_mod,hL4]; simp
    have hm : (M*d)%4=d%4 := by rw [Nat.mul_mod,hM4]; simp
    omega
  exact ⟨d,v,hd6,hd4,hv28,hv,hclock⟩

theorem modular_necessary (m j t : Nat) (h : TerminalHalt m j t) :
    t%4=2 ∧ (LowGeneral.coefficient t*total m j)%modulus j t=offset t%modulus j t := by
  obtain ⟨d,v,hp⟩ := (terminal_parameters m j t).mp h
  have he := parameter_equation m j t d v hp
  have hc := congrArg (fun n : Nat => n*total m j) (LowGeneral.coeff_eq t)
  rw [Nat.add_mul] at hc
  have h : LowGeneral.coefficient t*total m j=offset t+modulus j t*d := by omega
  exact ⟨burst_mod4 m j t d v hp,by rw [h,Nat.add_mul_mod_self_left]⟩

theorem modular_classification (m j t : Nat) (hj : 1≤j)
    (hlarge : modulus j t*(offset t+28)≤total m j) :
    TerminalHalt m j t ↔
      t%4=2 ∧ (LowGeneral.coefficient t*total m j)%modulus j t=offset t%modulus j t := by
  refine ⟨modular_necessary m j t,?_⟩
  rintro ⟨ht,hmod⟩
  have hK : 1≤geom j := by
    have h := geom_eq j
    have hp : 16≤16^j := Nat.pow_le_pow_right (n:=16) (by decide) hj
    omega
  have hL : 4≤4*2^t := by have h : 0<2^t := Nat.pow_pos (by decide); omega
  have hC : (3*total m j+offset t)%4=2 := by unfold total offset; omega
  obtain ⟨d,v,hd,hd4,hv,hl,hclock⟩ := linear_reconstruction (4*2^t) (geom j) (total m j) (offset t)
    hL (by omega) hK hC hlarge hmod
  exact (terminal_parameters m j t).mpr ⟨d,v,hd,hd4,by omega,hl,hclock⟩

private theorem scale_ge (m : Nat) : 16*m≤16^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have hp : 0<16^m := Nat.pow_pos (by decide)
    omega

theorem terminal_source (m j t : Nat) (h : TerminalHalt m j t) :
    ∃ d a b, 6≤d ∧ d%4=2 ∧
      run (4*m+4*j+3+t) (0,72*16^m+d-(12*m+6))=some (a,b) ∧ next (a,b)=none := by
  obtain ⟨d,u,hd,hd4,hu,hcoord,a,b,hfirst,hhalt⟩ := h
  let X := 16^m
  let u0 := 24*X-3
  let W := 72*X+d-(12*m+6)
  let D := d*16^j
  have hX := scale_ge m
  have hpos : 0<X := Nat.pow_pos (by decide)
  have hu0 : u0+3=3*2^(4*m+3) := by
    rw [Nat.pow_add,Nat.pow_mul]
    change u0+3=3*(X*8)
    dsimp [u0]; omega
  have hB : firstRun (4*m+3) (0,W)=some (u0,u0+12+d) := by
    apply first_of_coordinates
    · simpa using hu0
    · dsimp [u0,W]; omega
  have hrun := first_is_run _ _ _ _ _ hB
  have hc : 3*u0+d+24*j=3*u+D := by dsimp [u0,D]; omega
  have hp : (u0+1)%4=d%4 := by dsimp [u0]; omega
  obtain ⟨hcycles,_,_⟩ := LowBoundary.cycles_to_boundary j u0 d u hd (by omega) hp hc hu
  have hlast := first_is_run _ _ _ _ _ hfirst
  refine ⟨d,a,b,hd,hd4,?_,hhalt⟩
  change run (4*m+4*j+3+t) (0,W)=some (a,b)
  rw [show 4*m+4*j+3+t=(4*m+3)+4*j+t by omega,run_add,run_add,hrun]
  simp only [Option.bind_some]
  change (run (4*j) (LowReturnBand.phase u0 d)).bind (run t)=some (a,b)
  rw [hcycles]
  exact hlast

#print axioms terminal_parameters
#print axioms modular_classification
#print axioms terminal_source
end BB429.LowEvenTerminal
