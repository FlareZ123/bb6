import BB429LowZeroCycle
import BB429LowBoundary
import Lean.Elab.Tactic.Omega

namespace BB429.LowGeneral
open LowZeroCycle
set_option maxHeartbeats 2000000

def geom (j : Nat) := (4*16^j-1)/3

theorem geom_eq (j : Nat) : 3*geom j+1=4*16^j := by
  have h : 16^j%3=1 := by rw [Nat.pow_mod]; simp
  have hp : 0<16^j := Nat.pow_pos (by decide)
  unfold geom
  omega

theorem geom_mod4 (j : Nat) : geom j%4=1 := by
  have h := geom_eq j
  omega

def modulus (j t : Nat) := 4*2^t*geom j+1

def parameters (m j t d v : Nat) : Prop :=
  6≤d ∧ d%4=2 ∧ 28≤v ∧
  v+geom j*d=24*16^m+8*j+6 ∧
  4*2^t*v=72*16^m+d+24*j+30+3*t

/-- Coordinates just before the last odd-even pair, after j complete
    four-step cycles, followed by a halting first-branch burst. -/
def TerminalHalt (m j t : Nat) : Prop :=
  ∃ d u, 6≤d ∧ d%4=2 ∧ d*16^j+19≤u ∧
    3*u+d*16^j+9=72*16^m+d+24*j ∧
    ∃ a b, firstRun t (u+6-d*16^j,u+14+3*(d*16^j))=some (a,b) ∧
      next (a,b)=none

/-- Exact positive-cycle family reduced to two linear equations in d,v. -/
theorem terminal_parameters (m j t : Nat) :
    TerminalHalt m j t ↔ ∃ d v, parameters m j t d v := by
  constructor
  · rintro ⟨d,u,hd,hd4,hu,hcoord,a,b,hfirst,hhalt⟩
    let D := d*16^j
    let v := u+9-D
    have hv : v+D=u+9 := by dsimp [v]; change D+19≤u at hu; omega
    have hK := congrArg (fun n : Nat => n*d) (geom_eq j)
    rw [Nat.add_mul,Nat.one_mul, Nat.mul_assoc,Nat.mul_assoc,Nat.mul_comm (16^j) d] at hK
    change 3*(geom j*d)+d=4*D at hK
    change 3*u+D+9=72*16^m+d+24*j at hcoord
    have hlin : v+geom j*d=24*16^m+8*j+6 := by omega
    obtain ⟨ha,hb⟩ := first_coordinates t _ _ a b hfirst
    have hhalt' := (next_none_iff_halt_line a b).mp hhalt
    have hv' : u+6-D+3=v := by omega
    change a+3=(u+6-D+3)*2^t at ha
    rw [hv',Nat.mul_comm v (2^t)] at ha
    change 2*a+b=2*(u+6-D)+(u+14+3*D)+3*t at hb
    have hclock : 4*2^t*v=72*16^m+d+24*j+30+3*t := by
      rw [Nat.mul_assoc]; omega
    exact ⟨d,v,hd,hd4,by omega,hlin,hclock⟩
  · rintro ⟨d,v,hd,hd4,hv,hlin,hclock⟩
    let D := d*16^j
    let u := v+D-9
    have hu : u+9=v+D := by dsimp [u]; omega
    have hK := congrArg (fun n : Nat => n*d) (geom_eq j)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_assoc,Nat.mul_comm (16^j) d] at hK
    change 3*(geom j*d)+d=4*D at hK
    have hcoord : 3*u+D+9=72*16^m+d+24*j := by omega
    have hpos : 0<2^t := Nat.pow_pos (by decide)
    have hvp : v≤2^t*v := by
      simpa using Nat.mul_le_mul_right v (show 1≤2^t by omega)
    let a := 2^t*v-3
    let b := 2*a-1
    have ha : a+3=2^t*v := by dsimp [a]; omega
    have hb : b+1=2*a := by dsimp [b]; omega
    have hfirst : firstRun t (u+6-D,u+14+3*D)=some (a,b) := by
      apply first_of_coordinates
      · have he : u+6-D+3=v := by omega
        rw [he,Nat.mul_comm]; exact ha
      · rw [Nat.mul_assoc] at hclock
        omega
    exact ⟨d,u,hd,hd4,by omega,hcoord,a,b,hfirst,(next_none_iff_halt_line a b).mpr hb⟩

/-- Single exact Diophantine equation, with no large-counter approximation. -/
theorem parameter_equation (m j t d v : Nat) (h : parameters m j t d v) :
    modulus j t*d+(72*16^m+24*j+30+3*t)=
      4*2^t*(24*16^m+8*j+6) := by
  obtain ⟨hd,hd4,hv,hlin,hclock⟩ := h
  have hm := congrArg (fun n : Nat => (4*2^t)*n) hlin
  rw [Nat.mul_add,← Nat.mul_assoc,hclock] at hm
  unfold modulus
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem burst_mod4 (m j t d v : Nat) (h : parameters m j t d v) : t%4=0 := by
  obtain ⟨hd,hd4,hv,hlin,hclock⟩ := h
  rw [Nat.mul_assoc] at hclock
  omega

theorem pow16_mod9 (j : Nat) : 16^j%9 = 7^(j%3)%9 := by
  let r := j%3
  let q := j/3
  have he : j=r+3*q := (Nat.mod_add_div j 3).symm
  rw [Nat.pow_mod 16 j 9]
  change 7^j%9=7^r%9
  conv => lhs; rw [he,Nat.pow_add,Nat.pow_mul]
  rw [Nat.mul_mod,Nat.pow_mod (7^3)]
  simp

/-- Every cycle count congruent to 2 modulo 3 is impossible, independently
    of scale and terminal burst length. -/
theorem no_two_mod3 (m j t : Nat) (hj : j%3=2) : ¬TerminalHalt m j t := by
  intro h
  obtain ⟨d,v,hp⟩ := (terminal_parameters m j t).mp h
  have ht := burst_mod4 m j t d v hp
  have hP : 2^t%3=1 := by
    have he : t=4*(t/4) := by omega
    rw [he,Nat.pow_mul,Nat.pow_mod]; simp
  have hQ := pow16_mod9 j
  rw [hj] at hQ
  change 16^j%9=4 at hQ
  have hK := geom_eq j
  have hK9 := congrArg (fun n : Nat => n%9) hK
  rw [Nat.add_mod (3*geom j),Nat.mul_mod 3 (geom j),Nat.mul_mod 4 (16^j),hQ] at hK9
  have hK3 : geom j%3=2 := by
    have h := Nat.mod_lt (geom j) (by decide : 0<3)
    have he : geom j%9%3=geom j%3 := by
      exact Nat.mod_mod_of_dvd _ (by decide : 3∣9)
    omega
  have hM : modulus j t%3=0 := by
    unfold modulus
    have h4P : (4*2^t)%3=1 := by omega
    rw [Nat.add_mod,Nat.mul_mod,h4P,hK3]
  have he := parameter_equation m j t d v hp
  have hm := congrArg (fun n : Nat => n%3) he
  rw [Nat.add_mod,Nat.mul_mod (modulus j t),hM] at hm
  have hr : (4*2^t*(24*16^m+8*j+6))%3=1 := by
    have h4P : (4*2^t)%3=1 := by omega
    rw [Nat.mul_mod,h4P]
    have hsum : (24*16^m+8*j+6)%3=1 := by omega
    rw [hsum]
  rw [hr] at hm
  omega

/-- The two coefficients controlling the exact parameter equation. -/
def total (m j : Nat) := 24*16^m+8*j+6

def offset (t : Nat) := 12+3*t

def coefficient (t : Nat) := 4*2^t-3

theorem coeff_eq (t : Nat) : coefficient t+3=4*2^t := by
  have hp : 0<2^t := Nat.pow_pos (by decide)
  unfold coefficient
  omega

theorem modulus_pos (j t : Nat) : 0<modulus j t := by simp [modulus]

theorem modulus_ge (j t : Nat) : 4*2^t≤modulus j t := by
  have h := geom_eq j
  have hQ : 0<16^j := Nat.pow_pos (by decide)
  have hK : 0<geom j := by omega
  have hh := Nat.le_mul_of_pos_right (4*2^t) hK
  unfold modulus
  omega

/-- Any terminal witness implies the modular test, without a size guard. -/
theorem modular_necessary (m j t : Nat) (h : TerminalHalt m j t) :
    t%4=0 ∧ (coefficient t*total m j)%modulus j t = offset t%modulus j t := by
  obtain ⟨d,v,hp⟩ := (terminal_parameters m j t).mp h
  have he := parameter_equation m j t d v hp
  have hc := congrArg (fun n : Nat => n*total m j) (coeff_eq t)
  rw [Nat.add_mul] at hc
  have hB : 72*16^m+24*j+30+3*t=3*total m j+offset t := by unfold total offset; omega
  rw [hB] at he
  change modulus j t*d+(3*total m j+offset t)=4*2^t*total m j at he
  have h : coefficient t*total m j = offset t+modulus j t*d := by omega
  exact ⟨burst_mod4 m j t d v hp, by rw [h,Nat.add_mul_mod_self_left]⟩

/-- For every scale above an explicit threshold, the modular test suffices.
    In particular there is no asymptotic approximation of the guards. -/
theorem modular_sufficient (m j t : Nat)
    (hlarge : modulus j t*(offset t+28)≤total m j)
    (ht : t%4=0)
    (hmod : (coefficient t*total m j)%modulus j t = offset t%modulus j t) :
    TerminalHalt m j t := by
  let L := 4*2^t
  let K := geom j
  let M := modulus j t
  let C := total m j
  let H := offset t
  let A := coefficient t*C
  have hL : 0<L := by dsimp [L]; exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have hM : 0<M := modulus_pos j t
  have hLM : L≤M := modulus_ge j t
  have hMeq : M=L*K+1 := rfl
  have hCoeff : coefficient t+3=L := coeff_eq t
  have hcoeffpos : 0<coefficient t := by
    have hp : 0<2^t := Nat.pow_pos (by decide)
    dsimp [L] at hCoeff
    omega
  have hCA : C≤A := by exact Nat.le_mul_of_pos_left C hcoeffpos
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
    have h := congrArg (fun n : Nat => n*C) hCoeff
    rw [Nat.add_mul] at h
    exact h
  have hdEq : M*d+3*C+H=L*C := by omega
  have hKd : K*d≤C := by
    apply Nat.le_of_mul_le_mul_left (c:=L) _ hL
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
    have hM4 : M%4=1 := by unfold M modulus; rw [Nat.mul_assoc]; omega
    have hC4 : C%4=2 := by unfold C total; omega
    have hH4 : H%4=0 := by unfold H offset; omega
    have hL4 : L%4=0 := by unfold L; omega
    have hl : (L*C)%4=0 := by rw [Nat.mul_mod,hL4]; simp
    have hm : (M*d)%4=d%4 := by rw [Nat.mul_mod,hM4]; simp
    omega
  apply (terminal_parameters m j t).mpr
  refine ⟨d,v,hd6,hd4,hv28,?_,?_⟩
  · exact hv
  · change L*v=72*16^m+d+24*j+30+3*t
    dsimp [C,total,H,offset] at hclock
    omega

/-- An exact, finite modular decision test for every sufficiently large scale. -/
theorem modular_classification (m j t : Nat)
    (hlarge : modulus j t*(offset t+28)≤total m j) :
    TerminalHalt m j t ↔
      t%4=0 ∧ (coefficient t*total m j)%modulus j t = offset t%modulus j t :=
  ⟨modular_necessary m j t, fun h => modular_sufficient m j t hlarge h.1 h.2⟩

private theorem scale_ge (m : Nat) : 16*m≤16^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have hp : 0<16^m := Nat.pow_pos (by decide)
    omega

/-- Actual source-level prepared halting trajectory for every terminal
    arithmetic witness, including arbitrarily many full cycles. -/
theorem terminal_source (m j t : Nat) (h : TerminalHalt m j t) :
    ∃ d a b, 6≤d ∧ d%4=2 ∧
      run (4*m+4*j+5+t) (0,72*16^m+d-(12*m+6))=some (a,b) ∧ next (a,b)=none := by
  obtain ⟨d,u,hd,hd4,hguard,hcoord,a,b,hfirst,hhalt⟩ := h
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
  obtain ⟨hcycles,hphase,heven⟩ := LowBoundary.cycles_to_boundary j u0 d u hd (by omega) hp hc (by change D+19≤u at hguard; omega)
  have hD : 6≤D := by
    have h := Nat.le_mul_of_pos_right d (Nat.pow_pos (a:=16) (n:=j) (by decide))
    omega
  have hpair := LowBoundary.two_step u D hD heven hphase hguard
  have hlast := first_is_run _ _ _ _ _ hfirst
  refine ⟨d,a,b,hd,hd4,?_,hhalt⟩
  change run (4*m+4*j+5+t) (0,W)=some (a,b)
  rw [show 4*m+4*j+5+t=(4*m+3)+4*j+2+t by omega,run_add,run_add,run_add,hrun]
  simp only [Option.bind_some]
  change ((run (4*j) (LowReturnBand.phase u0 d)).bind (run 2)).bind (run t) = some (a,b)
  rw [hcycles]
  simp only [Option.bind_some,LowReturnBand.phase]
  change (run 2 (LowReturnBand.phase u D)).bind (run t)=some (a,b)
  rw [hpair]
  exact hlast

#print axioms terminal_parameters
#print axioms no_two_mod3
#print axioms modular_classification
#print axioms terminal_source

end BB429.LowGeneral
