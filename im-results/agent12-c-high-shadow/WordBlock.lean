import Lean
namespace BB6.Agent12WordBlock
structure State where
  a : Int
  m : Nat
  deriving Repr, DecidableEq

def gap (s : State) : Int := (s.m:Int)-s.a
def parity (s : State) : Int := (s.m:Int)%2
def consistent (s : State) : Prop := s.a%2=parity s
def valid (s : State) : Prop := 0≤s.a ∧ 0≤gap s ∧ consistent s

def step (r : Nat) (s : State) : State :=
  let m := s.m+3*r+1
  ⟨(2:Int)^r*(s.a+2+parity s)-(m:Int)-2*parity s,m⟩

def run : List Nat → State → State
  | [],s => s
  | r::rs,s => run rs (step r s)

def shift : List Nat → Nat := List.sum

def massRise : List Nat → Nat
  | [] => 0
  | r::rs => 3*r+1+massRise rs

theorem run_mass (rs : List Nat) (s : State) : (run rs s).m=s.m+massRise rs := by
  induction rs generalizing s with
  | nil => simp [run,massRise]
  | cons r rs ih => simp [run,ih,step,massRise]; omega

theorem step_consistent (r : Nat) (s : State) (hr : 1≤r) : consistent (step r s) := by
  cases r with
  | zero => omega
  | succ r =>
    unfold consistent step
    simp only [Int.pow_succ,parity]
    have h : (2:Int)^r*2*(s.a+2+(s.m:Int)%2)=2*((2:Int)^r*(s.a+2+(s.m:Int)%2)) := by ac_rfl
    rw [h]
    omega

theorem pow_growth (r : Nat) : r+1≤2^r := by
  induction r with
  | zero => decide
  | succ r ih => rw [Nat.pow_succ]; omega

theorem reverse_step (r : Nat) (s : State) (hr : 1≤r)
    (hm : 8*2^r≤s.m) (hp : consistent s)
    (hx : 0≤(step r s).a) (hg : 16≤gap (step r s)) :
    valid s ∧ 2≤s.a ∧ 2≤gap s ∧
    (if r=1 then (s.m:Int)≤2*s.a else 2*s.a<(s.m:Int)) ∧
    gap (step r s)+4≤(2:Int)^r*(gap s+4) := by
  let a := s.a
  let m : Int := s.m
  let o := parity s
  let p := (2:Int)^r
  let d : Int := (3*r+1:Nat)
  let x := (step r s).a
  have ho : 0≤o ∧ o≤1 := by dsimp [o,parity]; omega
  have hm' : 8*p≤m := by dsimp [p,m]; exact_mod_cast hm
  have hd : d≤m := by
    have h := pow_growth r
    dsimp [d,m]
    omega
  have hp0 : 0<p := Int.pow_pos (by decide)
  have hrel : p*(a+2+o)=x+m+d+2*o := by
    dsimp [p,a,o,x,step,parity,m,d]
    omega
  have hga : gap s=m-a := rfl
  have hgb : gap (step r s)=m+d-x := by simp [gap,step,x,m,d]; omega
  have hgap : 16≤m+d-x := by rwa [hgb] at hg
  have hx' : 0≤x := hx
  by_cases h1 : r=1
  · have hp1 : p=2 := by simp [p,h1]
    have hd1 : d=4 := by simp [d,h1]
    rw [hp1] at hrel hm'
    rw [hd1] at hrel hgap
    have ha : 2≤a := by omega
    have hg' : 2≤m-a := by omega
    have hbranch : m≤2*a := by omega
    refine ⟨⟨by omega,by rw [hga]; omega,hp⟩,ha,by rw [hga]; omega,?_,?_⟩
    · simp [h1]; exact hbranch
    · rw [hga,hgb,←show p=(2:Int)^r from rfl,hp1,hd1]
      omega
  · have hr2 : 2≤r := by omega
    have hP4 : 4≤p := by
      dsimp [p]
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) hr2 : 2^2≤2^r)
    have ha : 2≤a := by
      by_cases h : 2≤a
      · exact h
      · exfalso
        have hmul := Int.mul_le_mul_of_nonneg_left (show a+2+o≤4 by omega) (show 0≤p by omega)
        omega
    have hbranch : 2*a<m := by
      by_cases h2 : r=2
      · have hp2 : p=4 := by simp [p,h2]
        have hd2 : d=7 := by simp [d,h2]
        rw [hp2,hd2] at hrel
        rw [hd2] at hgap
        omega
      · have hr3 : 3≤r := by omega
        have hP8 : 8≤p := by
          dsimp [p]
          exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) hr3 : 2^3≤2^r)
        have hmul := Int.mul_le_mul_of_nonneg_right hP8 (show 0≤a+2+o by omega)
        omega
    have hg' : 2≤m-a := by omega
    have hmul := Int.mul_le_mul_of_nonneg_right hP4 (show 0≤m-a+4 by omega)
    refine ⟨⟨by omega,by rw [hga]; omega,hp⟩,ha,by rw [hga]; omega,?_,?_⟩
    · simp [h1]; exact hbranch
    · rw [hga,hgb,←show p=(2:Int)^r from rfl]
      omega
def decode (s : State) : Nat × Nat := (s.a.toNat,(gap s).toNat/2)

theorem decode_coords (s : State) (h : valid s) :
    (decode s).1=s.a.toNat ∧ ((decode s).1:Int)=s.a ∧
    (2:Int)*((decode s).2:Int)=gap s ∧
    (decode s).1+2*(decode s).2=s.m := by
  obtain ⟨ha,hg,hp⟩ := h
  have hpar : gap s % 2=0 := by unfold gap consistent parity at *; omega
  have hA : ((s.a.toNat:Nat):Int)=s.a := Int.toNat_of_nonneg ha
  have hG : (((gap s).toNat:Nat):Int)=gap s := Int.toNat_of_nonneg hg
  refine ⟨rfl,hA,?_,?_⟩
  · change 2*((((gap s).toNat/2):Nat):Int)=gap s
    rw [Int.natCast_ediv,hG]
    omega
  · change s.a.toNat+2*((gap s).toNat/2)=s.m
    have hh : (gap s).toNat%2=0 := by omega
    unfold gap at *
    omega

def EdgeLaw (next : Nat × Nat → Option (Nat × Nat)) : Prop :=
  ∀ (a k x y r : Nat), 1≤r → 2≤a → 1≤k → 8≤y →
    (if r=1 then 2*k≤a else a<2*k) →
    x+2*y=a+2*k+3*r+1 →
    2^r*(a+2+a%2)=2*x+2*y+2*(a%2) → next (a,k)=some (x,y)

theorem source_step_of_law (next : Nat × Nat → Option (Nat × Nat))
    (law : EdgeLaw next) (r : Nat) (s : State) (hr : 1≤r)
    (hm : 8*2^r≤s.m) (hp : consistent s)
    (hx : 0≤(step r s).a) (hg : 16≤gap (step r s)) :
    next (decode s)=some (decode (step r s)) := by
  obtain ⟨hv,ha,hk,hb,_⟩ := reverse_step r s hr hm hp hx hg
  have hv' : valid (step r s) := ⟨hx,by omega,step_consistent r s hr⟩
  obtain ⟨_,ha0,hk0,hm0⟩ := decode_coords s hv
  obtain ⟨_,hx0,hy0,hm1⟩ := decode_coords (step r s) hv'
  let a := (decode s).1
  let k := (decode s).2
  let x := (decode (step r s)).1
  let y := (decode (step r s)).2
  change next (a,k)=some (x,y)
  change (a:Int)=s.a at ha0
  change 2*(k:Int)=gap s at hk0
  change a+2*k=s.m at hm0
  change (x:Int)=(step r s).a at hx0
  change 2*(y:Int)=gap (step r s) at hy0
  change x+2*y=(step r s).m at hm1
  have hpar : parity s=(a%2:Nat) := by unfold consistent at hp; omega
  have hM : x+2*y=a+2*k+3*r+1 := by
    change x+2*y=s.m+3*r+1 at hm1
    omega
  have hA : (2:Int)^r*((a:Int)+2+(a%2:Nat))=2*(x:Int)+2*(y:Int)+2*(a%2:Nat) := by
    have hrel : (2:Int)^r*(s.a+2+parity s)=(step r s).a+((step r s).m:Int)+2*parity s := by simp [step]; omega
    rw [←ha0,hpar,←hx0,←hm1] at hrel
    push_cast at hrel
    simpa [Int.add_assoc,Int.two_mul] using hrel
  have hbranch : if r=1 then 2*k≤a else a<2*k := by
    split
    next h => rw [if_pos h] at hb; unfold gap at hk0; omega
    next h => rw [if_neg h] at hb; unfold gap at hk0; omega
  exact law a k x y r hr (by omega) (by omega) (by omega) hbranch hM (by exact_mod_cast hA)

def runNext (next : Nat × Nat → Option (Nat × Nat)) : Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0,s => s
  | n+1,s => runNext next n (s.bind next)

theorem word_certificate (next : Nat × Nat → Option (Nat × Nat)) (law : EdgeLaw next)
    (rs : List Nat) (s : State) (hr : ∀ r ∈ rs, 1≤r)
    (hm : 8*2^shift rs≤s.m) (hp : consistent s)
    (hx : 0≤(run rs s).a) (hg : 20*(2:Int)^shift rs≤gap (run rs s)+4) :
    valid s ∧ 20≤gap s+4 ∧
    gap (run rs s)+4≤(2:Int)^shift rs*(gap s+4) ∧
    runNext next rs.length (some (decode s))=some (decode (run rs s)) := by
  induction rs generalizing s with
  | nil =>
    simp [run,shift,runNext] at hx hg ⊢
    exact ⟨⟨hx,by omega,hp⟩,by omega⟩
  | cons r rs ih =>
    have hr0 := hr r (by simp)
    have hrs : ∀ t ∈ rs, 1≤t := by intro t ht; exact hr t (by simp [ht])
    have hs : shift (r::rs)=r+shift rs := by simp [shift]
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) (show shift rs≤shift (r::rs) by rw [hs]; omega)
    have hm' : 8*2^shift rs≤(step r s).m := by
      have hmul := Nat.mul_le_mul_left 8 hpow
      simp [step]; omega
    have hp' := step_consistent r s hr0
    have hmul : (2:Int)^shift (r::rs)=(2:Int)^r*(2:Int)^shift rs := by rw [hs,Int.pow_add]
    have hsmall : (2:Int)^shift rs≤(2:Int)^shift (r::rs) := by exact_mod_cast hpow
    have hg' : 20*(2:Int)^shift rs≤gap (run rs (step r s))+4 := by simp only [run] at hg; omega
    have hx' : 0≤(run rs (step r s)).a := hx
    obtain ⟨hv',hbudget,hbound,hrun⟩ := ih (step r s) hrs hm' hp' hx' hg'
    have hpowr := Nat.pow_le_pow_right (by decide : 0<2) (show r≤shift (r::rs) by rw [hs]; omega)
    have hm0 : 8*2^r≤s.m := Nat.le_trans (Nat.mul_le_mul_left 8 hpowr) hm
    obtain ⟨hv,_,_,_,hrel⟩ := reverse_step r s hr0 hm0 hp hv'.1 (by omega)
    have hP : 0<(2:Int)^shift rs := Int.pow_pos (by decide)
    have hh := Int.mul_le_mul_of_nonneg_left hrel (Int.le_of_lt hP)
    have hh' : (2:Int)^shift rs*((2:Int)^r*(gap s+4))=(2:Int)^shift (r::rs)*(gap s+4) := by rw [hmul]; ac_rfl
    rw [hh'] at hh
    have htotal : gap (run (r::rs) s)+4≤(2:Int)^shift (r::rs)*(gap s+4) := by
      exact Int.le_trans hbound hh
    have hbudget0 : 20≤gap s+4 := by
      by_cases h : 20≤gap s+4
      · exact h
      · have hlt := Int.mul_lt_mul_of_pos_left (show gap s+4<20 by omega) (Int.pow_pos (by decide : 0<(2:Int)) : 0<(2:Int)^shift (r::rs))
        rw [Int.mul_comm ((2:Int)^shift (r::rs)) 20] at hlt
        omega
    refine ⟨hv,hbudget0,htotal,?_⟩
    have he := source_step_of_law next law r s hr0 hm0 hp hv'.1 (by omega)
    simp only [List.length_cons,runNext,Option.bind_some,he,run]
    exact hrun

structure Coeff where
  p : Int
  q : Int
  c : Int
  w : Nat
  deriving Repr, DecidableEq

def coeff : List Nat → Nat → Coeff
  | [],_ => ⟨1,0,0,0⟩
  | r::rs,o =>
    let p := (2:Int)^r
    let w := 3*r+1
    let b := p*(2+(o:Int))-(w:Int)-2*(o:Int)
    let v := coeff rs ((o+w)%2)
    ⟨v.p*p,v.p+v.q,v.p*b-v.q*(w:Int)+v.c,w+v.w⟩

def applyCoeff (v : Coeff) (s : State) : State :=
  ⟨v.p*s.a-v.q*(s.m:Int)+v.c,s.m+v.w⟩

theorem run_eq_coeff (rs : List Nat) (s : State) :
    run rs s=applyCoeff (coeff rs (s.m%2)) s := by
  induction rs generalizing s with
  | nil => simp [run,coeff,applyCoeff]
  | cons r rs ih =>
    rw [run,ih]
    have hp : (step r s).m%2=(s.m%2+(3*r+1))%2 := by simp [step,Nat.add_mod,Nat.add_assoc]
    rw [hp]
    simp only [coeff,applyCoeff,step,parity]
    push_cast
    congr 1 <;> grind

theorem coeff_p (rs : List Nat) (o : Nat) : (coeff rs o).p=(2:Int)^shift rs := by
  induction rs generalizing o with
  | nil => simp [coeff,shift]
  | cons r rs ih => simp [coeff,ih,shift,Int.pow_add,Int.mul_comm]

theorem coeff_w (rs : List Nat) (o : Nat) : (coeff rs o).w=massRise rs := by
  induction rs generalizing o with
  | nil => rfl
  | cons r rs ih => simp [coeff,ih,massRise]

theorem block_certificate (next : Nat × Nat → Option (Nat × Nat)) (law : EdgeLaw next)
    (rs : List Nat) (s t : State) (hr : ∀ r ∈ rs, 1≤r)
    (hm : 8*2^shift rs≤s.m) (hp : consistent s)
    (he : applyCoeff (coeff rs (s.m%2)) s=t)
    (hx : 0≤t.a) (hg : 20*(2:Int)^shift rs≤gap t+4) :
    runNext next rs.length (some (decode s))=some (decode t) := by
  rw [←run_eq_coeff] at he
  rw [←he] at hx hg ⊢
  exact (word_certificate next law rs s hr hm hp hx hg).2.2.2

#print axioms reverse_step
#print axioms word_certificate
#print axioms block_certificate
end BB6.Agent12WordBlock
