import CountedOrdinary
import WordBlock

set_option maxHeartbeats 2000000
namespace BB6.Agent12WeightedWord
open BB6.Agent12WordBlock BB6.Agent12Clock BB6.Agent12CountedOrdinary
open BB6.Agent47ThinCounted (Path)

def enc (s : State) : Nat × Nat × Nat := ((decode s).1,(decode s).2,0)

def edgeClock (r : Nat) (s : State) : Int :=
  gap s+r+parity s*(3-3*(r:Int))

def edgeWeight6 (r : Nat) (s : State) : Int :=
  cost6 s.a s.m (step r s).a r (parity s)

def clocks : List Nat → State → Int × Int
  | [],_ => (0,0)
  | r::rs,s => let z := clocks rs (step r s); (edgeClock r s+z.1,edgeWeight6 r s+z.2)

theorem counted_step (r : Nat) (s : State) (hr : 1≤r)
    (hm : 8*2^r≤s.m) (hp : consistent s)
    (hx : 0≤(step r s).a) (hg : 16≤gap (step r s)) :
    ∃ t w, Path t w (enc s) (enc (step r s)) ∧
      (t:Int)=edgeClock r s ∧ 6*(w:Int)=edgeWeight6 r s := by
  obtain ⟨hv,ha,hk,hb,_⟩ := reverse_step r s hr hm hp hx hg
  have hv' : valid (step r s) := ⟨hx,by omega,step_consistent r s hr⟩
  obtain ⟨_,ha0,hk0,hm0⟩ := decode_coords s hv
  obtain ⟨_,hx0,hy0,hm1⟩ := decode_coords (step r s) hv'
  let a := (decode s).1
  let k := (decode s).2
  let x := (decode (step r s)).1
  let y := (decode (step r s)).2
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
  obtain ⟨t,w,hpath,ht,hw⟩ := ordinary_edge a k x y r hr (by omega) (by omega) (by omega) hbranch hM (by exact_mod_cast hA)
  refine ⟨t,w,hpath,?_,?_⟩
  · unfold edgeClock
    rw [←hk0,hpar]
    exact ht
  · unfold edgeWeight6
    rw [←ha0,←hm0,←hx0,hpar]
    exact hw

/-- The exact same endpoint guard as WordBlock.word_certificate now yields
    the actual counted source path, without expanding individual CLine calls. -/
theorem counted_word (rs : List Nat) (s : State) (hr : ∀ r ∈ rs, 1≤r)
    (hm : 8*2^shift rs≤s.m) (hp : consistent s)
    (hx : 0≤(run rs s).a) (hg : 20*(2:Int)^shift rs≤gap (run rs s)+4) :
    valid s ∧ 20≤gap s+4 ∧
    gap (run rs s)+4≤(2:Int)^shift rs*(gap s+4) ∧
    ∃ t w, Path t w (enc s) (enc (run rs s)) ∧
      (t:Int)=(clocks rs s).1 ∧ 6*(w:Int)=(clocks rs s).2 := by
  induction rs generalizing s with
  | nil =>
    simp [run,shift] at hx hg ⊢
    exact ⟨⟨hx,by omega,hp⟩,by omega,0,0,Path.nil _,rfl,rfl⟩
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
    obtain ⟨hv',hbudget,hbound,t,w,hpath,ht,hw⟩ := ih (step r s) hrs hm' hp' hx' hg'
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
    obtain ⟨u,v,hq,hu,hvclock⟩ := counted_step r s hr0 hm0 hp hv'.1 (by omega)
    refine ⟨hv,hbudget0,htotal,u+t,v+w,hq.append hpath,?_,?_⟩
    · simp [clocks]; omega
    · simp [clocks]; omega

-- Build the actual affine forms by a forward fold, exactly as in the C++ table.
def linStep (r : Nat) (o : Int) (a m : Lin) : Lin :=
  let p := (2:Int)^r
  let w := (3*r+1:Nat)
  ⟨p*a.a-m.a,p*a.m-m.m,p*(a.c+2+o)-m.c-w-2*o⟩

def linMass (r : Nat) (m : Lin) : Lin := ⟨m.a,m.m,m.c+(3*r+1:Nat)⟩

def forms : List Nat → Int → Lin → Lin → List (Lin × Lin × Lin × Int × Int)
  | [],_,_,_ => []
  | r::rs,o,a,m =>
    let x := linStep r o a m
    (a,m,x,r,o)::forms rs ((o+(3*r+1:Nat))%2) x (linMass r m)

theorem linStep_eval (r : Nat) (o : Int) (a m : Lin) (A M : Int) :
    (linStep r o a m).eval A M = (2:Int)^r*(a.eval A M+2+o)-(m.eval A M+(3*r+1:Nat))-2*o := by
  simp [linStep,Lin.eval]; grind

theorem linMass_eval (r : Nat) (m : Lin) (A M : Int) :
    (linMass r m).eval A M=m.eval A M+(3*r+1:Nat) := by simp [linMass,Lin.eval]; omega

theorem forms_clock (rs : List Nat) (a m : Lin) (A M : Int) (s : State)
    (ha : a.eval A M=s.a) (hm : m.eval A M=s.m) :
    sumClock A M (forms rs (parity s) a m)=(clocks rs s).2 := by
  induction rs generalizing a m s with
  | nil => rfl
  | cons r rs ih =>
    have hx : (linStep r (parity s) a m).eval A M=(step r s).a := by
      rw [linStep_eval,ha,hm]; simp [step]; omega
    have hmass : (linMass r m).eval A M=(step r s).m := by rw [linMass_eval,hm]; simp [step,Int.add_assoc]
    have hpar : parity (step r s)=(parity s+(3*r+1:Nat))%2 := by simp [parity,step,Int.add_emod,Int.add_assoc]
    simp only [forms,sumClock,clocks,ha,hm,hx,edgeWeight6,←hpar]
    rw [ih _ _ _ hx hmass]

def tableClock (rs : List Nat) (o : Int) : Quad := foldClock (forms rs o ⟨1,0,0⟩ ⟨0,1,0⟩)

theorem tableClock_exact (rs : List Nat) (s : State) :
    (tableClock rs (parity s)).eval s.a s.m=(clocks rs s).2 := by
  rw [tableClock,eval_foldClock]
  apply forms_clock <;> simp [Lin.eval]

/-- Each accepted word has a kernel-verifiable counted path whose raw clock
    is exactly the precomputed six-coefficient polynomial evaluation. -/
theorem block_raw_certificate (rs : List Nat) (s : State) (hr : ∀ r ∈ rs, 1≤r)
    (hm : 8*2^shift rs≤s.m) (hp : consistent s)
    (hx : 0≤(run rs s).a) (hg : 20*(2:Int)^shift rs≤gap (run rs s)+4) :
    ∃ t w, Path t w (enc s) (enc (run rs s)) ∧
      (t:Int)=(clocks rs s).1 ∧ 6*(w:Int)=(tableClock rs (parity s)).eval s.a s.m := by
  rw [tableClock_exact]
  exact (counted_word rs s hr hm hp hx hg).2.2.2

#print axioms counted_step
#print axioms counted_word
#print axioms tableClock_exact
#print axioms block_raw_certificate
end BB6.Agent12WeightedWord
