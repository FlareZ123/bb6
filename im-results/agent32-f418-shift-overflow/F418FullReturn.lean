import F418NormalPath
import F418RecoveryCore

/-! Complete pure checkpoint return classification, including recovery. -/
namespace BB6.Agent32F418.RecoveryCore
open Arithmetic EventSystem State ReturnBounds

namespace Word

def steps : Word → Nat
  | last _ => 1
  | more _ t => t.steps+1

def lastJ : Word → Nat
  | last r => 2*r+1
  | more _ t => t.lastJ

@[simp] theorem E_last (r : Nat) : (last r).E=5*r+5 := by simp [E,e,U]
@[simp] theorem E_more (r : Nat) (t : Word) : (more r t).E=5*r+5+t.E := by simp [E,e,U]; omega

theorem e_lastJ (b : Word) : b.e=(5*b.lastJ+1)/2 := by
  induction b with
  | last r => simp [e,lastJ]; omega
  | more r t ih => exact ih

theorem lastJ_odd (b : Word) : b.lastJ%2=1 := by
  induction b with
  | last r => simp [lastJ]
  | more r t ih => exact ih

theorem value_pos (b : Word) : 0<b.value := by
  cases b with
  | last r => exact Nat.two_pow_pos _
  | more r t => exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem oddChain (b : Word) : OddChain b.value b.lastJ := by
  induction b with
  | last r => exact OddChain.last _ (lastJ_odd (last r))
  | more r t ih => exact OddChain.more _ _ _ (by omega) t.value_pos ih

theorem of_oddChain {N j : Nat} (h : OddChain N j) : ∃ b : Word, b.value=N ∧ b.lastJ=j := by
  induction h with
  | last j hj =>
    refine ⟨last (j/2),?_,?_⟩ <;> simp [value,lastJ,show 2*(j/2)+1=j by omega]
  | more j Q k hj hQ hc ih =>
    obtain ⟨t,ht,hj'⟩ := ih
    exact ⟨more (j/2) t,by simp [value,ht,show 2*(j/2)+1=j by omega],hj'⟩

theorem episode_exact (b : Word) (n w : Nat) :
    iterate b.steps (shift2 b.value 1 n w) = some (reg1 (n*2^b.E+b.C) (w+b.E)) := by
  induction b generalizing n w with
  | last r =>
    have hj : (2*r+1)%2≠0 := by omega
    have he : (5*(2*r+1)+1)/2=5*r+3 := by omega
    have hs : splitOdd (2^(2*r+1))=(2*r+1,0) := by simpa using splitOdd_factor (2*r+1) 0
    simp [steps,value,iterate,advance,hs,hj,he,shift2OrReg1,Prefix.reset1_affine,C,Nat.add_assoc]
  | more r t ih =>
    have hj : (2*r+1)%2≠0 := by omega
    have he : (5*(2*r+1)+1)/2=5*r+3 := by omega
    have hpos : t.value≠0 := Nat.ne_of_gt t.value_pos
    simp only [steps,iterate,advance,value,splitOdd_factor,if_neg hj,he,shift2OrReg1,
      if_neg hpos,Option.bind_some]
    rw [ih,Prefix.reset1_affine]
    simp only [C,E_more,Option.some.injEq,State.reg1.injEq]
    refine ⟨?_,?_⟩
    · rw [Nat.add_mul,Nat.mul_assoc n,←Nat.pow_add,Nat.mul_assoc (2^(2*r+1+2)-1),←Nat.pow_add]
      simp only [show 5*r+3+2+t.E=5*r+5+t.E by omega,
        show 2*r+1+2=2*r+3 by omega,Nat.add_assoc]
    · omega

theorem gap_exact (b : Word) (W : Nat) :
    gap (2^W*2^b.E+b.C) (W+1+b.E)=2^(W+b.E)-b.C := by
  unfold gap
  rw [←Nat.pow_add,show W+1+b.E=W+b.E+1 by omega,Nat.pow_succ]
  omega

theorem shift4_exact (b : Word) (W : Nat) :
    iterate (b.steps+1) (Prefix.pure b.value W) = some (shift4 (2^(W+b.E)-b.C) (W+b.E)) := by
  unfold Prefix.pure
  rw [iterate_add,episode_exact]
  simp [iterate,advance,gap_exact,show W+1+b.E-1=W+b.E by omega]

def f (b : Word) := (5*b.e+4)/2

def n4 (b : Word) (W : Nat) := resetRight 0 (2^(W+b.E)+(2^(b.e+1)-1)) b.f

def w4 (b : Word) (W : Nat) := W+b.E+b.f+3

theorem recover_to_phase0 (b : Word) (W : Nat) (hw : b.value<2^W) (he : b.e%2=1) :
    iterate (b.steps+2) (Prefix.pure b.value W)=some (shift2 (b.Q W) 0 (b.n4 W) (b.w4 W)) := by
  rw [show b.steps+2=(b.steps+1)+1 by omega,iterate_add,shift4_exact,gap_factor (width hw)]
  simp [iterate,advance,splitOdd_factor,show b.e%2≠0 by omega,n4,w4,f,Nat.add_assoc] <;> omega

theorem recover_prefix (b : Word) (W : Nat) (hw : b.value<2^W) :
    ∃ p : Prefix, ∃ R : Nat, b.Q W=p.value R := by
  rcases Prefix.prefix_or_oddChain (b.Q W) (Q_pos (width hw)) with h | ⟨last,h⟩
  · exact h
  · obtain ⟨i,hi,hb⟩ := Q_has_even (width hw)
    have hc := Prefix.oddChain_noEven h i hi
    rw [hc] at hb
    contradiction

end Word

end BB6.Agent32F418.RecoveryCore

namespace BB6.Agent32F418.ReturnBounds
open Arithmetic EventSystem State
namespace Prefix

def C0 : Prefix → Nat
  | last r => (2^(2*r+2)-3)*2^(5*r)
  | more r t => (2^(2*r+3)-3)*2^(5*r+3+t.E)+t.C

theorem C0_diff (b : Prefix) : b.C0+2^(b.E-1)=b.C := by
  cases b with
  | last r =>
    simp only [C0,C,E_last]
    rw [show 5*r+2-1=5*r+1 by omega,Nat.pow_succ 2 (5*r),Nat.mul_comm (2^(5*r)) 2,←Nat.add_mul]
    congr 1
    have h : 4≤2^(2*r+2) := by
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤2*r+2)
    omega
  | more r t =>
    simp only [C0,C,E_more]
    rw [show 5*r+5+t.E-1=(5*r+3+t.E)+1 by omega,Nat.pow_succ 2 (5*r+3+t.E),Nat.mul_comm (2^(5*r+3+t.E)) 2]
    have h : 8≤2^(2*r+3) := by exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3≤2*r+3)
    have h' : (2^(2*r+3)-3)+2=2^(2*r+3)-1 := by omega
    rw [Nat.add_right_comm,←Nat.add_mul,h']

theorem reset0_affine (j n e : Nat) :
    resetRight 0 (n+(2^j-1)) e = n*2^(e+2)+(2^(j+2)-3)*2^e := by
  unfold resetRight
  have hx := Nat.two_pow_pos j
  have hp : 2^(j+2)=4*2^j := by rw [Nat.pow_add,Nat.mul_comm]
  have h : 4*(n+(2^j-1))+1+2*0 = 4*n+(2^(j+2)-3) := by rw [hp]; omega
  rw [h,Nat.add_mul,Nat.pow_add (a:=2) (m:=e) (n:=2)]
  change 4*n*2^e+(2^(j+2)-3)*2^e = n*(2^e*4)+(2^(j+2)-3)*2^e
  ac_rfl

theorem episode0_exact (b : Prefix) (Q n w : Nat) :
    iterate b.steps (shift2 (b.value Q) 0 n w) =
      some (reg0 Q (n*2^b.E+b.C0) (w+b.E)) := by
  cases b with
  | last r =>
    have hj : (2*r)%2=0 := by omega
    have he : (5*(2*r)+1)/2=5*r := by omega
    simp [steps,value,iterate,advance,splitOdd_factor,hj,he,reset0_affine,C0,Nat.add_assoc]
  | more r t =>
    have hj : (2*r+1)%2≠0 := by omega
    have he : (5*(2*r+1)+1)/2=5*r+3 := by omega
    have hpos : t.value Q≠0 := Nat.ne_of_gt (value_pos t Q)
    simp only [steps,iterate,advance,value,splitOdd_factor,if_neg hj,he,shift2OrReg1,
      if_neg hpos,Option.bind_some]
    rw [episode_exact,reset0_affine]
    simp only [C0,E_more,Option.some.injEq,State.reg0.injEq]
    refine ⟨trivial,?_,?_⟩
    · rw [Nat.add_mul,Nat.mul_assoc n,←Nat.pow_add,Nat.mul_assoc (2^(2*r+1+2)-3),←Nat.pow_add]
      simp only [show 5*r+3+2+t.E=5*r+5+t.E by omega,
        show 2*r+1+2=2*r+3 by omega,Nat.add_assoc]
    · omega

end Prefix
end BB6.Agent32F418.ReturnBounds

namespace BB6.Agent32F418.RecoveryCore
open Arithmetic EventSystem State ReturnBounds
namespace Word

def outW (b : Word) (W : Nat) (p : Prefix) := b.w4 W+p.E

def outN (b : Word) (W : Nat) (p : Prefix) (R : Nat) := R+gap (b.n4 W*2^p.E+p.C0) (b.outW W p)

theorem recover_exact (b : Word) (W : Nat) (p : Prefix) (R : Nat)
    (hw : b.value<2^W) (he : b.e%2=1) (hq : b.Q W=p.value R) :
    iterate (b.steps+2+p.steps+1) (Prefix.pure b.value W)=some (Prefix.pure (b.outN W p R) (b.outW W p)) := by
  rw [show b.steps+2+p.steps+1=(b.steps+2)+(p.steps+1) by omega,iterate_add,recover_to_phase0 b W hw he,hq]
  simp only [Option.bind_some]
  rw [iterate_add,Prefix.episode0_exact]
  simp [iterate,advance,outN,outW,Prefix.pure]

end Word

inductive PurePath : Nat → Nat → Prop where
  | seed : PurePath 268311341 29
  | normal {b : Prefix} {Q W : Nat} : PurePath (b.value Q) W → PurePath (b.next Q W) (W+b.E+1)
  | recover {b : Word} {W : Nat} {p : Prefix} {R : Nat} :
      PurePath b.value W → b.e%2=1 → b.Q W=p.value R → PurePath (b.outN W p R) (b.outW W p)

theorem purePath_reaches {N W : Nat} (h : PurePath N W) : Reaches EventSystem.seed (Prefix.pure N W) := by
  induction h with
  | seed => exact reaches_iff.mpr ⟨4,Prefix.seed_to_pure⟩
  | @normal b Q W h ih =>
    have hw := (reaches_safe ih).2.2.2.1
    exact reaches_trans ih (reaches_iff.mpr ⟨b.steps+1,Prefix.normal_return_exact b Q W hw⟩)
  | @recover b W p R h he hq ih =>
    have hw := (reaches_safe ih).2.2.2.1
    exact reaches_trans ih (reaches_iff.mpr ⟨b.steps+2+p.steps+1,b.recover_exact W p R hw he hq⟩)

theorem purePath_safe {N W : Nat} (h : PurePath N W) : 0<N ∧ N<2^W := by
  have hs := reaches_safe (purePath_reaches h)
  exact ⟨hs.1,hs.2.2.2.1⟩

theorem none_has_fatal_pure {k N W : Nat} (hp : PurePath N W) (hn : iterate k (Prefix.pure N W)=none) :
    ∃ (b : Word) (V : Nat), PurePath b.value V ∧ b.e%2=0 := by
  induction k using Nat.strongRecOn generalizing N W with
  | ind k ih =>
    obtain ⟨hpos,hwidth⟩ := purePath_safe hp
    rcases Prefix.prefix_or_oddChain N hpos with ⟨p,Q,hq⟩ | ⟨last,ho⟩
    · subst N
      have hx := Prefix.normal_return_exact p Q W hwidth
      obtain ⟨hle,hn'⟩ := Prefix.none_after_some hn hx
      exact ih (k-(p.steps+1)) (by omega) (PurePath.normal hp) hn'
    · obtain ⟨b,hb,_⟩ := Word.of_oddChain ho
      subst N
      by_cases he : b.e%2=0
      · exact ⟨b,W,hp,he⟩
      · have he' : b.e%2=1 := by omega
        obtain ⟨p,R,hq⟩ := b.recover_prefix W hwidth
        have hx := b.recover_exact W p R hwidth he' hq
        obtain ⟨hle,hn'⟩ := Prefix.none_after_some hn hx
        exact ih (k-(b.steps+2+p.steps+1)) (by omega) (PurePath.recover hp he' hq) hn'

theorem seed_none_iff_fatal_pure :
    (∃ k, iterate k EventSystem.seed=none) ↔ ∃ (b : Word) (W : Nat), PurePath b.value W ∧ b.e%2=0 := by
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨_,hn⟩ := Prefix.none_after_some hk Prefix.seed_to_pure
    exact none_has_fatal_pure PurePath.seed hn
  · rintro ⟨b,W,hp,he⟩
    have hj := b.e_lastJ
    have hodd := b.lastJ_odd
    have hf : b.lastJ%4=3 := by omega
    have hr := purePath_reaches hp
    obtain ⟨Q,n,w,ht,_⟩ := fatal_episode b.oddChain hf (reaches_safe hr)
    obtain ⟨k,hk⟩ := reaches_iff.mp (reaches_trans hr ht)
    exact ⟨k+1,by rw [iterate_add,hk]; rfl⟩

#print axioms Word.episode_exact
#print axioms Word.recover_to_phase0
#print axioms Prefix.episode0_exact
#print axioms Word.recover_exact
#print axioms seed_none_iff_fatal_pure

end BB6.Agent32F418.RecoveryCore
