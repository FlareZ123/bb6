import Raw13Coupled6OneRAHierarchy

namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRACost
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def GoodC (c : Nat) (R S : List Bool) : Prop := ∀ k L,
  run0 p (k+c) (A (false::L) (rep one k ++ R)) =
    some (A (rep zero k ++ true::L) S)

inductive StepsC : Nat → Nat → List Bool → List Bool → Prop where
  | nil (R) : StepsC 0 0 R R
  | cons {n c d R S T} : GoodC c R S → StepsC n d S T → StepsC (n+1) (c+d) R T

theorem splitC {m n c : Nat} {R T : List Bool} (h : StepsC (m+n) c R T) :
    ∃ S a b, a+b=c ∧ StepsC m a R S ∧ StepsC n b S T := by
  induction m generalizing R c with
  | zero => exact ⟨R,0,c,by omega,.nil R,by simpa using h⟩
  | succ m ih =>
    rw [show m+1+n=m+n+1 by omega] at h
    cases h with
    | cons hi hs =>
      obtain ⟨S,a,b,hab,hm,hn⟩ := ih hs
      refine ⟨S,_,b,?_,.cons hi hm,hn⟩
      omega

theorem appendC {m n c d : Nat} {R S T : List Bool} (h : StepsC m c R S) (g : StepsC n d S T) :
    StepsC (m+n) (c+d) R T := by
  induction h with
  | nil R => simpa using g
  | @cons m a b R U S hi hs ih =>
    rw [show m+1+n=m+n+1 by omega,show a+b+d=a+(b+d) by omega]
    exact .cons hi (ih g)

def drainOver (k : Nat) := 6*2^k-3*k-6
def fillOver (k : Nat) := 6*2^k-6

theorem pow_ge (k : Nat) : k+1 ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem fillOver_eq (k : Nat) : 3*k+drainOver k = fillOver k := by
  have := pow_ge k
  unfold drainOver fillOver
  omega

theorem drainOver_succ (k : Nat) : drainOver k+fillOver k+3=drainOver (k+1) := by
  have := pow_ge k
  unfold drainOver fillOver
  rw [Nat.pow_succ]
  omega

def DrainC (k : Nat) : Prop := ∀ (L : List Bool) {c : Nat} {R S : List Bool},
  StepsC (2^k-1) c R S → run0 p (c+drainOver k) (A (rep zero (3*k) ++ L) R) =
    some (A L (rep one (3*k) ++ S))

def FillC (k : Nat) : Prop := ∀ (L : List Bool) {c : Nat} {R S : List Bool},
  StepsC (2^k) c R S → run0 p (c+fillOver k) (A (false::L) (rep one (3*k) ++ R)) =
    some (A (true::L) (rep one (3*k) ++ S))

theorem fillC_of_drain {k : Nat} (hd : DrainC k) : FillC k := by
  intro L c R S hs
  have hp := Nat.two_pow_pos k
  have eq : 2^k=2^k-1+1 := by omega
  rw [eq] at hs
  cases hs with
  | @cons n a b R T S hi hn =>
    have h := hi (3*k) L
    have h' := hd (true::L) hn
    have H := join0 h h'
    rw [←fillOver_eq k]
    rw [show a+b+(3*k+drainOver k)=3*k+a+(b+drainOver k) by omega]
    exact H

theorem drainC_all (k : Nat) : DrainC k := by
  induction k with
  | zero =>
    intro L c R S hs
    cases hs
    rfl
  | succ k ih =>
    intro L c R S hs
    have hp := Nat.two_pow_pos k
    have eq : 2^(k+1)-1=(2^k-1)+2^k := by rw [Nat.pow_succ]; omega
    rw [eq] at hs
    obtain ⟨mid,a,b,hab,hm,hn⟩ := splitC hs
    have ha := ih (false::false::false::L) hm
    have hb := fillC_of_drain ih (false::false::L) hn
    have hc := left_triple L (rep one (3*k) ++ S)
    have h := join0 (join0 ha hb) hc
    have et : a+drainOver k+(b+fillOver k)+3=c+drainOver (k+1) := by rw [←drainOver_succ]; omega
    rw [et] at h
    have e : 3*(k+1)=3*k+3 := by omega
    rw [e,rep_add']
    simpa [rep,zero,one,List.append_assoc] using h

theorem fillC_all (k : Nat) : FillC k := fillC_of_drain (drainC_all k)

theorem overflow_delimiterC (j m c : Nat) {R S : List Bool} (hs : StepsC (2^m) c R S) :
    GoodC (8*(j+1)+c+fillOver m) (rep d1 (j+1) ++ rep one (3*m) ++ R)
         (rep d0 (j+1) ++ rep one (3*m) ++ S) := by
  intro k L
  have h := first_d1 k L (rep d1 j ++ rep one (3*m) ++ R)
  have h' := d1_scan j (true::true::true::(rep zero k ++ true::L)) (rep one (3*m) ++ R)
  have h1 := join0 h (by simpa only [List.append_assoc] using h')
  have h2 := fillC_all m (rep [true,true,true,true] j ++ true::true::true::(rep zero k ++ true::L)) hs
  have h3 := join0 h1 h2
  rw [ones_commute,←rep11_double] at h3
  have h4 := join0 h3 (left_pairs (2*(j+1)) (rep zero k ++ true::L) (rep one (3*m) ++ S))
  rw [show k+4+4*j+(c+fillOver m)+2*(2*(j+1))=k+(8*(j+1)+c+fillOver m) by omega] at h4
  simpa [rep,pair_double,List.append_assoc] using h4

theorem good_zeroC (R : List Bool) : GoodC 8 (d0 ++ R) (d1 ++ R) := by
  intro k L
  have h := start_scan k L (true::false::true::R) false
  have f (X : List Bool) : run0 p 5 (B (false::X) (true::false::true::R)) =
      some (A (true::true::X) (true::false::R)) := by rfl
  have H := join0 (join0 h (f (rep zero k ++ true::L))) (left_pair (rep zero k ++ true::L) (true::false::R))
  simpa [d0,d1,Nat.add_assoc] using H

theorem good_carryC (j : Nat) (R : List Bool) :
    GoodC (8*(j+1)) (rep d1 j ++ d0 ++ R) (rep d0 j ++ d1 ++ R) := by
  cases j with
  | zero => simpa [rep] using good_zeroC R
  | succ j =>
    have h : StepsC (2^0) 8 (d0++R) (d1++R) := .cons (good_zeroC R) (.nil _)
    have H := overflow_delimiterC j 0 8 h
    rw [show 8*(j+1)+8+fillOver 0=8*(j+1+1) by simp [fillOver]; omega] at H
    simpa only [Nat.mul_zero, Nat.zero_mul, rep, List.nil_append, List.append_assoc] using H

/-- V=1 overflow is a Good increment and leaves the width unchanged with terminal U=011. -/
theorem overflowVcore (j : Nat) (L : List Bool) :
    run0 p (8*j+14) (A (false::true::true::true::L) (rep d1 j ++ [true])) =
      some (A L (rep d0 (j+1) ++ [false,true,true])) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    have h : run0 p 4 (A (false::true::true::true::L) (rep d1 (j+1) ++ [true])) =
      some (A (false::true::true::true::true::true::true::true::L) (rep d1 j ++ [true])) := by rfl
    have H := join0 h (ih (true::true::true::true::L))
    have J := join0 H (left_pairs 2 L (rep d0 (j+1) ++ [false,true,true]))
    rw [show 4+(8*j+14)+2*2=8*(j+1)+14 by omega] at J
    simpa [rep,pair,d0] using J

theorem overflowVC (j : Nat) : GoodC (8*(j+1)+10) (rep d1 (j+1) ++ [true])
    (rep d0 (j+1) ++ [false,true,true]) := by
  intro k L
  have h := first_d1 k L (rep d1 j ++ [true])
  have H := join0 h (overflowVcore j (rep zero k ++ true::L))
  rw [show k+4+(8*j+14)=k+(8*(j+1)+10) by omega] at H
  simpa [rep,List.append_assoc] using H

#print axioms overflow_delimiterC
#print axioms good_carryC
#print axioms overflowVC
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRACost
