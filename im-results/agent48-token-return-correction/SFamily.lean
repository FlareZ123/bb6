import RawTokenReturn
import Lean.Elab.Tactic.Omega

namespace BB6.Portfolio
set_option linter.unusedSimpArgs false
private theorem int_add_offset_eq (h a b : Int) : h+a=h+b ↔ a=b := Int.add_right_inj h
private theorem int_offset_eq_self (h a : Int) : h+a=h ↔ a=0 := by omega
private theorem int_self_eq_offset (h a : Int) : h=h+a ↔ a=0 := by omega
@[simp] private theorem d0_0_false : D0 (0:State) false = some (true, .R, (1 : State)) := rfl
@[simp] private theorem d0_0_true : D0 (0:State) true = some (false, .R, (4 : State)) := rfl
@[simp] private theorem d0_1_false : D0 (1:State) false = some (true, .L, (2 : State)) := rfl
@[simp] private theorem d0_1_true : D0 (1:State) true = some (false, .R, (0 : State)) := rfl
@[simp] private theorem d0_2_false : D0 (2:State) false = some (true, .L, (0 : State)) := rfl
@[simp] private theorem d0_2_true : D0 (2:State) true = some (true, .L, (3 : State)) := rfl
@[simp] private theorem d0_3_false : D0 (3:State) false = some (true, .L, (2 : State)) := rfl
@[simp] private theorem d0_3_true : D0 (3:State) true = some (true, .L, (5 : State)) := rfl
@[simp] private theorem d0_4_false : D0 (4:State) false = some (false, .L, (2 : State)) := rfl
@[simp] private theorem d0_4_true : D0 (4:State) true = some (false, .L, (1 : State)) := rfl
@[simp] private theorem d0_5_false : D0 (5:State) false = some (true, .L, (4 : State)) := rfl
@[simp] private theorem d0_5_true : D0 (5:State) true = none := rfl

/-- Mirrored tok_DR (2 :: 1^p ++ [0]) [] (0^a ++ [1]). -/
def tokenS (a p : Nat) (h : Int) : Cfg :=
  ⟨0,h,fun i => decide ((h-2*(a:Int) ≤ i ∧ i ≤ h ∧ (i-h)%2=0) ∨
    i=h-2*(a:Int)-1 ∨ i=h+1 ∨
    (h+2≤i ∧ i≤h+2*(p:Int)+2 ∧ (i-h)%2=0))⟩

/-- Mirrored tok_EL (1^b ++ [0]) [] (0^a ++ [1]). -/
def tokenE (a b : Nat) (h : Int) : Cfg :=
  ⟨1,h,fun i => decide (i=h-2*(a:Int)-2 ∨
    (h-2*(a:Int)-1 ≤ i ∧ i<h ∧ (i-h)%2=1) ∨
    (h≤i ∧ i<h+2*(b:Int) ∧ (i-h)%2=0))⟩

/-- Mirrored CR ([0]^a ++ [1]) with b consecutive ones to the right. -/
def tokenC (a b : Nat) (h : Int) : Cfg :=
  ⟨2,h,fun i => decide ((h-2*(a:Int)≤i ∧ i≤h ∧ (i-h)%2=0) ∨
    i=h-2*(a:Int)-1 ∨ (h<i ∧ i≤h+(b:Int)))⟩

private theorem run_add (n m : Nat) (c : Option Cfg) :
    run D0 (n+m) c = run D0 m (run D0 n c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.add_succ,run,ih,run]

private theorem s_pump (a p : Nat) (h : Int) :
    run D0 4 (some (tokenS (a+1) p h)) = some (tokenS a (p+1) (h-2)) := by
  let t := (tokenS (a+1) p h).tape
  have hh : t h = true := by simp only [t, tokenS, decide_eq_true_eq]; omega
  have hp : t (h+1) = true := by simp [t, tokenS]
  have hm : t (h-1) = false := by simp only [t, tokenS, decide_eq_false_iff_not]; omega
  have hr : run D0 4 (some ⟨0,h,t⟩) =
      some ⟨0,h-2,updateTape (updateTape (updateTape (updateTape t h false) (h+1) false) h true) (h-1) true⟩ := by
    simp [run,step,Dir.dx,hh,hp,hm,updateTape,show h+1≠h by omega,
      show h+1+-1=h by omega,show h≠h+1 by omega,
      show h+-1=h-1 by omega,show h-1≠h by omega,show h-1≠h+1 by omega,
      show h-1+-1=h-2 by omega]
  change run D0 4 (some ⟨0,h,t⟩) = _
  rw [hr]
  unfold tokenS
  congr 2
  funext i
  simp only [updateTape]
  by_cases hp' : i=h+1
  · subst i; simp [tokenS,show h+1≠h-1 by omega,show h+1≠h by omega]; omega
  by_cases hh' : i=h
  · subst i; simp [tokenS,show h≠h-1 by omega]; omega
  by_cases hm' : i=h-1
  · subst i; simp [tokenS]; omega
  simp only [if_neg hp',if_neg hh',if_neg hm',t,tokenS]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

#print axioms s_pump

private theorem s_base (p : Nat) (h : Int) :
    run D0 28 (some (tokenS 0 p h)) = some (tokenE 3 (p+1) (h+2)) := by
  let t := (tokenS 0 p h).tape
  have hp0 : t (h) = true := by
    simp only [t, tokenS, decide_eq_true_eq]; omega
  have hp1 : t (h+(1:Int)) = true := by
    simp [t, tokenS]
  have hm1 : t (h+(-1:Int)) = true := by
    simp only [t, tokenS, decide_eq_true_eq]; omega
  have hm2 : t (h+(-2:Int)) = false := by
    simp only [t, tokenS, decide_eq_false_iff_not]; omega
  have hm3 : t (h+(-3:Int)) = false := by
    simp only [t, tokenS, decide_eq_false_iff_not]; omega
  have hm4 : t (h+(-4:Int)) = false := by
    simp only [t, tokenS, decide_eq_false_iff_not]; omega
  have hm5 : t (h+(-5:Int)) = false := by
    simp only [t, tokenS, decide_eq_false_iff_not]; omega
  have hm6 : t (h+(-6:Int)) = false := by
    simp only [t, tokenS, decide_eq_false_iff_not]; omega
  have hr : run D0 28 (some ⟨0,h,t⟩) = some ⟨1,h+2,
    updateTape (updateTape (updateTape (updateTape (updateTape (updateTape (updateTape (updateTape t h false) (h+1) true) (h+(-1)) true) (h+(-2)) false) (h+(-3)) true) (h+(-4)) false) (h+(-5)) true) (h+(-6)) true⟩ := by
    simp [run,step,Dir.dx,updateTape,Int.add_assoc,int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,hp0,hp1,hm1,hm2,hm3,hm4,hm5,hm6]
    funext i
    simp only [updateTape]
    by_cases h0 : i=h
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases h1 : i=h+1
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases hm1' : i=h+(-1)
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases hm2' : i=h+(-2)
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases hm3' : i=h+(-3)
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases hm4' : i=h+(-4)
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases hm5' : i=h+(-5)
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    by_cases hm6' : i=h+(-6)
    · subst i; simp [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset]
    simp [h0,h1,hm1',hm2',hm3',hm4',hm5',hm6']
  change run D0 28 (some ⟨0,h,t⟩) = _
  rw [hr]
  unfold tokenE
  congr 2
  funext i
  simp only [updateTape]
  by_cases hip0 : i=h
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_false_iff_not.mpr
    omega
  by_cases hip1 : i=h+(1:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_true_eq.mpr
    omega
  by_cases him1 : i=h+(-1:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_true_eq.mpr
    omega
  by_cases him2 : i=h+(-2:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_false_iff_not.mpr
    omega
  by_cases him3 : i=h+(-3:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_true_eq.mpr
    omega
  by_cases him4 : i=h+(-4:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_false_iff_not.mpr
    omega
  by_cases him5 : i=h+(-5:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_true_eq.mpr
    omega
  by_cases him6 : i=h+(-6:Int)
  · subst i
    simp only [int_add_offset_eq,int_offset_eq_self,int_self_eq_offset,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    symm
    apply decide_eq_true_eq.mpr
    omega
  simp only [if_neg hip0, if_neg hip1, if_neg him1, if_neg him2, if_neg him3, if_neg him4, if_neg him5, if_neg him6,t,tokenS]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

#print axioms s_base

private theorem e_pump (a b : Nat) (h : Int) :
    run D0 2 (some (tokenE a (b+1) h)) = some (tokenE (a+1) b (h+2)) := by
  let t := (tokenE a (b+1) h).tape
  have hh : t h = true := by simp only [t,tokenE,decide_eq_true_eq]; omega
  have hp : t (h+1) = false := by simp only [t,tokenE,decide_eq_false_iff_not]; omega
  have hr : run D0 2 (some ⟨1,h,t⟩) = some ⟨1,h+2,updateTape (updateTape t h false) (h+1) true⟩ := by
    simp [run,step,Dir.dx,hh,hp,updateTape,show h+1≠h by omega] <;> omega
  change run D0 2 (some ⟨1,h,t⟩) = _
  rw [hr]
  unfold tokenE
  congr 2
  funext i
  simp only [updateTape]
  by_cases hp' : i=h+1
  · subst i; simp only [ite_true,if_pos rfl]; symm; apply decide_eq_true_eq.mpr; omega
  by_cases hh' : i=h
  · subst i; simp only [if_neg hp',ite_true,if_pos rfl]; symm; apply decide_eq_false_iff_not.mpr; omega
  simp only [if_neg hp',if_neg hh',t,tokenE]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem e_exit (a : Nat) (h : Int) :
    run D0 1 (some (tokenE a 0 h)) = some (tokenC a 1 (h-1)) := by
  let t := (tokenE a 0 h).tape
  have hh : t h = false := by simp only [t,tokenE,decide_eq_false_iff_not]; omega
  have hr : run D0 1 (some ⟨1,h,t⟩) = some ⟨2,h-1,updateTape t h true⟩ := by
    simp [run,step,Dir.dx,hh,show h+-1=h-1 by omega]
  change run D0 1 (some ⟨1,h,t⟩) = _
  rw [hr]
  unfold tokenC
  congr 2
  funext i
  simp only [updateTape]
  by_cases hh' : i=h
  · subst i; simp only [ite_true,if_pos rfl]; symm; apply decide_eq_true_eq.mpr; omega
  simp only [if_neg hh',t,tokenE]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem c_pump (a b : Nat) (h : Int) :
    run D0 2 (some (tokenC (a+1) b h)) = some (tokenC a (b+2) (h-2)) := by
  let t := (tokenC (a+1) b h).tape
  have hh : t h = true := by simp only [t,tokenC,decide_eq_true_eq]; omega
  have hm : t (h-1) = false := by simp only [t,tokenC,decide_eq_false_iff_not]; omega
  have hr : run D0 2 (some ⟨2,h,t⟩) = some ⟨2,h-2,updateTape (updateTape t h true) (h-1) true⟩ := by
    simp [run,step,Dir.dx,hh,hm,updateTape,show h+-1=h-1 by omega,
      show h-1≠h by omega,show h-1+-1=h-2 by omega]
  change run D0 2 (some ⟨2,h,t⟩) = _
  rw [hr]
  unfold tokenC
  congr 2
  funext i
  simp only [updateTape]
  by_cases hm' : i=h-1
  · subst i; simp only [ite_true,if_pos rfl]; symm; apply decide_eq_true_eq.mpr; omega
  by_cases hh' : i=h
  · subst i; simp only [if_neg hm',ite_true,if_pos rfl]; symm; apply decide_eq_true_eq.mpr; omega
  simp only [if_neg hm',if_neg hh',t,tokenC]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem c_base (b : Nat) (h : Int) :
    run D0 2 (some (tokenC 0 b h)) = some (F0Pure (b+2) (h-2)) := by
  let t := (tokenC 0 b h).tape
  have hh : t h = true := by simp only [t,tokenC,decide_eq_true_eq]; omega
  have hm : t (h-1) = true := by simp only [t,tokenC,decide_eq_true_eq]; omega
  have hr : run D0 2 (some ⟨2,h,t⟩) = some ⟨5,h-2,updateTape (updateTape t h true) (h-1) true⟩ := by
    simp [run,step,Dir.dx,hh,hm,updateTape,show h+-1=h-1 by omega,
      show h-1≠h by omega,show h-1+-1=h-2 by omega]
  change run D0 2 (some ⟨2,h,t⟩) = _
  rw [hr]
  unfold F0Pure
  congr 2
  funext i
  simp only [updateTape]
  by_cases hm' : i=h-1
  · subst i; simp only [ite_true,if_pos rfl]; symm; apply decide_eq_true_eq.mpr; omega
  by_cases hh' : i=h
  · subst i; simp only [if_neg hm',ite_true,if_pos rfl]; symm; apply decide_eq_true_eq.mpr; omega
  simp only [if_neg hm',if_neg hh',t,tokenC]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem s_sweep (a p : Nat) (h : Int) :
    run D0 (4*a) (some (tokenS a p h)) = some (tokenS 0 (p+a) (h-2*(a:Int))) := by
  induction a generalizing p h with
  | zero => simp [run]
  | succ a ih =>
    rw [show 4*(a+1)=4+4*a by omega,run_add,s_pump,ih]
    congr 2 <;> omega

private theorem e_sweep (a b : Nat) (h : Int) :
    run D0 (2*b) (some (tokenE a b h)) = some (tokenE (a+b) 0 (h+2*(b:Int))) := by
  induction b generalizing a h with
  | zero => simp [run]
  | succ b ih =>
    rw [show 2*(b+1)=2+2*b by omega,run_add,e_pump,ih]
    congr 2 <;> omega

private theorem c_sweep (a b : Nat) (h : Int) :
    run D0 (2*a) (some (tokenC a b h)) = some (tokenC 0 (b+2*a) (h-2*(a:Int))) := by
  induction a generalizing b h with
  | zero => simp [run]
  | succ a ih =>
    rw [show 2*(a+1)=2+2*a by omega,run_add,c_pump,ih]
    congr 2 <;> omega

/-- Exact raw return for arbitrary lengths of the two alternating sections. -/
theorem tokenS_to_F0Pure (a p : Nat) (h : Int) :
    run D0 (8*a+4*p+41) (some (tokenS a p h)) =
      some (F0Pure (2*a+2*p+11) (h-2*(a:Int)-7)) := by
  rw [show 8*a+4*p+41 = 4*a+28+2*(p+a+1)+1+2*(3+(p+a+1))+2 by omega]
  rw [run_add,run_add,run_add,run_add,run_add,s_sweep,s_base,e_sweep,e_exit,c_sweep,c_base]
  congr 2 <;> omega

#print axioms tokenS_to_F0Pure

/-- Full halting equivalence, with no assumption of root reachability. -/
theorem tokenS_halting_iff (a p : Nat) (h : Int) :
    (∃ n, tokenHaltsAt (tokenS a p h) n) ↔
    (∃ n, tokenHaltsAt (F0Pure (2*a+2*p+11) (h-2*(a:Int)-7)) n) := by
  let m := 8*a+4*p+41
  have hm := tokenS_to_F0Pure a p h
  change run D0 m (some (tokenS a p h)) = _ at hm
  constructor
  · rintro ⟨n,last,hr,hs⟩
    have hmn : m≤n := by
      by_cases hle : m≤n
      · exact hle
      · have he : m=n+1+(m-n-1) := by omega
        rw [he,run_add,run,hr] at hm
        change run D0 (m-n-1) (step D0 last) = _ at hm
        rw [hs] at hm
        have hn : ∀ k, run D0 k none=none := by
          intro k; induction k <;> simp [run, *]
        rw [hn] at hm
        contradiction
    refine ⟨n-m,last,?_,hs⟩
    have he : n=m+(n-m) := by omega
    conv at hr => lhs; rw [he,run_add,hm]
    exact hr
  · rintro ⟨n,last,hr,hs⟩
    exact ⟨m+n,last,by rw [run_add,hm,hr],hs⟩

#print axioms tokenS_halting_iff
end BB6.Portfolio
