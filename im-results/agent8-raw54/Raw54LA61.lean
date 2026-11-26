import Raw54LAPair126
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.LA.M61
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper
open BB6.Agent8Raw54.LA.Pair126 (EqL EqZ RelRun eqL_refl eqL_symm eqL_zero eqL_append eqL_cons eqZ_refl eqZ_trans eqZ_symm eqZ_run rel_exact rel_pad)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def U := rep [true]
def V := rep [false]

theorem Vcomm (n : Nat) (L : List Bool) : V n++false::L = false::(V n++L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false::(V n++false::L) = false::false::(V n++L)
    rw [ih]

theorem Ucomm (n : Nat) (L : List Bool) : U n++true::L = true::(U n++L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true::(U n++true::L) = true::true::(U n++L)
    rw [ih]

theorem scanB (m : Nat) (L X : List Bool) :
    run0 table (m+3) ⟨0,false::L,true::(U m++false::X)⟩ =
      some ⟨2,X.headD false::true::(V (m+1)++true::L),X.tail⟩ := by
  have h0 : run0 table 1 ⟨0,false::L,true::(U m++false::X)⟩ =
      some ⟨1,true::true::L,U m++false::X⟩ := rfl
  have h1 : run0 table (1*m) ⟨1,true::true::L,U m++false::X⟩ =
      some ⟨1,true::(V m++true::L),false::X⟩ := by
    simpa only [U,V,List.cons_append,List.nil_append] using
      sweepR table 1 [true] [] [true] [false] 1
        (by intro A B; rfl) m (true::L) (false::X)
  have h2 : run0 table 2 ⟨1,true::(V m++true::L),false::X⟩ =
      some ⟨2,X.headD false::true::(V (m+1)++true::L),X.tail⟩ := by cases X <;> rfl
  have H := join0 (join0 h0 h1) h2
  rw [show 1+1*m+2=m+3 by omega] at H
  exact H

theorem scanC (n : Nat) (L Y : List Bool) :
    run0 table (n+1) ⟨2,(U n++false::Y).headD false::L,(U n++false::Y).tail⟩ =
      some ⟨3,Y.headD false::false::(V n++L),Y.tail⟩ := by
  induction n generalizing L with
  | zero => cases Y <;> rfl
  | succ n ih =>
    change run0 table (n+1+1) ⟨2,true::L,U n++false::Y⟩ = _
    rw [show n+1+1=1+(n+1) by omega]
    have h : run0 table 1 ⟨2,true::L,U n++false::Y⟩ =
        some ⟨2,(U n++false::Y).headD false::false::L,(U n++false::Y).tail⟩ := rfl
    have H := join0 h (ih (false::L))
    rw [Vcomm] at H
    exact H

-- Main scan: B consumes the first one-run, C the second, and D
-- turns the second run's zeros back into ones. The final two moves
-- expose the first run's counter representation on the left.
theorem mainScan (m n : Nat) (L : List Bool) :
    RelRun table (m+2*n+8)
      ⟨0,false::L,true::(U m++false::U n)⟩
      ⟨0,V m++true::L,true::false::U (n+2)⟩ := by
  have h0 := scanB m L (U n++false::[false])
  have h1 := scanC n (true::(V (m+1)++true::L)) [false]
  have h2 : run0 table (1*(n+2))
      ⟨3,false::false::(V n++true::(V (m+1)++true::L)),[]⟩ =
      some ⟨3,true::(V (m+1)++true::L),U (n+2)⟩ := by
    simpa only [U,V,rep,List.nil_append,List.cons_append,List.append_nil] using
      sweepL table 3 [] [] [false] [true] 1
        (by intro A B; rfl) (n+2) (true::(V (m+1)++true::L)) []
  have h3 : run0 table 2 ⟨3,true::(V (m+1)++true::L),U (n+2)⟩ =
      some ⟨0,V m++true::L,true::false::U (n+2)⟩ := rfl
  have H := join0 (join0 (join0 h0 h1) h2) h3
  rw [show m+3+(n+1)+1*(n+2)+2=m+2*n+8 by omega] at H
  apply rel_pad (a := ⟨0,false::L,true::(U m++false::(U n++[false,false]))⟩)
    (b := ⟨0,V m++true::L,true::false::U (n+2)⟩)
  · refine ⟨rfl,eqL_refl _,?_⟩
    have he : EqL (U n++[false,false]) (U n) := by
      simpa only [List.append_nil] using eqL_append (U n) (show EqL [false,false] [] from eqL_zero 2)
    exact eqL_cons true (eqL_append (U m) (eqL_cons false he))
  · exact eqZ_refl _
  · simpa only [List.append_assoc,List.cons_append] using H

-- Overflow: C stops before a positive third one-run. D sees one
-- immediately, bypassing its zero sweep and installing a new counter.
theorem overflow (k n : Nat) :
    run0 table (3*k+9) ⟨0,[],true::false::(U (3*k+3)++false::true::U n)⟩ =
      some ⟨0,V (3*k+3)++[true,false,true],true::false::U n⟩ := by
  have h0 := scanB 0 [] (U (3*k+3)++false::true::U n)
  have h0' : run0 table 3 ⟨0,[],true::false::(U (3*k+3)++false::true::U n)⟩ =
      some ⟨2,(U (3*k+3)++false::true::U n).headD false::[true,false,true],(U (3*k+3)++false::true::U n).tail⟩ := by rfl
  have h1 := scanC (3*k+3) [true,false,true] (true::U n)
  have h2 : run0 table 2 ⟨3,true::false::(V (3*k+3)++[true,false,true]),U n⟩ =
      some ⟨0,V (3*k+3)++[true,false,true],true::false::U n⟩ := rfl
  have H := join0 (join0 h0' h1) h2
  rw [show 3+(3*k+3+1)+2=3*k+9 by omega] at H
  exact H

def digits : List Bool → List Bool
  | [] => [false,true]
  | b::w => false::false::b::digits w

theorem digits_zeros (k : Nat) (w : List Bool) :
    digits (List.replicate k false++true::w) = V (3*k+2)++true::digits w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false::false::false::digits (List.replicate k false++true::w) = _
    rw [ih,show 3*(k+1)+2=3*k+2+1+1+1 by omega]
    rfl

inductive Section where
  | p (w : List Bool) (n : Nat)
  | q (w : List Bool) (k n : Nat)
  | r (w : List Bool) (k n : Nat)
  | o (k n : Nat)

def cfg : Section → Z0
  | .p w n => ⟨0,false::digits w,true::false::U n⟩
  | .q w k n => ⟨0,true::digits w,U (3*k+1)++false::U (n+1)⟩
  | .r w k n => ⟨0,false::digits w,U (3*k+4)++false::U (n+1)⟩
  | .o k n => ⟨0,[],true::false::(U (3*k+3)++false::U (n+1))⟩

theorem sectionReturn (s : Section) : ∃ t s', 0<t ∧ RelRun table t (cfg s) (cfg s') := by
  cases s with
  | p w n =>
    exact ⟨2*n+8,.q w 0 (n+1),by omega,by simpa only [cfg,U,V,rep,List.nil_append,List.append_nil,List.cons_append,show 0+2*n+8=2*n+8 by omega] using mainScan 0 n (digits w)⟩
  | q w k n =>
    cases w with
    | nil =>
      refine ⟨4,.o k n,by omega,rel_exact ?_⟩
      simp only [cfg,digits]
      rw [show 3*k+1=3*k+1 by rfl,show 3*k+3=3*k+1+1+1 by omega]
      rfl
    | cons b w =>
      cases b
      · refine ⟨3,.r w k n,by omega,rel_exact ?_⟩
        simp only [cfg,digits]
        rw [show 3*k+4=3*k+1+1+1+1 by omega]
        rfl
      · refine ⟨3,.q w (k+1) n,by omega,rel_exact ?_⟩
        simp only [cfg,digits]
        rw [show 3*(k+1)+1=3*k+1+1+1+1 by omega]
        rfl
  | r w k n =>
    refine ⟨3*k+3+2*(n+1)+8,.p (List.replicate k false++true::w) (n+3),by omega,?_⟩
    have h := mainScan (3*k+3) (n+1) (digits w)
    simp only [cfg,digits_zeros] at *
    exact h
  | o k n =>
    refine ⟨3*k+9,.p (List.replicate k false++[true]) n,by omega,rel_exact ?_⟩
    have h := overflow k n
    change run0 table (3*k+9) ⟨0,[],true::false::(U (3*k+3)++false::true::U n)⟩ = some ⟨0,false::digits (List.replicate k false++true::[]),true::false::U n⟩
    rw [digits_zeros]
    exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have first : run0 table 27 ⟨0,[],[]⟩ = some (cfg (.p [true] 0)) := rfl
  have arbitrary : ∀ k : Nat, ∃ t z u, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ EqZ (cfg u) z := by
    intro k
    induction k with
    | zero => exact ⟨27,_,.p [true] 0,by omega,first,eqZ_refl _⟩
    | succ k ih =>
      obtain ⟨t,z,u,ht,hr,he⟩ := ih
      obtain ⟨s,u',hs,w,hw,he'⟩ := sectionReturn u
      obtain ⟨z',hz',hzz⟩ := eqZ_run table s he hw
      exact ⟨t+s,z',u',by omega,join0 hr hz',eqZ_trans (eqZ_symm he') hzz⟩
  intro n
  obtain ⟨t,z,u,ht,hr,_⟩ := arbitrary n
  have hz : (zrun table t start).map project = some z := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms sectionReturn
#print axioms never
end BB6.Agent8Raw54.LA.M61
