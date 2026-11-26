import Raw54LA104
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.LA.M37
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper
open BB6.Agent8Raw54.LA.Pair126 (EqL EqZ RelRun eqL_refl eqL_symm eqL_zero eqL_append eqL_cons eqZ_refl eqZ_trans eqZ_symm eqZ_run rel_exact rel_pad)
open BB6.Agent8Raw54.LA.M61 (U V Vcomm Ucomm)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

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

theorem scan (n : Nat) (L Y : List Bool) :
    run0 table (n+4) ⟨0,false::L,true::false::(U n++false::Y)⟩ =
      some ⟨3,Y.headD false::false::(V n++true::false::true::L),Y.tail⟩ := by
  have h0 : run0 table 3 ⟨0,false::L,true::false::(U n++false::Y)⟩ =
      some ⟨2,(U n++false::Y).headD false::true::false::true::L,(U n++false::Y).tail⟩ := by cases n <;> rfl
  have H := join0 h0 (scanC n (true::false::true::L) Y)
  rw [show 3+(n+1)=n+4 by omega] at H
  exact H

theorem push (n : Nat) (L R : List Bool) :
    run0 table (n+6) ⟨0,false::L,true::false::(U n++false::true::R)⟩ =
      some ⟨0,V n++true::false::true::L,true::false::R⟩ := by
  have h0 := scan n L (true::R)
  have h1 : run0 table 2 ⟨3,true::false::(V n++true::false::true::L),R⟩ =
      some ⟨0,V n++true::false::true::L,true::false::R⟩ := rfl
  have H := join0 h0 h1
  rw [show n+4+2=n+6 by omega] at H
  exact H

theorem merge (n : Nat) (L R : List Bool) :
    run0 table (2*n+8) ⟨0,false::L,true::false::(U n++false::false::R)⟩ =
      some ⟨0,true::L,true::false::(U (n+2)++R)⟩ := by
  have h0 := scan n L (false::R)
  have h1 : run0 table (1*(n+2)) ⟨3,false::false::(V n++true::false::true::L),R⟩ =
      some ⟨3,true::false::true::L,U (n+2)++R⟩ := by
    simpa only [U,V,rep,List.cons_append,List.nil_append] using
      sweepL table 3 [] [] [false] [true] 1 (by intro A B; rfl) (n+2) (true::false::true::L) R
  have h2 : run0 table 2 ⟨3,true::false::true::L,U (n+2)++R⟩ =
      some ⟨0,true::L,true::false::(U (n+2)++R)⟩ := rfl
  have H := join0 (join0 h0 h1) h2
  rw [show n+4+1*(n+2)+2=2*n+8 by omega] at H
  exact H

theorem mergeLast (n : Nat) (L : List Bool) :
    RelRun table (2*n+8) ⟨0,false::L,true::false::U n⟩
      ⟨0,true::L,true::false::U (n+2)⟩ := by
  apply rel_pad (a := ⟨0,false::L,true::false::(U n++[false,false])⟩)
    (b := ⟨0,true::L,true::false::(U (n+2)++[])⟩)
  · refine ⟨rfl,eqL_refl _,eqL_cons true (eqL_cons false ?_)⟩
    simpa only [List.append_nil] using eqL_append (U n) (show EqL [false,false] [] from eqL_zero 2)
  · simp only [List.append_nil]; exact eqZ_refl _
  · exact merge n L []

theorem pop (L S : List Bool) :
    run0 table 9 ⟨0,true::false::false::true::false::true::L,true::false::S⟩ =
      some ⟨0,true::L,true::false::false::true::true::true::false::S⟩ := rfl

theorem decrease (X S : List Bool) :
    run0 table 8 ⟨0,true::false::false::false::false::X,true::false::S⟩ =
      some ⟨0,false::X,true::false::true::true::true::false::S⟩ := rfl

theorem emptyTransfer (S : List Bool) :
    RelRun table 8 ⟨0,[true],true::false::S⟩
      ⟨0,[false],true::false::true::true::true::false::S⟩ := by
  refine ⟨⟨0,[],true::false::true::true::true::false::S⟩,rfl,?_⟩
  exact ⟨rfl,eqL_symm (eqL_zero 1),eqL_refl _⟩

theorem Uadd (n m : Nat) : U n++U m = U (n+m) := by
  induction n with
  | zero => simp only [U,rep,List.nil_append,Nat.zero_add]
  | succ n ih =>
    rw [Nat.succ_add]
    change true::(U n++U m)=true::U (n+m)
    rw [ih]

-- At A0, the initial nonterminal run has length 3 mod 4. A
-- subsequent run has length 0 mod 4 after a single zero, or 3 mod 4
-- after two zeros. The final run is unrestricted.
inductive Word where
  | last (n : Nat)
  | one (n : Nat) (w : Word)
  | two (n : Nat) (w : Word)
def word : Word → List Bool
  | .last n => U n
  | .one n w => U (4*n+3)++false::true::word w
  | .two n w => U (4*n+3)++false::false::word w

def grow (n : Nat) : Word → Word
  | .last m => .last (4*n+4+m)
  | .one m w => .one (n+m+1) w
  | .two m w => .two (n+m+1) w

theorem grow_spec (n : Nat) (w : Word) : word (grow n w)=U (4*n+4)++word w := by
  cases w with
  | last m => exact (Uadd (4*n+4) m).symm
  | one m w =>
    simp only [grow,word,← List.append_assoc,Uadd]
    rw [show 4*(n+m+1)+3=4*n+4+(4*m+3) by omega]
  | two m w =>
    simp only [grow,word,← List.append_assoc,Uadd]
    rw [show 4*(n+m+1)+3=4*n+4+(4*m+3) by omega]

def pops := rep [false,true,true,true,false]
def wrap : Nat → Word → Word
  | 0,w => .one 0 w
  | j+1,w => .two 0 (wrap j w)

theorem wrap_spec (j : Nat) (w : Word) : word (wrap j w)=true::true::true::false::(pops j++true::word w) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change true::true::true::false::false::word (wrap j w) = _
    rw [ih]
    rfl

def frames : List Nat → List Bool
  | [] => []
  | k::ks => V (4*k+2)++true::false::true::frames ks

inductive Section where
  | p (ks : List Nat) (w : Word)
  | q (ks : List Nat) (j : Nat) (w : Word)
def cfg : Section → Z0
  | .p ks w => ⟨0,false::frames ks,true::false::word w⟩
  | .q ks j w => ⟨0,true::frames ks,true::false::(pops j++true::word w)⟩

theorem sectionReturn (s : Section) : ∃ t s', 0<t ∧ RelRun table t (cfg s) (cfg s') := by
  cases s with
  | p ks w =>
    cases w with
    | last n => exact ⟨2*n+8,.q ks 0 (.last (n+1)),by omega,mergeLast n (frames ks)⟩
    | one n w =>
      refine ⟨4*n+3+6,.p (n::ks) w,by omega,rel_exact ?_⟩
      exact push (4*n+3) (frames ks) (word w)
    | two n w =>
      refine ⟨2*(4*n+3)+8,.q ks 0 (grow n w),by omega,rel_exact ?_⟩
      have h := merge (4*n+3) (frames ks) (word w)
      simp only [cfg,word,pops,rep,List.nil_append,grow_spec]
      exact h
  | q ks j w =>
    cases ks with
    | nil =>
      refine ⟨8,.p [] (wrap j w),by omega,?_⟩
      simpa only [cfg,frames,wrap_spec] using emptyTransfer (pops j++true::word w)
    | cons k ks =>
      cases k with
      | zero =>
        refine ⟨9,.q ks (j+1) w,by omega,rel_exact ?_⟩
        exact pop (frames ks) (pops j++true::word w)
      | succ k =>
        refine ⟨8,.p (k::ks) (wrap j w),by omega,rel_exact ?_⟩
        simp only [cfg,frames,wrap_spec]
        rw [show 4*(k+1)+2=4*k+2+1+1+1+1 by omega]
        exact decrease (V (4*k+2)++true::false::true::frames ks) (pops j++true::word w)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have first : run0 table 43 ⟨0,[],[]⟩ = some (cfg (.q [] 0 (.last 5))) := rfl
  have arbitrary : ∀ k : Nat, ∃ t z u, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ EqZ (cfg u) z := by
    intro k
    induction k with
    | zero => exact ⟨43,_,.q [] 0 (.last 5),by omega,first,eqZ_refl _⟩
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
end BB6.Agent8Raw54.LA.M37
