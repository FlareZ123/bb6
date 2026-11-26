import Raw54LA61
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.LA.M104
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper
open BB6.Agent8Raw54.LA.Pair126 (EqL EqZ RelRun eqL_refl eqL_symm eqL_zero eqL_append eqL_cons eqZ_refl eqZ_trans eqZ_symm eqZ_run rel_exact rel_pad)
open BB6.Agent8Raw54.LA.M61 (U V Vcomm Ucomm)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem toQ (L R : List Bool) :
    run0 table 5 ⟨0,false::L,true::false::R⟩ = some ⟨0,L,false::true::true::R⟩ := rfl

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
    run0 table (n+1+3) ⟨0,false::L,false::(U (n+1)++false::Y)⟩ =
      some ⟨3,Y.headD false::false::(V (n+1)++true::true::L),Y.tail⟩ := by
  have h0 : run0 table 2 ⟨0,false::L,false::(U (n+1)++false::Y)⟩ =
      some ⟨2,(U (n+1)++false::Y).headD false::true::true::L,(U (n+1)++false::Y).tail⟩ := rfl
  have H := join0 h0 (scanC (n+1) (true::true::L) Y)
  rw [show 2+(n+1+1)=n+1+3 by omega] at H
  exact H

theorem push (n : Nat) (L R : List Bool) :
    run0 table (n+1+5) ⟨0,false::L,false::(U (n+1)++false::true::R)⟩ =
      some ⟨0,V (n+1)++true::true::L,true::false::R⟩ := by
  have h0 := scan n L (true::R)
  have h1 : run0 table 2 ⟨3,true::false::(V (n+1)++true::true::L),R⟩ =
      some ⟨0,V (n+1)++true::true::L,true::false::R⟩ := rfl
  have H := join0 h0 h1
  rw [show n+1+3+2=n+1+5 by omega] at H
  exact H

theorem drain (n s : Nat) (L R : List Bool) :
    run0 table (2*(n+1)+s+8)
      ⟨0,false::(U s++false::L),false::(U (n+1)++false::false::R)⟩ =
      some ⟨0,L,true::false::(V (s+1)++U (n+3)++R)⟩ := by
  have h0 := scan n (U s++false::L) (false::R)
  have h1 : run0 table (1*(n+3))
      ⟨3,false::false::(V (n+1)++true::true::(U s++false::L)),R⟩ =
      some ⟨3,true::true::(U s++false::L),U (n+3)++R⟩ := by
    simpa only [U,V,rep,List.cons_append,List.nil_append] using
      sweepL table 3 [] [] [false] [true] 1 (by intro A B; rfl)
        (n+3) (true::true::(U s++false::L)) R
  have h2 : run0 table 1 ⟨3,true::true::(U s++false::L),U (n+3)++R⟩ =
      some ⟨4,U (s+1)++false::L,false::(U (n+3)++R)⟩ := rfl
  have h3 : run0 table (1*(s+1)) ⟨4,U (s+1)++false::L,false::(U (n+3)++R)⟩ =
      some ⟨4,false::L,V (s+1)++false::(U (n+3)++R)⟩ := by
    simpa only [U,V,List.nil_append] using
      sweepL table 4 [] [] [true] [false] 1 (by intro A B; rfl)
        (s+1) (false::L) (false::(U (n+3)++R))
  have h4 : run0 table 1 ⟨4,false::L,V (s+1)++false::(U (n+3)++R)⟩ =
      some ⟨0,L,true::false::(V (s+1)++U (n+3)++R)⟩ := by
    rw [Vcomm,List.append_assoc]
    rfl
  have H := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show n+1+3+1*(n+3)+1+1*(s+1)+1=2*(n+1)+s+8 by omega] at H
  exact H

-- A left frame consists of a multiple-of-three zero gap (with the
-- phase offset at the top) followed by a positive even one-run.
abbrev Rest := List (Nat × Nat)
def rest : Rest → List Bool
  | [] => []
  | (k,b)::xs => V (3*(k+1))++U (2*b+2)++rest xs
inductive Left where
  | empty
  | top (k b : Nat) (xs : Rest)

def pLeft : Left → List Bool
  | .empty => []
  | .top k b xs => V (3*k+2)++U (2*b+2)++rest xs

def qLeft : Left → List Bool
  | .empty => []
  | .top k b xs => V (3*k+1)++U (2*b+2)++rest xs

def afterPush (n : Nat) : Left → Left
  | .empty => .top n 0 []
  | .top 0 b xs => .top n (b+1) xs
  | .top (k+1) b xs => .top n 0 ((k,b)::xs)

def afterDrain : Left → Left × Nat
  | .empty => (.empty,0)
  | .top (k+1) b xs => (.top k b xs,0)
  | .top 0 b [] => (.empty,b+1)
  | .top 0 b ((k,c)::xs) => (.top k c xs,b+1)

theorem pToQ (l : Left) (R : List Bool) :
    run0 table 5 ⟨0,pLeft l,true::false::R⟩ = some ⟨0,qLeft l,false::true::true::R⟩ := by
  cases l with
  | empty => rfl
  | top k b xs => exact toQ (qLeft (.top k b xs)) R

theorem qPush (l : Left) (n : Nat) (R : List Bool) :
    run0 table (3*n+7) ⟨0,qLeft l,false::(U (3*n+2)++false::true::R)⟩ =
      some ⟨0,pLeft (afterPush n l),true::false::R⟩ := by
  cases l with
  | empty =>
    have h0 : run0 table 2 ⟨0,[],false::(U (3*n+2)++false::true::R)⟩ =
        some ⟨2,true::true::true::[],U (3*n+1)++false::true::R⟩ := rfl
    have h1 : run0 table 2 ⟨0,[false],false::(U (3*n+2)++false::true::R)⟩ =
        some ⟨2,true::true::true::[],U (3*n+1)++false::true::R⟩ := rfl
    have h := push (3*n+1) [] R
    simp only [qLeft,pLeft,afterPush,rest,List.append_nil]
    change run0 table (3*n+7) ⟨0,[],false::(U (3*n+2)++false::true::R)⟩ =
      some ⟨0,V (3*n+2)++[true,true],true::false::R⟩
    rw [show 3*n+7=2+(3*n+5) by omega,run0_add table 2 (3*n+5),h0]
    rw [show 3*n+1+1+5=2+(3*n+5) by omega,run0_add table 2 (3*n+5),h1] at h
    exact h
  | top k b xs =>
    have h := push (3*n+1) (V (3*k)++U (2*b+2)++rest xs) R
    rw [show 3*n+1+1+5=3*n+7 by omega] at h
    cases k with
    | zero =>
      simp only [qLeft,pLeft,afterPush]
      rw [show 2*(b+1)+2=2*b+2+1+1 by omega]
      simpa only [U,V,rep,List.nil_append,List.cons_append,List.append_assoc] using h
    | succ k =>
      simpa only [qLeft,pLeft,afterPush,rest,U,V,rep,List.nil_append,List.cons_append,List.append_assoc] using h

theorem qDrain (l : Left) (a : Nat) (R : List Bool) :
    ∃ t, 0<t ∧ RelRun table t
      ⟨0,qLeft l,false::(U (a+2)++false::false::R)⟩
      ⟨0,pLeft (afterDrain l).1,true::false::(V (2*(afterDrain l).2+1)++U (a+4)++R)⟩ := by
  cases l with
  | empty =>
    refine ⟨2*(a+2)+8,by omega,?_⟩
    have h := drain (a+1) 0 [] R
    apply rel_pad (a := ⟨0,[false,false],false::(U (a+2)++false::false::R)⟩)
      (b := ⟨0,[],true::false::(V 1++U (a+4)++R)⟩)
    · exact ⟨rfl,eqL_zero 2,eqL_refl _⟩
    · exact eqZ_refl _
    · exact h
  | top k b xs =>
    cases k with
    | succ k =>
      refine ⟨2*(a+2)+8,by omega,rel_exact ?_⟩
      have h := drain (a+1) 0 (pLeft (.top k b xs)) R
      change run0 table (2*(a+2)+8) ⟨0,V (3*(k+1)+1)++U (2*b+2)++rest xs,false::(U (a+2)++false::false::R)⟩ =
        some ⟨0,pLeft (.top k b xs),true::false::(V 1++U (a+4)++R)⟩
      rw [show 3*(k+1)+1=3*k+2+1+1 by omega]
      exact h
    | zero =>
      refine ⟨2*(a+2)+(2*b+2)+8,by omega,?_⟩
      cases xs with
      | nil =>
        have h := drain (a+1) (2*b+2) [] R
        apply rel_pad (a := ⟨0,false::(U (2*b+2)++[false]),false::(U (a+2)++false::false::R)⟩)
          (b := ⟨0,[],true::false::(V (2*b+2+1)++U (a+4)++R)⟩)
        · refine ⟨rfl,?_,eqL_refl _⟩
          simp only [qLeft,V,rep,List.nil_append,List.cons_append,rest,List.append_nil]
          apply eqL_cons false
          simpa only [List.append_nil] using eqL_append (U (2*b+2)) (show EqL [false] [] from eqL_zero 1)
        · have he : 2*b+2+1=2*(b+1)+1 := by omega
          simp only [afterDrain,pLeft,he]
          exact eqZ_refl _
        · exact h
      | cons x xs =>
        rcases x with ⟨k,c⟩
        apply rel_exact
        have h := drain (a+1) (2*b+2) (pLeft (.top k c xs)) R
        simp only [qLeft,afterDrain,rest]
        change run0 table (2*(a+2)+(2*b+2)+8)
          ⟨0,false::(U (2*b+2)++(V (3*(k+1))++U (2*c+2)++rest xs)),false::(U (a+2)++false::false::R)⟩ =
          some ⟨0,pLeft (.top k c xs),true::false::(V (2*(b+1)+1)++U (a+4)++R)⟩
        rw [show 3*(k+1)=3*k+2+1 by omega,show 2*(b+1)+1=2*b+2+1 by omega]
        simpa only [V,rep,pLeft,List.cons_append,List.append_assoc,List.nil_append] using h

-- All internal right one-runs have the prescribed residues, while
-- the terminal run is unrestricted. Gaps are positive odd numbers.
inductive Word where
  | last (n : Nat)
  | more (n g : Nat) (w : Word)
def suffix : Word → List Bool
  | .last n => U n
  | .more n g w => U (3*n)++V (2*g+1)++true::suffix w
inductive Section where
  | p (l : Left) (w : Word)
  | q (l : Left) (w : Word)
def cfg : Section → Z0
  | .p l w => ⟨0,pLeft l,true::false::suffix w⟩
  | .q l w => ⟨0,qLeft l,false::true::true::suffix w⟩

theorem sectionReturn (s : Section) : ∃ t s', 0<t ∧ RelRun table t (cfg s) (cfg s') := by
  cases s with
  | p l w => exact ⟨5,.q l w,by omega,rel_exact (pToQ l (suffix w))⟩
  | q l w =>
    cases w with
    | last n =>
      obtain ⟨t,ht,z,hz,he⟩ := qDrain l n []
      refine ⟨t,.p (afterDrain l).1 (.more 0 (afterDrain l).2 (.last (n+3))),ht,?_⟩
      have H : EqZ ⟨0,qLeft l,false::(U (n+2)++[false,false])⟩ (cfg (.q l (.last n))) := by
        refine ⟨rfl,eqL_refl _,eqL_cons false ?_⟩
        simpa only [cfg,suffix,U,rep,List.nil_append,List.cons_append,List.append_nil] using eqL_append (U (n+2)) (show EqL [false,false] [] from eqL_zero 2)
      obtain ⟨w,hw,hew⟩ := eqZ_run table t H hz
      refine ⟨w,hw,eqZ_trans (eqZ_symm hew) ?_⟩
      simpa only [cfg,suffix,U,rep,List.nil_append,List.append_nil,List.cons_append,List.append_assoc] using he
    | more n g w =>
      cases g with
      | zero =>
        refine ⟨3*n+7,.p (afterPush n l) w,by omega,rel_exact ?_⟩
        simpa only [cfg,suffix,U,V,rep,List.nil_append,List.cons_append,List.append_assoc] using qPush l n (suffix w)
      | succ g =>
        obtain ⟨t,ht,h⟩ := qDrain l (3*n) (V (2*g+1)++true::suffix w)
        refine ⟨t,.p (afterDrain l).1 (.more 0 (afterDrain l).2 (.more (n+1) g w)),ht,?_⟩
        simp only [cfg,suffix]
        rw [show 2*(g+1)+1=2*g+1+1+1 by omega,show 3*(n+1)=3*n+3 by omega]
        simpa only [U,V,rep,List.nil_append,List.cons_append,List.append_assoc] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have first : run0 table 8 ⟨0,[],[]⟩ = some (cfg (.p .empty (.more 0 0 (.last 1)))) := by rfl
  have arbitrary : ∀ k : Nat, ∃ t z u, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ EqZ (cfg u) z := by
    intro k
    induction k with
    | zero => exact ⟨8,_,.p .empty (.more 0 0 (.last 1)),by omega,first,eqZ_refl _⟩
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
end BB6.Agent8Raw54.LA.M104
