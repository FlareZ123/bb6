import AlternatingVariants

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent50OnesSweep
open BB6Coverage Agent50Zipper Agent50AlternatingSweep

def table (i : Fin 4) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,true => some (some (match i.val with
      | 0 => ⟨true,false,2⟩
      | 1 => ⟨true,true,3⟩
      | 2 => ⟨true,false,4⟩
      | _ => ⟨true,false,5⟩))
  | 2,true => some (some ⟨true,true,1⟩)
  | 5,false => none
  | _,_ => Agent50AlternatingSweep.table true s

def cost (i : Fin 4) : Nat := match i.val with
  | 0 => 8
  | 1 => 12
  | _ => 4

theorem first0 (i : Fin 4) : zrun (table i) 9 (family 0 0) = some (family 2 (-1)) := rfl

theorem prelude0 (i : Fin 4) (R : List Bool) :
    zrun (table i) 2 ⟨0,0,[],P++R⟩ = some ⟨2,2,true::K,R⟩ := rfl

theorem prelude (i : Fin 4) (h : Int) (R : List Bool) :
    zrun (table i) 2 ⟨0,h,[],P++R⟩ = some ⟨2,h+2,true::K,R⟩ := by
  have H := zrun_shift (table i) h 2 ⟨0,0,[],P++R⟩
  rw [prelude0] at H
  simpa [shift,Int.add_comm] using H

theorem rightOne0 (i : Fin 4) (L R : List Bool) :
    zrun (table i) 2 ⟨2,0,true::L,P++R⟩ = some ⟨2,2,true::(K++L),R⟩ := rfl

theorem rightOne (i : Fin 4) (h : Int) (L R : List Bool) :
    zrun (table i) 2 ⟨2,h,true::L,P++R⟩ = some ⟨2,h+2,true::(K++L),R⟩ := by
  have H := zrun_shift (table i) h 2 ⟨2,0,true::L,P++R⟩
  rw [rightOne0] at H
  simpa [shift,Int.add_comm] using H

theorem rightSweep (i : Fin 4) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table i) (2*n) ⟨2,h,true::L,rep P n++R⟩ =
      some ⟨2,h+2*(n:Int),true::(rep K n++L),R⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (rightOne i h L (rep P n++R)) (ih (h+2) (K++L))
    rw [show 2*(n+1)=2+2*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep K n) K L,rep_snoc K n,
      Int.natCast_succ,show h+2+2*(n:Int)=h+2*((n:Int)+1) by omega] using H

theorem turn0 (i : Fin 4) (L : List Bool) :
    zrun (table i) 9 ⟨2,0,true::L,[]⟩ = some ⟨0,-1,L,P++P⟩ := rfl

theorem turn (i : Fin 4) (h : Int) (L : List Bool) :
    zrun (table i) 9 ⟨2,h,true::L,[]⟩ = some ⟨0,h-1,L,P++P⟩ := by
  have H := zrun_shift (table i) h 9 ⟨2,0,true::L,[]⟩
  rw [turn0] at H
  simpa [shift,show -1+h=h-1 by omega] using H

theorem leftPair0 (i : Fin 4) (L R : List Bool) :
    zrun (table i) (cost i) ⟨0,0,K++K++L,P++R⟩ = some ⟨0,-4,L,P++P++P++R⟩ := by
  rcases i with ⟨i,hi⟩
  have H : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases H with h|h|h|h <;> subst i <;> rfl

theorem leftPair (i : Fin 4) (h : Int) (L R : List Bool) :
    zrun (table i) (cost i) ⟨0,h,K++K++L,P++R⟩ = some ⟨0,h-4,L,P++P++P++R⟩ := by
  have H := zrun_shift (table i) h (cost i) ⟨0,0,K++K++L,P++R⟩
  rw [leftPair0] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem leftSweep (i : Fin 4) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table i) (cost i*n) ⟨0,h,rep (K++K) n++L,P++R⟩ =
      some ⟨0,h-4*(n:Int),L,P++rep (P++P) n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H0 := leftPair i h (rep (K++K) n++L) R
    simp only [List.append_assoc] at H0
    have H := join H0 (ih (h-4) (P++P++R))
    rw [Nat.mul_succ,Nat.add_comm]
    have hw := congrArg (fun x : List Bool => x ++ R) (rep_snoc (P++P) n)
    simp only [List.append_assoc] at hw
    simpa only [rep,List.append_assoc,hw,Int.natCast_succ,
      show h-4-4*(n:Int)=h-4*((n:Int)+1) by omega] using H

theorem growth (i : Fin 4) (n : Nat) (h : Int) :
    ∃ t, 0 < t ∧ zrun (table i) t (family (2*n+2) h) = some (family (2*n+4) (h-1)) := by
  let m := 2*n+1
  have h1 := prelude i h (rep P m)
  have h2 := rightSweep i m (h+2) K []
  simp only [List.append_nil] at h2
  have h3 := turn i (h+2+2*(m:Int)) (rep K m++K)
  have h4 := leftSweep i (n+1) (h+2+2*(m:Int)-1) [] P
  simp only [← Agent50AlternatingVariants.rep_double,List.append_nil] at h4
  have he : rep K m++K = rep K (2*(n+1)) := by
    rw [rep_snoc K m,show 2*(n+1)=m+1 by dsimp [m]; omega]
    rfl
  rw [he] at h2 h3
  have H := join (join (join h1 h2) h3) h4
  have hr : P++rep P (2*(n+1))++P = rep P (2*n+4) := by
    rw [List.append_assoc,rep_snoc,show 2*n+4=2*(n+1)+2 by omega]
    rfl
  rw [hr] at H
  refine ⟨2+2*m+9+cost i*(n+1),by omega,?_⟩
  simpa only [family,rep,show m=2*n+1 by rfl,show 2*n+2=(2*n)+1+1 by omega,
    Int.natCast_succ,show h+2+2*((↑(2*n:Nat):Int)+1)-1-4*((n:Int)+1)=h-1 by omega] using H

theorem arbitraryRun (i : Fin 4) (n : Nat) :
    ∃ t h, n ≤ t ∧ zrun (table i) t (family 0 0) = some (family (2*n+2) h) := by
  induction n with
  | zero => exact ⟨9,-1,by decide,first0 i⟩
  | succ n ih =>
    obtain ⟨t,h,ht,hr⟩ := ih
    obtain ⟨u,hu,hg⟩ := growth i n h
    exact ⟨t+u,h-1,by omega,by simpa only [show 2*(n+1)+2=2*n+4 by omega] using join hr hg⟩

theorem never (i : Fin 4) (m : Machine) (hm : compatible (table i) m) : NeverHalts m := by
  intro n
  obtain ⟨t,h,ht,hr⟩ := arbitraryRun i n
  have H := zrun_sound (table i) m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms growth
#print axioms never
end BB6Coverage.Agent50OnesSweep

namespace BB6Coverage.Agent50TripleSweep
open BB6Coverage Agent50Zipper Agent50AlternatingSweep

def table (w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,true => some (some (if w then ⟨true,false,3⟩ else ⟨false,false,1⟩))
  | 2,true => some (some ⟨true,true,0⟩)
  | 5,false => none
  | _,_ => Agent50AlternatingSweep.table true s

def T : List Bool := [false,true,false]
def J : List Bool := [true,true,true]
def suffix (b : Bool) : List Bool := if b then P else P++P
def leftForm (n : Nat) : List Bool := if n=0 then [] else false::rep J n
def fam (n : Nat) (b : Bool) (h : Int) : Z := ⟨0,h,[],rep T n++suffix b⟩
def cost (w : Bool) : Nat := if w then 5 else 3

theorem first0 (w : Bool) : zrun (table w) 9 ⟨0,0,[],[]⟩ = some (fam 0 false (-1)) := rfl

theorem rightOne0 (w : Bool) (L R : List Bool) :
    zrun (table w) 3 ⟨0,0,false::L,T++false::R⟩ = some ⟨0,3,false::(J++L),false::R⟩ := rfl

theorem rightOne (w : Bool) (h : Int) (L R : List Bool) :
    zrun (table w) 3 ⟨0,h,false::L,T++false::R⟩ = some ⟨0,h+3,false::(J++L),false::R⟩ := by
  have H := zrun_shift (table w) h 3 ⟨0,0,false::L,T++false::R⟩
  rw [rightOne0] at H
  simpa [shift,Int.add_comm] using H

theorem rightSweep (w : Bool) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table w) (3*n) ⟨0,h,false::L,rep T n++false::R⟩ =
      some ⟨0,h+3*(n:Int),false::(rep J n++L),false::R⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have hR : rep T n++false::R = false::(if n=0 then R else [true,false]++rep T (n-1)++false::R) := by
      cases n <;> rfl
    have H1 := rightOne w h L (if n=0 then R else [true,false]++rep T (n-1)++false::R)
    rw [← hR] at H1
    have H := join H1 (ih (h+3) (J++L))
    rw [show 3*(n+1)=3+3*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep J n) J L,rep_snoc J n,
      Int.natCast_succ,show h+3+3*(n:Int)=h+3*((n:Int)+1) by omega] using H

theorem rightStart0 (w : Bool) (R : List Bool) :
    zrun (table w) 3 ⟨0,0,[],T++false::R⟩ = some ⟨0,3,false::J,false::R⟩ := rfl

theorem rightStart (w : Bool) (h : Int) (R : List Bool) :
    zrun (table w) 3 ⟨0,h,[],T++false::R⟩ = some ⟨0,h+3,false::J,false::R⟩ := by
  have H := zrun_shift (table w) h 3 ⟨0,0,[],T++false::R⟩
  rw [rightStart0] at H
  simpa [shift,Int.add_comm] using H

theorem rightAll (w : Bool) (n : Nat) (h : Int) (R : List Bool) :
    zrun (table w) (3*n) ⟨0,h,[],rep T n++false::R⟩ =
      some ⟨0,h+3*(n:Int),leftForm n,false::R⟩ := by
  cases n with
  | zero => simp [rep,zrun,leftForm]
  | succ n =>
    have hR : rep T n++false::R = false::(if n=0 then R else [true,false]++rep T (n-1)++false::R) := by
      cases n <;> rfl
    have H1 := rightStart w h (if n=0 then R else [true,false]++rep T (n-1)++false::R)
    rw [← hR] at H1
    have H := join H1 (rightSweep w n (h+3) J R)
    rw [show 3*(n+1)=3+3*n by omega]
    simpa only [rep,List.append_assoc,rep_snoc J n,leftForm,Nat.succ_ne_zero,if_false,
      Int.natCast_succ,show h+3+3*(n:Int)=h+3*((n:Int)+1) by omega] using H

theorem turn0 (w : Bool) (b : Bool) (n : Nat) :
    zrun (table w) (if b then 12 else 6) ⟨0,0,leftForm n,suffix b⟩ =
      some ⟨0,2,rep J (n+1),suffix (!b)⟩ := by
  cases b <;> cases n <;> rfl

theorem turn (w : Bool) (b : Bool) (n : Nat) (h : Int) :
    zrun (table w) (if b then 12 else 6) ⟨0,h,leftForm n,suffix b⟩ =
      some ⟨0,h+2,rep J (n+1),suffix (!b)⟩ := by
  have H := zrun_shift (table w) h (if b then 12 else 6) ⟨0,0,leftForm n,suffix b⟩
  rw [turn0] at H
  simpa [shift,Int.add_comm] using H

theorem leftOne0 (w : Bool) (L R : List Bool) :
    zrun (table w) (cost w) ⟨0,0,J++L,R⟩ = some ⟨0,-3,L,T++R⟩ := by cases w <;> rfl

theorem leftOne (w : Bool) (h : Int) (L R : List Bool) :
    zrun (table w) (cost w) ⟨0,h,J++L,R⟩ = some ⟨0,h-3,L,T++R⟩ := by
  have H := zrun_shift (table w) h (cost w) ⟨0,0,J++L,R⟩
  rw [leftOne0] at H
  simpa [shift,show -3+h=h-3 by omega] using H

theorem leftSweep (w : Bool) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table w) (cost w*n) ⟨0,h,rep J n++L,R⟩ =
      some ⟨0,h-3*(n:Int),L,rep T n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftOne w h (rep J n++L) R) (ih (h-3) (T++R))
    rw [Nat.mul_succ,Nat.add_comm]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep T n) T R,rep_snoc T n,
      Int.natCast_succ,show h-3-3*(n:Int)=h-3*((n:Int)+1) by omega] using H

theorem growth (w : Bool) (b : Bool) (n : Nat) (h : Int) :
    ∃ t, 0 < t ∧ zrun (table w) t (fam n b h) = some (fam (n+1) (!b) (h-1)) := by
  have h1 : zrun (table w) (3*n) (fam n b h) = some ⟨0,h+3*(n:Int),leftForm n,suffix b⟩ := by
    cases b
    · exact rightAll w n h [true,false,true]
    · exact rightAll w n h [true]
  have h2 := turn w b n (h+3*(n:Int))
  have h3 := leftSweep w (n+1) (h+3*(n:Int)+2) [] (suffix (!b))
  simp only [List.append_nil] at h3
  have H := join (join h1 h2) h3
  refine ⟨3*n+(if b then 12 else 6)+cost w*(n+1),by cases b <;> simp <;> omega,?_⟩
  simpa only [fam,Int.natCast_succ,show h+3*(n:Int)+2-3*((n:Int)+1)=h-1 by omega] using H

theorem arbitraryRun (w : Bool) (n : Nat) :
    ∃ t b h, n ≤ t ∧ zrun (table w) t (family 0 0) = some (fam n b h) := by
  induction n with
  | zero => exact ⟨9,false,-1,by decide,first0 w⟩
  | succ n ih =>
    obtain ⟨t,b,h,ht,hr⟩ := ih
    obtain ⟨u,hu,hg⟩ := growth w b n h
    exact ⟨t+u,!b,h-1,by omega,join hr hg⟩

theorem never (w : Bool) (m : Machine) (hm : compatible (table w) m) : NeverHalts m := by
  intro n
  obtain ⟨t,b,h,ht,hr⟩ := arbitraryRun w n
  have H := zrun_sound (table w) m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms growth
#print axioms never
end BB6Coverage.Agent50TripleSweep
