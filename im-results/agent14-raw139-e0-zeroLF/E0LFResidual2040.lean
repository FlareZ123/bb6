import SparseZipper
import FastThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent14E0LFResidual2040
open BB6Coverage Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := List.replicate n true
def zeros (n : Nat) : List Bool := List.replicate n false
theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m :=
  List.replicate_append_replicate.symm
theorem zeros_add (n m : Nat) : zeros (n+m) = zeros n ++ zeros m :=
  List.replicate_append_replicate.symm
theorem ones_succ (n : Nat) : ones (n+1) = true::ones n := by
  rw [show n+1=1+n by omega,ones_add];rfl
theorem zeros_succ (n : Nat) : zeros (n+1) = false::zeros n := by
  rw [show n+1=1+n by omega,zeros_add];rfl

def atR (q : Fin 6) (h : Int) (L R : List Bool) : Z :=
  ⟨q,h,R.headD false::L,R.tail⟩
def entry (n : Nat) (h : Int) (L R : List Bool) : Z :=
  ⟨0,h,false::L,ones n ++ false::false::R⟩
def exit (n : Nat) (h : Int) (L R : List Bool) : Z :=
  ⟨5,h,L,ones n ++ false::false::R⟩

def Reach (a b : Z) : Prop := ∃ n, zrun table n a = some b
theorem reach_of {a b : Z} {n : Nat} (h : zrun table n a = some b) : Reach a b := ⟨n,h⟩
theorem reach_join {a b c : Z} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨k,hk⟩ := g
  exact ⟨n+k,join hn hk⟩

theorem prep (h : Int) (L R : List Bool) :
    zrun table 1 ⟨0,h,false::L,R⟩ = some (atR 1 (h+1) (true::L) R) := by rfl

theorem eraseStep (h : Int) (L R : List Bool) :
    zrun table 1 (atR 1 h L (true::R)) =
      some (atR 1 (h+1) (false::L) R) := by rfl

theorem keepStep (h : Int) (L R : List Bool) :
    zrun table 1 (atR 0 h L (true::R)) =
      some (atR 0 (h+1) (true::L) R) := by rfl

theorem fKeep (h : Int) (L R : List Bool) :
    zrun table 1 ⟨5,h,true::L,R⟩ = some ⟨5,h-1,L,true::R⟩ := by rfl

theorem fWrite (h : Int) (L R : List Bool) :
    zrun table 1 ⟨5,h,false::L,R⟩ = some ⟨0,h-1,L,true::R⟩ := by rfl

theorem eraseRight (n : Nat) (h : Int) (L R : List Bool) :
    zrun table n (atR 1 h L (ones n++R)) =
      some (atR 1 (h+(n:Int)) (zeros n++L) R) := by
  induction n generalizing h L with
  | zero => simp [ones,zeros,zrun]
  | succ n ih =>
    have H := join (eraseStep h L (ones n++R)) (ih (h+1) (false::L))
    rw [show n+1=1+n by omega]
    have hi : ones (1+n)++R = true::(ones n++R) := by
      rw [ones_add,List.append_assoc];rfl
    have hl : zeros n++false::L = zeros (1+n)++L := by
      rw [show 1+n=n+1 by omega,zeros_add,List.append_assoc];rfl
    simpa only [hi,hl,Int.natCast_add,Int.natCast_one,show h+1+(n:Int)=h+(1+(n:Int)) by omega] using H

theorem keepRight (n : Nat) (h : Int) (L R : List Bool) :
    zrun table n (atR 0 h L (ones n++R)) =
      some (atR 0 (h+(n:Int)) (ones n++L) R) := by
  induction n generalizing h L with
  | zero => simp [ones,zrun]
  | succ n ih =>
    have H := join (keepStep h L (ones n++R)) (ih (h+1) (true::L))
    rw [show n+1=1+n by omega]
    have hi : ones (1+n)++R = true::(ones n++R) := by
      rw [ones_add,List.append_assoc];rfl
    have hl : ones n++true::L = ones (1+n)++L := by
      rw [show 1+n=n+1 by omega,ones_add,List.append_assoc];rfl
    simpa only [hi,hl,Int.natCast_add,Int.natCast_one,show h+1+(n:Int)=h+(1+(n:Int)) by omega] using H

theorem keepLeft (n : Nat) (h : Int) (L R : List Bool) :
    zrun table n ⟨5,h,ones n++L,R⟩ =
      some ⟨5,h-(n:Int),L,ones n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [ones,zrun]
  | succ n ih =>
    have H := join (fKeep h (ones n++L) R) (ih (h-1) (true::R))
    rw [show n+1=1+n by omega]
    have hi : ones (1+n)++L = true::(ones n++L) := by
      rw [ones_add,List.append_assoc];rfl
    have hr : ones n++true::R = ones (1+n)++R := by
      rw [show 1+n=n+1 by omega,ones_add,List.append_assoc];rfl
    simpa only [hi,hr,Int.natCast_add,Int.natCast_one,show h-1-(n:Int)=h-(1+(n:Int)) by omega] using H

theorem turnI0 (L R : List Bool) :
    zrun table 4 ⟨1,0,false::false::L,false::R⟩ =
      some ⟨5,-2,L,false::false::true::R⟩ := by rfl

theorem turnI (h : Int) (L R : List Bool) :
    zrun table 4 ⟨1,h,false::false::L,false::R⟩ =
      some ⟨5,h-2,L,false::false::true::R⟩ := by
  have H := zrun_shift table h 4 ⟨1,0,false::false::L,false::R⟩
  rw [turnI0] at H
  simpa [shift,show -2+h=h-2 by omega] using H

theorem turnII0 (L R : List Bool) :
    zrun table 5 ⟨0,0,false::L,false::true::true::R⟩ =
      some ⟨5,1,true::true::L,false::false::R⟩ := by rfl

theorem turnII (h : Int) (L R : List Bool) :
    zrun table 5 ⟨0,h,false::L,false::true::true::R⟩ =
      some ⟨5,h+1,true::true::L,false::false::R⟩ := by
  have H := zrun_shift table h 5 ⟨0,0,false::L,false::true::true::R⟩
  rw [turnII0] at H
  simpa [shift,Int.add_comm] using H

/-- Elementary run I, before the final F transition. -/
theorem firstPass (m : Nat) (h : Int) (L R : List Bool) :
    Reach (entry (m+1) h L R)
      ⟨5,h+(m:Int),zeros m++true::L,false::false::true::R⟩ := by
  have h1 := prep h L (ones (m+1)++false::false::R)
  have h2 := eraseRight (m+1) (h+1) (true::L) (false::false::R)
  have h3 := turnI (h+1+((m+1:Nat):Int)) (zeros m++true::L) R
  have h2' : zrun table (m+1) (atR 1 (h+1) (true::L) (ones (m+1)++false::false::R)) =
      some ⟨1,h+1+((m+1:Nat):Int),false::false::(zeros m++true::L),false::R⟩ := by
    simpa [atR,zeros_succ] using h2
  have H := join (join h1 h2') h3
  exact reach_of (show zrun table (1+(m+1)+4) (entry (m+1) h L R) =
      some ⟨5,h+(m:Int),zeros m++true::L,false::false::true::R⟩ from by
    simpa only [entry,show h+1+((m+1:Nat):Int)-2=h+(m:Int) by omega] using H)

/-- Elementary run II: the two terminal ones are consumed. -/
theorem secondPass (b : Nat) (h : Int) (L R : List Bool) :
    Reach (atR 0 h L (ones b++false::false::true::true::R))
      (exit (b+2) (h-1) L R) := by
  have h1 := keepRight b h L (false::false::true::true::R)
  have h1' : zrun table b (atR 0 h L (ones b++false::false::true::true::R)) =
      some ⟨0,h+(b:Int),false::(ones b++L),false::true::true::R⟩ := by
    simpa [atR] using h1
  have h2 := turnII (h+(b:Int)) (ones b++L) R
  have h3 := keepLeft (b+2) (h+(b:Int)+1) L (false::false::R)
  have hl : ones (b+2)++L = true::true::(ones b++L) := by
    rw [show b+2=2+b by omega,ones_add,List.append_assoc];rfl
  rw [hl] at h3
  have H := join (join h1' h2) h3
  exact reach_of (show zrun table (b+5+(b+2)) (atR 0 h L (ones b++false::false::true::true::R)) =
      some (exit (b+2) (h-1) L R) from by
    simpa only [exit,show h+(b:Int)+1-((b+2:Nat):Int)=h-1 by omega] using H)

theorem Ione (h : Int) (L R : List Bool) :
    Reach (entry 1 h L R) (exit 1 (h-1) L (true::R)) := by
  have h1 : Reach (entry 1 h L R) ⟨5,h,true::L,false::false::true::R⟩ := by
    simpa [zeros] using firstPass 0 h L R
  exact reach_join h1 (reach_of (fKeep h L (false::false::true::R)))

theorem Itwo (h : Int) (L R : List Bool) :
    Reach (entry 2 h L R) (atR 0 h L (ones 2++false::false::true::R)) := by
  have h1 : Reach (entry 2 h L R) ⟨5,h+1,false::true::L,false::false::true::R⟩ := by
    simpa [zeros] using firstPass 1 h L R
  have h2 := fWrite (h+1) (true::L) (false::false::true::R)
  have h2' : zrun table 1 ⟨5,h+1,false::true::L,false::false::true::R⟩ =
      some (atR 0 h L (ones 2++false::false::true::R)) := by
    simpa [atR,ones,show h+1-1=h by omega] using h2
  exact reach_join h1 (reach_of h2')

theorem Ibig (m : Nat) (h : Int) (L R : List Bool) :
    Reach (entry (m+3) h L R)
      (entry 1 (h+(m:Int)+1) (zeros m++true::L) (true::R)) := by
  have h1 := firstPass (m+2) h L R
  have hl : zeros (m+2)++true::L = false::false::(zeros m++true::L) := by
    rw [show m+2=2+m by omega,zeros_add,List.append_assoc];rfl
  rw [hl] at h1
  have h2 := fWrite (h+((m+2:Nat):Int)) (false::(zeros m++true::L)) (false::false::true::R)
  have h2' : zrun table 1 ⟨5,h+((m+2:Nat):Int),false::false::(zeros m++true::L),false::false::true::R⟩ =
      some (entry 1 (h+(m:Int)+1) (zeros m++true::L) (true::R)) := by
    simpa [entry,ones,show h+((m+2:Nat):Int)-1=h+(m:Int)+1 by omega] using h2
  exact reach_join h1 (reach_of h2')

def First1 (k : Nat) : Prop :=
  ∀ h L R, Reach (entry (4*k+1) h L (true::true::R))
    (exit (4*k+1) (h-1) L (true::true::true::R))

def First2 (k : Nat) : Prop :=
  ∀ h L R, Reach (entry (4*k+2) h L (true::true::R))
    (exit (4*k+4) (h-1) L (true::R))

theorem advance1 (k : Nat) (H : First1 k) (h : Int) (L R : List Bool) :
    Reach (entry (4*k+1) h (false::false::L) (true::true::R))
      (entry (4*k+2) (h-2) L (true::true::true::R)) := by
  have h1 := H h (false::false::L) R
  have h2 := fWrite (h-1) (false::L) (ones (4*k+1)++false::false::true::true::true::R)
  have h2' : zrun table 1 (exit (4*k+1) (h-1) (false::false::L) (true::true::true::R)) =
      some (entry (4*k+2) (h-2) L (true::true::true::R)) := by
    simpa [entry,exit,ones_succ,show h-1-1=h-2 by omega] using h2
  exact reach_join h1 (reach_of h2')

theorem advance2 (k : Nat) (H : First2 k) (h : Int) (L R : List Bool) :
    Reach (entry (4*k+2) h (false::false::L) (true::true::true::R))
      (entry (4*k+5) (h-2) L (true::true::R)) := by
  have h1 := H h (false::false::L) (true::R)
  have h2 := fWrite (h-1) (false::L) (ones (4*k+4)++false::false::true::true::R)
  have h2' : zrun table 1 (exit (4*k+4) (h-1) (false::false::L) (true::true::R)) =
      some (entry (4*k+5) (h-2) L (true::true::R)) := by
    simpa [entry,exit,ones_succ,show h-1-1=h-2 by omega] using h2
  exact reach_join h1 (reach_of h2')

theorem consumePairs (k : Nat) (H : ∀ j < k, First1 j ∧ First2 j)
    (h : Int) (L R : List Bool) :
    Reach (entry 1 h (zeros (4*k)++L) (true::true::R))
      (entry (4*k+1) (h-4*(k:Int)) L (true::true::R)) := by
  induction k generalizing h L with
  | zero => exact ⟨0,by simp [entry,zeros,zrun]⟩
  | succ k ih =>
    have h0 := ih (fun j hj => H j (by omega)) h (false::false::false::false::L)
    have h1 := advance1 k (H k (by omega)).1 (h-4*(k:Int)) (false::false::L) R
    have h2 := advance2 k (H k (by omega)).2 (h-4*(k:Int)-2) L R
    have Z : zeros (4*(k+1))++L = zeros (4*k)++false::false::false::false::L := by
      rw [show 4*(k+1)=4*k+4 by omega,zeros_add,List.append_assoc];rfl
    have J := reach_join (reach_join h0 h1) h2
    simpa only [Z,show 4*(k+1)+1=4*k+5 by omega,Int.natCast_succ,
      show h-4*(k:Int)-2-2=h-4*((k:Int)+1) by omega] using J

theorem families (k : Nat) : First1 k ∧ First2 k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      constructor
      · intro h L R
        exact Ione h L (true::true::R)
      · intro h L R
        exact reach_join (Itwo h L (true::true::R)) (secondPass 2 h L (true::R))
    | succ k =>
      have prev : ∀ j < k, First1 j ∧ First2 j := fun j hj => ih j (by omega)
      have hk := ih k (by omega)
      constructor
      · intro h L R
        have h0 := Ibig (4*k+2) h L (true::true::R)
        have h1 := consumePairs k prev (h+3+4*(k:Int)) (false::false::true::L) (true::R)
        have hz : zeros (4*k+2)++true::L = zeros (4*k)++false::false::true::L := by
          rw [zeros_add,List.append_assoc];rfl
        have h0' : Reach (entry (4*(k+1)+1) h L (true::true::R))
            (entry 1 (h+3+4*(k:Int)) (zeros (4*k)++false::false::true::L) (true::true::true::R)) := by
          simpa only [hz,show 4*k+2+3=4*(k+1)+1 by omega,
            show h+((4*k+2:Nat):Int)+1=h+3+4*(k:Int) by omega] using h0
        have h1' : Reach (entry 1 (h+3+4*(k:Int)) (zeros (4*k)++false::false::true::L) (true::true::true::R))
            (entry (4*k+1) (h+3) (false::false::true::L) (true::true::true::R)) := by
          simpa only [show h+3+4*(k:Int)-4*(k:Int)=h+3 by omega] using h1
        have h2 := advance1 k hk.1 (h+3) (true::L) (true::R)
        have h3 := hk.2 (h+1) (true::L) (true::true::R)
        have h2' : Reach (entry (4*k+1) (h+3) (false::false::true::L) (true::true::true::R))
            (entry (4*k+2) (h+1) (true::L) (true::true::true::true::R)) := by
          simpa only [show h+3-2=h+1 by omega] using h2
        have h3' : Reach (entry (4*k+2) (h+1) (true::L) (true::true::true::true::R))
            (exit (4*k+4) h (true::L) (true::true::true::R)) := by
          simpa only [show h+1-1=h by omega] using h3
        have h4 := fKeep h L (ones (4*k+4)++false::false::true::true::true::R)
        have h4' : zrun table 1 (exit (4*k+4) h (true::L) (true::true::true::R)) =
            some (exit (4*(k+1)+1) (h-1) L (true::true::true::R)) := by
          simpa [exit,show 4*(k+1)+1=4*k+4+1 by omega,ones_succ] using h4
        exact reach_join (reach_join (reach_join (reach_join h0' h1') h2') h3') (reach_of h4')
      · intro h L R
        have h0 := Ibig (4*k+3) h L (true::true::R)
        have h1 := consumePairs k prev (h+4+4*(k:Int)) (false::false::false::true::L) (true::R)
        have hz : zeros (4*k+3)++true::L = zeros (4*k)++false::false::false::true::L := by
          rw [zeros_add,List.append_assoc];rfl
        have h0' : Reach (entry (4*(k+1)+2) h L (true::true::R))
            (entry 1 (h+4+4*(k:Int)) (zeros (4*k)++false::false::false::true::L) (true::true::true::R)) := by
          simpa only [hz,show 4*k+3+3=4*(k+1)+2 by omega,
            show h+((4*k+3:Nat):Int)+1=h+4+4*(k:Int) by omega] using h0
        have h1' : Reach (entry 1 (h+4+4*(k:Int)) (zeros (4*k)++false::false::false::true::L) (true::true::true::R))
            (entry (4*k+1) (h+4) (false::false::false::true::L) (true::true::true::R)) := by
          simpa only [show h+4+4*(k:Int)-4*(k:Int)=h+4 by omega] using h1
        have h2 := advance1 k hk.1 (h+4) (false::true::L) (true::R)
        have h2' : Reach (entry (4*k+1) (h+4) (false::false::false::true::L) (true::true::true::R))
            (entry (4*k+2) (h+2) (false::true::L) (true::true::true::true::R)) := by
          simpa only [show h+4-2=h+2 by omega] using h2
        have h3 := hk.2 (h+2) (false::true::L) (true::true::R)
        have h3' : Reach (entry (4*k+2) (h+2) (false::true::L) (true::true::true::true::R))
            (exit (4*k+4) (h+1) (false::true::L) (true::true::true::R)) := by
          simpa only [show h+2-1=h+1 by omega] using h3
        have h4 := fWrite (h+1) (true::L) (ones (4*k+4)++false::false::true::true::true::R)
        have h4' : zrun table 1 (exit (4*k+4) (h+1) (false::true::L) (true::true::true::R)) =
            some (atR 0 h L (ones (4*k+6)++false::false::true::true::true::R)) := by
          have hl : ones (4*k+6) = true::true::ones (4*k+4) := by
            rw [show 4*k+6=2+(4*k+4) by omega,ones_add];rfl
          simpa [exit,atR,hl,show h+1-1=h by omega] using h4
        have h5 := secondPass (4*k+6) h L (true::R)
        have h5' : Reach (atR 0 h L (ones (4*k+6)++false::false::true::true::true::R))
            (exit (4*(k+1)+4) (h-1) L (true::R)) := by
          simpa only [show 4*k+6+2=4*(k+1)+4 by omega] using h5
        exact reach_join (reach_join (reach_join (reach_join (reach_join h0' h1') h2') h3') (reach_of h4')) h5'

def X (k : Nat) (h : Int) : Z := ⟨0,h,[],ones (4*k+1)++[false,false,true,true]⟩
def Y (k : Nat) (h : Int) : Z := ⟨0,h,[],ones (4*k+2)++[false,false,true,true,true]⟩

theorem emptyLeft {h : Int} {R : List Bool} {n : Nat} :
    zrun table (n+1) ⟨0,h,[],R⟩ = zrun table (n+1) ⟨0,h,[false],R⟩ := by rfl

theorem xy (k : Nat) (h : Int) : ∃ n, 0<n ∧ zrun table n (X k h) = some (Y k (h-2)) := by
  obtain ⟨n,hn⟩ := (families k).1 h [] []
  cases n with
  | zero => simp [entry,exit,zrun] at hn
  | succ n =>
    have h1 : zrun table (n+1) (X k h) = some (exit (4*k+1) (h-1) [] [true,true,true]) := by
      rw [X,emptyLeft]
      exact hn
    have h2 : zrun table 1 (exit (4*k+1) (h-1) [] [true,true,true]) =
        some (Y k (h-2)) := by
      simp [exit,Y,ones_succ,zrun,step,table,move,show h-1-1=h-2 by omega]
    exact ⟨n+1+1,by omega,join h1 h2⟩

theorem yx (k : Nat) (h : Int) : ∃ n, 0<n ∧ zrun table n (Y k h) = some (X (k+1) (h-2)) := by
  obtain ⟨n,hn⟩ := (families k).2 h [] [true]
  cases n with
  | zero => simp [entry,exit,zrun] at hn
  | succ n =>
    have h1 : zrun table (n+1) (Y k h) = some (exit (4*k+4) (h-1) [] [true,true]) := by
      rw [Y,emptyLeft]
      exact hn
    have h2 : zrun table 1 (exit (4*k+4) (h-1) [] [true,true]) =
        some (X (k+1) (h-2)) := by
      simp [exit,X,show 4*(k+1)+1=4*k+4+1 by omega,ones_succ,zrun,step,table,move,show h-1-1=h-2 by omega]
    exact ⟨n+1+1,by omega,join h1 h2⟩

def start : Z := ⟨0,0,[],[]⟩
theorem first : zrun table 9 start = some (X 0 (-3)) := by rfl

theorem arbitraryRun (n : Nat) : ∃ t k h, n ≤ t ∧ zrun table t start = some (X k h) := by
  induction n with
  | zero => exact ⟨9,0,-3,by omega,first⟩
  | succ n ih =>
    obtain ⟨t,k,h,ht,hr⟩ := ih
    obtain ⟨a,ha,hxy⟩ := xy k h
    obtain ⟨b,hb,hyx⟩ := yx k (h-2)
    exact ⟨t+a+b,k+1,h-2-2,by omega,join (join hr hxy) hyx⟩

theorem start_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

theorem table_never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound table m hm t _ _ hr
  rw [start_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none =>
    have he' : run m n (emptyAt 0) = none := he
    simp [he'] at H
  | some c => rfl

def ctr : PartialMachine := FAR.fromCodes [7,3,11,5,14,13,24,16,20,11,2,22]
theorem same : ctr = table := BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  table_never m (by simpa only [← same] using hm)

#print axioms families
#print axioms arbitraryRun
#print axioms never
end BB6Coverage.Agent14E0LFResidual2040
