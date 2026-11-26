import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RBWord80
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def enc : List Bool → List Bool
  | [] => []
  | b::w => b::b::enc w
def blk (n : Nat) : List Bool := false::rep O (2*n+3)
def stack : List Nat → List Bool
  | [] => [false,true,true,true,true]
  | n::s => blk n ++ stack s
def modeL (m : Option Nat) (s : List Nat) : List Bool :=
  match m with
  | none => false::true::stack s
  | some n => blk n ++ stack s
def sec (w : List Bool) : Z0 := ⟨4,[],rep Z 6 ++ enc w⟩
def scan (m : Option Nat) (s : List Nat) (w : List Bool) : Z0 :=
  ⟨4,modeL m s,false::enc w⟩
def nextN (m : Option Nat) : Nat := match m with | none => 0 | some n => n+1

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem enc_zeros (k : Nat) (w : List Bool) :
    enc (List.replicate k false ++ w) = rep Z (2*k) ++ enc w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,enc,ih,show 2*(k+1)=2*k+2 by omega]
    rfl

theorem drainRaw (n : Nat) (L R : List Bool) :
    run0 table (n+10) ⟨4,false::(rep O (n+3) ++ L),false::false::false::R⟩ =
      some ⟨4,L,rep Z (n+5) ++ true::true::R⟩ := by
  have a : run0 table 6 ⟨4,false::(rep O (n+3) ++ L),false::false::false::R⟩ =
      some ⟨4,rep O (n+4) ++ L,false::true::true::R⟩ := by rfl
  have b := sweepL table 4 [] [] O Z 1 (by intro L R; rfl) (n+4) L (false::true::true::R)
  simp only [List.nil_append,Nat.one_mul] at b
  have H := join0 a b
  rw [show 6+(n+4)=n+10 by omega] at H
  simpa only [rep_add Z (n+4) 1,List.append_assoc,show rep Z 1 = [false] by rfl,List.cons_append,List.nil_append] using H

theorem drainRawBlank (n : Nat) (L : List Bool) :
    run0 table (n+10) ⟨4,false::(rep O (n+3) ++ L),[false]⟩ =
      some ⟨4,L,rep Z (n+5) ++ [true,true]⟩ := by
  have a : run0 table 6 ⟨4,false::(rep O (n+3) ++ L),[false]⟩ =
      some ⟨4,rep O (n+4) ++ L,[false,true,true]⟩ := by rfl
  have b : run0 table 6 ⟨4,false::(rep O (n+3) ++ L),[false,false,false]⟩ =
      some ⟨4,rep O (n+4) ++ L,[false,true,true]⟩ := by rfl
  have H := drainRaw n L []
  rw [show n+10=6+(n+4) by omega,run0_add,b] at H
  rw [show n+10=6+(n+4) by omega,run0_add,a]
  exact H

theorem drainBlock (n : Nat) (L : List Bool) (w : List Bool) :
    run0 table (2*n+10) ⟨4,blk n ++ L,false::false::false::enc w⟩ =
      some ⟨4,L,false::false::false::enc (List.replicate (n+1) false ++ true::w)⟩ := by
  have H := drainRaw (2*n) L (enc w)
  rw [show 2*n+5=3+2*(n+1) by omega,rep_add Z 3 (2*(n+1))] at H
  simpa only [blk,List.cons_append,enc_zeros,enc,List.append_assoc,show rep Z 3 = [false,false,false] by rfl,List.nil_append] using H

theorem drain (s : List Nat) (w : List Bool) :
    ∃ t, 0<t ∧ ∃ u, run0 table t ⟨4,stack s,false::false::false::enc w⟩ = some (sec u) := by
  induction s generalizing w with
  | nil =>
    refine ⟨11,by omega,true::w,?_⟩
    simpa only [stack,sec,enc,show rep O 4 = [true,true,true,true] by rfl,List.append_nil] using drainRaw 1 [] (enc w)
  | cons n s ih =>
    obtain ⟨t,ht,u,h⟩ := ih (List.replicate (n+1) false ++ true::w)
    exact ⟨2*n+10+t,by omega,u,join0 (drainBlock n (stack s) w) h⟩

theorem modeStop (m : Option Nat) (s : List Nat) (w : List Bool) :
    ∃ t, 0<t ∧ ∃ u, run0 table t (scan m s (false::w)) = some (sec u) := by
  cases m with
  | none =>
    have a : run0 table 8 (scan none s (false::w)) = some ⟨4,stack s,false::false::false::true::true::enc w⟩ := by rfl
    obtain ⟨t,ht,u,h⟩ := drain s (true::w)
    exact ⟨8+t,by omega,u,join0 a h⟩
  | some n => exact drain (n::s) w

theorem modeNil (m : Option Nat) (s : List Nat) :
    ∃ t, 0<t ∧ ∃ u, run0 table t (scan m s []) = some (sec u) := by
  cases m with
  | none =>
    have a : run0 table 8 (scan none s []) = some ⟨4,stack s,[false,false,false,true,true]⟩ := by rfl
    obtain ⟨t,ht,u,h⟩ := drain s [true]
    exact ⟨8+t,by omega,u,join0 a h⟩
  | some n =>
    have a := drainRawBlank (2*n) (stack s)
    rw [show 2*n+5=3+2*(n+1) by omega,rep_add Z 3 (2*(n+1))] at a
    have a' : run0 table (2*n+10) (scan (some n) s []) =
      some ⟨4,stack s,false::false::false::enc (List.replicate (n+1) false ++ [true])⟩ := by
      simpa only [scan,modeL,blk,List.cons_append,enc,enc_zeros,List.append_assoc,show rep Z 3 = [false,false,false] by rfl,List.nil_append] using a
    obtain ⟨t,ht,u,h⟩ := drain s (List.replicate (n+1) false ++ [true])
    exact ⟨2*n+10+t,by omega,u,join0 a' h⟩

theorem scanTF (m : Option Nat) (s : List Nat) (w : List Bool) :
    run0 table 4 (scan m s (true::false::w)) = some (scan none (nextN m::s) w) := by
  cases m <;> rfl

theorem scanTT (m : Option Nat) (s : List Nat) (w : List Bool) :
    run0 table 10 (scan m s (true::true::w)) = some (scan (some (nextN m+1)) s w) := by
  cases m with
  | none => rfl
  | some n =>
    rfl

theorem scanT (m : Option Nat) (s : List Nat) :
    run0 table 12 (scan m s [true]) = some ⟨4,stack (nextN m::s),[false,false,false,true,true]⟩ := by
  cases m <;> rfl

theorem scanAll (fuel : Nat) (m : Option Nat) (s : List Nat) (w : List Bool) (hw : w.length ≤ fuel) :
    ∃ t, 0<t ∧ ∃ u, run0 table t (scan m s w) = some (sec u) := by
  induction fuel generalizing m s w with
  | zero =>
    cases w with
    | nil => exact modeNil m s
    | cons b w => simp at hw
  | succ fuel ih =>
    cases w with
    | nil => exact modeNil m s
    | cons b w =>
      cases b with
      | false => exact modeStop m s w
      | true =>
        cases w with
        | nil =>
          obtain ⟨t,ht,u,h⟩ := drain (nextN m::s) [true]
          exact ⟨12+t,by omega,u,join0 (scanT m s) h⟩
        | cons b w =>
          have hw' : w.length ≤ fuel := by simp at hw; omega
          cases b with
          | false =>
            obtain ⟨t,ht,u,h⟩ := ih none (nextN m::s) w hw'
            exact ⟨4+t,by omega,u,join0 (scanTF m s w) h⟩
          | true =>
            obtain ⟨t,ht,u,h⟩ := ih (some (nextN m+1)) s w hw'
            exact ⟨10+t,by omega,u,join0 (scanTT m s w) h⟩

theorem sectionReturn (w : List Bool) : ∃ t, 0<t ∧ ∃ u, run0 table t (sec w) = some (sec u) := by
  have prep : run0 table 15 (sec w) = some ⟨0,modeL none [],false::enc w⟩ := by rfl
  obtain ⟨t,ht,u,h⟩ := scanAll w.length none [] w (by omega)
  have h' : run0 table t ⟨0,modeL none [],false::enc w⟩ = some (sec u) := by
    cases t with
    | zero => omega
    | succ t => exact h
  exact ⟨15+t,by omega,u,join0 prep h'⟩

theorem first : run0 table 34 ⟨0,[],[]⟩ = some (sec [true,true]) := by rfl

theorem arbitrary (k : Nat) : ∃ t, k≤t ∧ ∃ w, run0 table t ⟨0,[],[]⟩ = some (sec w) := by
  induction k with
  | zero => exact ⟨34,by omega,[true,true],first⟩
  | succ k ih =>
    obtain ⟨t,ht,w,h⟩ := ih
    obtain ⟨s,hs,u,g⟩ := sectionReturn w
    exact ⟨t+s,by omega,u,join0 h g⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,w,hr⟩ := arbitrary n
  have hz : (zrun table t start).map project = some (sec w) := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl
#print axioms sectionReturn
#print axioms never
end BB6.Agent8Raw54.RBWord80
