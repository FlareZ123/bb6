import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFRun34
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def encL : List Bool → List Bool | [] => [] | b::bs => b::b::encL bs
inductive Runs where
  | last : Nat → Runs
  | more : Nat → Nat → Runs → Runs

def encR : Runs → List Bool
  | .last n => rep O (2*n+2)
  | .more m g w => rep O (2*m+1) ++ rep Z (2*g+1) ++ encR w

def strip : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::bs => (0,bs)
  | true::bs => ((strip bs).1+1,(strip bs).2)
abbrev S := List Bool × Runs
def cfg (s : S) : Z0 := ⟨0,false::encL s.1,false::encR s.2⟩
def next : S → S
  | (bs,.last n) => ((strip bs).2,.more 0 (strip bs).1 (.last (n+1)))
  | (bs,.more m 0 w) => (List.replicate m false ++ true::bs,w)
  | (bs,.more m (g+1) w) => ((strip bs).2,.more 0 (strip bs).1 (.more (m+1) g w))
def cost : S → Nat
  | (bs,.last n) => 4*n+16+2*(strip bs).1
  | (_, .more m 0 _) => 2*m+10
  | (bs,.more m (_+1) _) => 4*m+14+2*(strip bs).1

theorem prep (n : Nat) (L T : List Bool) :
    run0 table (n+2) ⟨0,false::L,false::(rep O (n+1) ++ T)⟩ =
      some ⟨2,true::(rep Z n ++ true::true::L),T⟩ := by
  have a : run0 table 2 ⟨0,false::L,false::(rep O (n+1) ++ T)⟩ = some ⟨2,true::true::true::L,rep O n ++ T⟩ := by rfl
  have b := sweepR table 2 [true] [] O Z 1 (by intro L R; rfl) n (true::true::L) T
  simp only [List.nil_append,List.cons_append,Nat.one_mul] at b
  have H := join0 a b
  rw [show 2+n=n+2 by omega] at H
  exact H

theorem gap1 (n : Nat) (L T : List Bool) :
    run0 table (n+10) ⟨0,false::L,false::(rep O (n+1) ++ false::true::T)⟩ =
      some ⟨0,false::(rep Z n ++ true::true::L),false::true::T⟩ := by
  have a := prep n L (false::true::T)
  have b : run0 table 8 ⟨2,true::(rep Z n ++ true::true::L),false::true::T⟩ =
      some ⟨0,false::(rep Z n ++ true::true::L),false::true::T⟩ := by rfl
  have H := join0 a b
  rw [show n+2+8=n+10 by omega] at H
  exact H

theorem restore (bs : List Bool) (k : Nat) (T : List Bool) :
    run0 table (2*(strip bs).1+5) ⟨4,encL bs,false::false::(rep Z (2*k) ++ T)⟩ =
      some ⟨0,false::encL (strip bs).2,false::true::false::(rep Z (2*(k+(strip bs).1)) ++ T)⟩ := by
  induction bs generalizing k with
  | nil => simp only [strip,Nat.mul_zero,Nat.zero_add,Nat.add_zero]; rfl
  | cons b bs ih =>
    cases b
    · simp only [strip,Nat.mul_zero,Nat.zero_add,Nat.add_zero]; rfl
    · have a : run0 table 2 ⟨4,encL (true::bs),false::false::(rep Z (2*k) ++ T)⟩ =
          some ⟨4,encL bs,false::false::(rep Z (2*(k+1)) ++ T)⟩ := by
        rw [show 2*(k+1)=2*k+2 by omega]; rfl
      have H := join0 a (ih (k+1))
      rw [show 2+(2*(strip bs).1+5)=2*(strip (true::bs)).1+5 by simp [strip]; omega,
        show 2*(k+1+(strip bs).1)=2*(k+(strip (true::bs)).1) by simp [strip]; omega] at H
      exact H

theorem resetD (n : Nat) (bs : List Bool) (T : List Bool) :
    run0 table (n+10+2*(strip bs).1) ⟨3,rep Z (n+3) ++ true::true::encL bs,T⟩ =
      some ⟨0,false::encL (strip bs).2,false::true::false::(rep Z (2*(strip bs).1) ++ (rep O (n+3) ++ T))⟩ := by
  have a := sweepL table 3 [] [] Z O 1 (by intro L R; rfl) (n+3) (true::true::encL bs) T
  simp only [List.nil_append,Nat.one_mul] at a
  have b : run0 table 2 ⟨3,true::true::encL bs,rep O (n+3) ++ T⟩ =
      some ⟨4,encL bs,false::false::(rep O (n+3) ++ T)⟩ := by rfl
  have H := join0 (join0 a b) (restore bs 0 (rep O (n+3) ++ T))
  rw [show n+3+2+(2*(strip bs).1+5)=n+10+2*(strip bs).1 by omega] at H
  simpa only [Nat.zero_add] using H

theorem reset (n : Nat) (bs : List Bool) (T : List Bool) :
    run0 table (2*n+14+2*(strip bs).1) ⟨0,false::encL bs,false::(rep O (n+1) ++ false::false::T)⟩ =
      some ⟨0,false::encL (strip bs).2,false::true::false::(rep Z (2*(strip bs).1) ++ (rep O (n+3) ++ T))⟩ := by
  have a := prep n (encL bs) (false::false::T)
  have b : run0 table 2 ⟨2,true::(rep Z n ++ true::true::encL bs),false::false::T⟩ =
      some ⟨3,rep Z (n+3) ++ true::true::encL bs,T⟩ := by rfl
  have H := join0 (join0 a b) (resetD n bs T)
  rw [show n+2+2+(n+10+2*(strip bs).1)=2*n+14+2*(strip bs).1 by omega] at H
  exact H

theorem reset_blank (n : Nat) (bs : List Bool) :
    run0 table (2*n+14+2*(strip bs).1) ⟨0,false::encL bs,false::rep O (n+1)⟩ =
      some ⟨0,false::encL (strip bs).2,false::true::false::(rep Z (2*(strip bs).1) ++ rep O (n+3))⟩ := by
  have a := prep n (encL bs) []
  simp only [List.append_nil] at a
  have b : run0 table 2 ⟨2,true::(rep Z n ++ true::true::encL bs),[]⟩ =
      some ⟨3,rep Z (n+3) ++ true::true::encL bs,[]⟩ := by rfl
  have H := join0 (join0 a b) (resetD n bs [])
  rw [show n+2+2+(n+10+2*(strip bs).1)=2*n+14+2*(strip bs).1 by omega] at H
  simpa only [List.append_nil] using H

theorem encL_zero (m : Nat) (bs : List Bool) :
    encL (List.replicate m false ++ true::bs) = rep Z (2*m) ++ true::true::encL bs := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ,List.cons_append,encL,ih,show 2*(m+1)=2*m+2 by omega]; rfl

theorem encR_head (w : Runs) : ∃ T, encR w = true::T := by
  cases w <;> exact ⟨_,rfl⟩

theorem epoch (s : S) : run0 table (cost s) (cfg s) = some (cfg (next s)) := by
  rcases s with ⟨bs,w⟩
  cases w with
  | last n =>
    have H := reset_blank (2*n+1) bs
    rw [show 2*(2*n+1)+14+2*(strip bs).1=4*n+16+2*(strip bs).1 by omega] at H
    simpa only [cfg,cost,next,encR,show 2*n+1+1=2*n+2 by omega,show 2*n+1+3=2*(n+1)+2 by omega,show 2*(n+1)=2*n+2 by omega,rep,O,Z,List.cons_append,List.nil_append,List.append_assoc] using H
  | more m g w =>
    cases g with
    | zero =>
      obtain ⟨T,hT⟩ := encR_head w
      have H := gap1 (2*m) (encL bs) T
      simpa only [cfg,cost,next,encL_zero,encR,hT,rep,O,Z,List.cons_append,List.nil_append,List.append_assoc] using H
    | succ g =>
      have H := reset (2*m) bs (rep Z (2*g+1) ++ encR w)
      rw [show 2*(2*m)+14+2*(strip bs).1=4*m+14+2*(strip bs).1 by omega] at H
      simpa only [cfg,cost,next,encR,show 2*m+3=2*(m+1)+1 by omega,show 2*(g+1)+1=2*g+1+2 by omega,show 2*(m+1)=2*m+2 by omega,show 2*(g+1)=2*g+2 by omega,rep,O,Z,List.cons_append,List.nil_append,List.append_assoc] using H

def orbit : Nat → S | 0 => ([],.more 0 0 (.last 0)) | n+1 => next (orbit n)
def family (n : Nat) : Z0 := cfg (orbit n)
theorem first : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (s : S) : 0 < cost s := by
  rcases s with ⟨bs,w⟩
  cases w with
  | last n => simp [cost]; omega
  | more m g w => cases g <;> simp [cost] <;> omega
theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := epoch (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => cost (orbit n)) first (fun n => positive (orbit n)) growth m hm
#print axioms never
end BB6.Agent8Raw54.LFRun34
