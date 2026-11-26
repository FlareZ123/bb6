import SweepPumping
import FastFAR

namespace BB6Coverage.Agent48.E0OneLA9011
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
set_option maxHeartbeats 0

abbrev O (n : Nat) := rep [true] n
abbrev Zeros (n : Nat) := rep [false] n

def p (x : Bool) : PartialMachine := FAR.fromCodes [7,13,11,21,14,3,24,16,2,11,23,(if x then 19 else 11)]
def stage (k a b : Nat) : Z0 := ⟨0, if k=0 then [] else false::O k, true::(Zeros a ++ O b)⟩

def Reach (x : Bool) (a b : Z0) : Prop := ∃ t, run0 (p x) t a = some b
def PosReach (x : Bool) (a b : Z0) : Prop := ∃ t, 0 < t ∧ run0 (p x) t a = some b

theorem reach_trans {x : Bool} {a b c : Z0} (h : Reach x a b) (g : Reach x b c) : Reach x a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨s,hs⟩ := g
  exact ⟨t+s,join0 ht hs⟩
theorem reach_pos {x : Bool} {a b c : Z0} (h : Reach x a b) (g : PosReach x b c) : PosReach x a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨s,hp,hs⟩ := g
  exact ⟨t+s,by omega,join0 ht hs⟩
theorem pos_trans {x : Bool} {a b c : Z0} (h : PosReach x a b) (g : PosReach x b c) : PosReach x a c := by
  obtain ⟨t,hp,ht⟩ := h; obtain ⟨s,_,hs⟩ := g
  exact ⟨t+s,by omega,join0 ht hs⟩

theorem zeroShift (x : Bool) (a : Nat) (L R : List Bool) :
    run0 (p x) (a+1) ⟨5,false::L,Zeros a ++ true::R⟩ = some ⟨5,true::(O (a+1) ++ L),R⟩ := by
  induction a generalizing L with
  | zero => cases x <;> rfl
  | succ a ih =>
    have h : run0 (p x) 1 ⟨5,false::L,Zeros (a+1) ++ true::R⟩ = some ⟨5,false::true::L,Zeros a ++ true::R⟩ := by cases x <;> rfl
    have H := join0 h (ih (true::L))
    rw [show 1+(a+1)=a+1+1 by omega] at H
    have eq : O (a+1) ++ true::L = O (a+2) ++ L := by
      calc
        _ = (O (a+1) ++ [true]) ++ L := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = _ := by rw [rep_snoc]; rfl
    rw [eq] at H
    exact H

theorem startF (x : Bool) (k a b : Nat) :
    run0 (p x) (a+3) (stage k (a+1) (b+1)) = some ⟨5,O (a+2) ++ false::true::O k,O b⟩ := by
  have h : run0 (p x) 2 (stage k (a+1) (b+1)) = some ⟨5,[false,false,true]++O k,Zeros a ++ true::O b⟩ := by cases x <;> cases k <;> rfl
  have H := join0 h (zeroShift x a (false::true::O k) (O b))
  rw [show 2+(a+1)=a+3 by omega] at H
  exact H

-- A1,D1,E0 repeatedly pop a one and append a zero beneath the right marker.
theorem drainA (x : Bool) (n : Nat) (L R : List Bool) :
    run0 (p x) (3*n) ⟨0,O n ++ L,true::R⟩ = some ⟨0,L,true::(Zeros n ++ R)⟩ := by
  simpa only [List.cons_append,List.nil_append] using
    sweepL (p x) 0 [] [true] [true] [false] 3 (by intro A B; cases x <;> rfl) n L R

-- C0,D1,E1 pop one from the left ones-run and push one to the right.
theorem drainC (x : Bool) (n : Nat) (L R : List Bool) :
    run0 (p x) (3*n) ⟨2,false::true::(O n ++ L),R⟩ = some ⟨2,false::true::L,O n ++ R⟩ := by
  simpa only [List.cons_append,List.nil_append] using
    sweepL (p x) 2 [false,true] [] [true] [true] 3 (by intro A B; cases x <;> rfl) n L R

theorem inner0 (k a b : Nat) : Reach false (stage k (a+1) (b+4)) (stage (k+1) (a+4) b) := by
  have h := startF false k a (b+3)
  have g : run0 (p false) 2 ⟨5,O (a+2) ++ false::true::O k,O (b+3)⟩ = some ⟨0,O (a+4) ++ false::true::O k,true::O b⟩ := by rfl
  have H := join0 (join0 h g) (drainA false (a+4) (false::true::O k) (O b))
  exact ⟨_,by simpa [stage,rep] using H⟩

theorem inner1 (k a b : Nat) : Reach true (stage k (a+1) (b+5)) (stage (k+1) (a+5) b) := by
  have h := startF true k a (b+4)
  have g : run0 (p true) 3 ⟨5,O (a+2) ++ false::true::O k,O (b+4)⟩ = some ⟨0,O (a+5) ++ false::true::O k,true::O b⟩ := by rfl
  have H := join0 (join0 h g) (drainA true (a+5) (false::true::O k) (O b))
  exact ⟨_,by simpa [stage,rep] using H⟩

theorem innerAll0 (j k a b : Nat) : Reach false (stage k (a+1) (b+4*j)) (stage (k+j) (a+1+3*j) b) := by
  induction j generalizing k a with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ j ih =>
    have h := inner0 k a (b+4*j)
    have g := ih (k+1) (a+3)
    have eq : a+4 = a+3+1 := by omega
    rw [eq] at h
    have H := reach_trans h g
    simpa only [show b+4*j+4=b+4*(j+1) by omega,show k+1+j=k+(j+1) by omega,show a+3+1+3*j=a+1+3*(j+1) by omega] using H

theorem innerAll1 (j k a b : Nat) : Reach true (stage k (a+1) (b+5*j)) (stage (k+j) (a+1+4*j) b) := by
  induction j generalizing k a with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ j ih =>
    have h := inner1 k a (b+5*j)
    have g := ih (k+1) (a+4)
    have eq : a+5 = a+4+1 := by omega
    rw [eq] at h
    have H := reach_trans h g
    simpa only [show b+5*j+5=b+5*(j+1) by omega,show k+1+j=k+(j+1) by omega,show a+4+1+4*j=a+1+4*(j+1) by omega] using H

theorem finishC (x : Bool) (k s : Nat) : PosReach x ⟨2,false::(O (s+1) ++ false::true::O k),[]⟩ (stage 0 (k+2) (s+1)) := by
  have h := drainC x s (false::true::O k) []
  have h' : run0 (p x) (3*s) ⟨2,false::(O (s+1) ++ false::true::O k),[]⟩ = some ⟨2,[false,true,false,true]++O k,O s⟩ := by simpa only [List.append_nil,rep,List.cons_append,List.nil_append] using h
  have g : run0 (p x) 3 ⟨2,[false,true,false,true]++O k,O s⟩ = some ⟨0,O (k+1),true::false::O (s+1)⟩ := by cases x <;> rfl
  have h3 : run0 (p x) (3*(k+1)) ⟨0,O (k+1),true::false::O (s+1)⟩ = some ⟨0,[],true::(Zeros (k+1) ++ false::O (s+1))⟩ := by simpa only [List.append_nil] using drainA x (k+1) [] (false::O (s+1))
  have H := join0 (join0 h' g) h3
  have eq : Zeros (k+1) ++ false::O (s+1) = Zeros (k+2) ++ O (s+1) := by
    calc
      _ = (Zeros (k+1) ++ [false]) ++ O (s+1) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = _ := by rw [rep_snoc]; rfl
  rw [eq] at H
  exact ⟨3*s+3+3*(k+1),by omega,by simpa [stage] using H⟩

theorem end01 (k a : Nat) : PosReach false (stage k (a+1) 1) (stage 0 (k+2) (a+2)) := by
  have h := startF false k a 0
  have g : run0 (p false) 1 ⟨5,O (a+2) ++ false::true::O k,[]⟩ = some ⟨2,false::(O (a+2) ++ false::true::O k),[]⟩ := by rfl
  exact reach_pos ⟨_,join0 h g⟩ (finishC false k (a+1))

theorem end02 (k a : Nat) : PosReach false (stage k (a+1) 2) (stage 0 (k+2) (a+5)) := by
  have h := startF false k a 1
  have g : run0 (p false) 4 ⟨5,O (a+2) ++ false::true::O k,O 1⟩ = some ⟨2,false::(O (a+5) ++ false::true::O k),[]⟩ := by rfl
  exact reach_pos ⟨_,join0 h g⟩ (finishC false k (a+4))

theorem end12 (k a : Nat) : PosReach true (stage k (a+1) 2) (stage 0 (k+2) (a+3)) := by
  have h := startF true k a 1
  have g : run0 (p true) 2 ⟨5,O (a+2) ++ false::true::O k,O 1⟩ = some ⟨2,false::(O (a+3) ++ false::true::O k),[]⟩ := by rfl
  exact reach_pos ⟨_,join0 h g⟩ (finishC true k (a+2))

theorem end13 (k a : Nat) : PosReach true (stage k (a+1) 3) (stage 0 (k+2) (a+6)) := by
  have h := startF true k a 2
  have g : run0 (p true) 5 ⟨5,O (a+2) ++ false::true::O k,O 2⟩ = some ⟨2,false::(O (a+6) ++ false::true::O k),[]⟩ := by rfl
  exact reach_pos ⟨_,join0 h g⟩ (finishC true k (a+5))

theorem outer02 (a j : Nat) : PosReach false (stage 0 (a+1) (2+4*j)) (stage 0 (j+2) (a+3*j+5)) := by
  have h := innerAll0 j 0 a 2
  have g := end02 j (a+3*j)
  rw [Nat.zero_add,show a+1+3*j=a+3*j+1 by omega] at h
  exact reach_pos h g

theorem outer01 (a j : Nat) : PosReach false (stage 0 (a+1) (1+4*j)) (stage 0 (j+2) (a+3*j+2)) := by
  have h := innerAll0 j 0 a 1
  have g := end01 j (a+3*j)
  rw [Nat.zero_add,show a+1+3*j=a+3*j+1 by omega] at h
  exact reach_pos h g

theorem outer12 (a j : Nat) : PosReach true (stage 0 (a+1) (2+5*j)) (stage 0 (j+2) (a+4*j+3)) := by
  have h := innerAll1 j 0 a 2
  have g := end12 j (a+4*j)
  rw [Nat.zero_add,show a+1+4*j=a+4*j+1 by omega] at h
  exact reach_pos h g

theorem outer13 (a j : Nat) : PosReach true (stage 0 (a+1) (3+5*j)) (stage 0 (j+2) (a+4*j+6)) := by
  have h := innerAll1 j 0 a 3
  have g := end13 j (a+4*j)
  rw [Nat.zero_add,show a+1+4*j=a+4*j+1 by omega] at h
  exact reach_pos h g

def family0 (n : Nat) : Z0 := stage 0 (2*n+1) (8*n+2)
def family1 (n : Nat) : Z0 := stage 0 (n+1) (5*n+2)

theorem growth0 (n : Nat) : PosReach false (family0 n) (family0 (n+1)) := by
  have h := outer02 (2*n) (2*n)
  have g := outer01 (2*n+1) (2*n+1)
  have k := outer02 (2*n+2) (2*n+1)
  rw [show 2+4*(2*n)=8*n+2 by omega,show 2*n+3*(2*n)+5=1+4*(2*n+1) by omega] at h
  rw [show 2*n+1+3*(2*n+1)+2=2+4*(2*n+1) by omega] at g
  have H := pos_trans (pos_trans h g) k
  simpa only [family0,show 2*n+1+2=2*(n+1)+1 by omega,show 2*n+2+3*(2*n+1)+5=8*(n+1)+2 by omega] using H

theorem growth1 (n : Nat) : PosReach true (family1 n) (family1 (n+1)) := by
  have h := outer12 n n
  have g := outer13 (n+1) n
  rw [show 2+5*n=5*n+2 by omega,show n+4*n+3=3+5*n by omega] at h
  have H := pos_trans h g
  simpa only [family1,show n+1+4*n+6=5*(n+1)+2 by omega] using H

theorem nonhalt (x : Bool) (m : Machine) (hm : compatible (p x) m) : NeverHalts m := by
  let family := if x then family1 else family0
  have growth : ∀ n, PosReach x (family n) (family (n+1)) := by cases x <;> exact (fun n => by first | exact growth0 n | exact growth1 n)
  let cost := fun n => Classical.choose (growth n)
  have properties (n : Nat) := Classical.choose_spec (growth n)
  apply never_of_growth (p x) family 8 cost
  · cases x <;> rfl
  · exact fun n => (properties n).1
  · exact fun n => (properties n).2
  · exact hm

#print axioms nonhalt
end BB6Coverage.Agent48.E0OneLA9011
