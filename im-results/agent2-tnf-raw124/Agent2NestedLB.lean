import Agent2NestedLE
open BB6Coverage BB6Coverage.Agent50Pump BB6.Agent2MultiPump
open BB6.Agent2NestedLE (unary rep_unary unary_add unary_tail env2)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2NestedLB

def fromRows (xs : List (Option (Option Move))) : PartialMachine := fun s => (xs[2*s.1.val+s.2.toNat]?).getD none

def p1007 : PartialMachine := fromRows [some (some ⟨true,true,1⟩),some (some ⟨false,false,4⟩),some (some ⟨true,true,2⟩),some (some ⟨false,true,0⟩),some (some ⟨false,true,3⟩),none,some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,false,0⟩),some (some ⟨true,false,5⟩),some (some ⟨true,false,4⟩),some (some ⟨true,false,1⟩)]
def p1021 : PartialMachine := fromRows [some (some ⟨true,true,1⟩),some (some ⟨false,false,5⟩),some (some ⟨true,true,2⟩),some (some ⟨false,true,0⟩),some (some ⟨false,true,3⟩),some (some ⟨true,false,4⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨true,false,0⟩),some (some ⟨true,false,1⟩)]

def F (n : Nat) : HZ := ⟨3,bits "0011" ++ rep (bits "01") (n+3),[]⟩
def G (i j : Nat) : HZ := ⟨0,[],rep (bits "1010") i ++ unary true (2*j+1) ++ bits "01010"⟩
def initStart : MShape := ⟨3,⟨bits "0011010101",[⟨bits "01",[],0⟩]⟩,⟨[],[]⟩⟩
def initEnd : MShape := ⟨0,⟨[],[]⟩,⟨bits "1111111",[⟨bits "11",bits "01010",0⟩]⟩⟩
def initOps (c d : Nat) : List MOp := List.replicate 17 .step ++ [.left 0 c (bits "11")] ++ List.replicate d .step

def innerStart : MShape := ⟨0,⟨[],[]⟩,⟨[],[⟨bits "1010",bits "111",0⟩,⟨bits "11",bits "01010",1⟩]⟩⟩
def innerEnd : MShape := ⟨0,⟨[],[]⟩,⟨bits "1010",[⟨bits "1010",bits "1",0⟩,⟨bits "11",bits "01010",1⟩]⟩⟩
def innerOps : List MOp := [.rewriteR ⟨bits "1",[⟨bits "0101",bits "11",0⟩,⟨bits "11",bits "01010",1⟩]⟩,.step,.right 1 4 (bits "1010"),.step,.left 0 4 (bits "1010")] ++ List.replicate 4 .step

def exitStart : MShape := ⟨0,⟨[],[]⟩,⟨bits "101010101010",[⟨bits "1010",bits "101010",0⟩]⟩⟩
def exitEnd : MShape := ⟨3,⟨bits "0011010101010101010101",[⟨bits "0101",[],0⟩]⟩,⟨[],[]⟩⟩
def exitOps : List MOp := [.step,.right 1 4 (bits "1010")] ++ List.replicate 20 .step ++ [.rewriteL exitEnd.l]

theorem init1007 : runM p1007 (initOps 2 7) initStart = some initEnd := by decide
theorem init1021 : runM p1021 (initOps 4 13) initStart = some initEnd := by decide
theorem inner1007 : runM p1007 innerOps innerStart = some innerEnd := by decide
theorem inner1021 : runM p1021 innerOps innerStart = some innerEnd := by decide
theorem exit1007 : runM p1007 exitOps exitStart = some exitEnd := by decide
theorem exit1021 : runM p1021 exitOps exitStart = some exitEnd := by decide

theorem rep_add (w : List Bool) (a b : Nat) : rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega,rep,rep,ih,List.append_assoc]
theorem rep_double (w : List Bool) (n : Nat) : rep (w++w) n = rep w (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,rep_add]
    simp [rep]

theorem initStart_eval (n : Nat) : initStart.eval (env2 n 0) = F n := by
  change (⟨3,(bits "0011" ++ rep (bits "01") 3) ++ (rep (bits "01") n ++ [] ++ []),[]⟩ : HZ) = F n
  simp only [List.append_nil,List.append_assoc,← rep_add,F]
  rw [Nat.add_comm 3 n]
theorem initEnd_eval (n : Nat) : initEnd.eval (env2 n 0) = G 0 (n+3) := by
  change (⟨0,[],unary true 7 ++ (rep (unary true 2) n ++ bits "01010" ++ [])⟩ : HZ) = G 0 (n+3)
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G,rep,List.nil_append]
  rw [show 7+2*n=2*(n+3)+1 by omega]
theorem innerStart_eval (i j : Nat) : innerStart.eval (env2 i j) = G i (j+1) := by
  change (⟨0,[],[] ++ (rep (bits "1010") i ++ unary true 3 ++ (rep (unary true 2) j ++ bits "01010" ++ []))⟩ : HZ) = G i (j+1)
  simp only [List.append_nil,List.nil_append,rep_unary,List.append_assoc,unary_tail,G]
  rw [show 3+2*j=2*(j+1)+1 by omega]
theorem innerEnd_eval (i j : Nat) : innerEnd.eval (env2 i j) = G (i+1) j := by
  change (⟨0,[],bits "1010" ++ (rep (bits "1010") i ++ unary true 1 ++ (rep (unary true 2) j ++ bits "01010" ++ []))⟩ : HZ) = G (i+1) j
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G,rep]
  rw [show 1+2*j=2*j+1 by omega]
theorem exitStart_eval (n : Nat) : exitStart.eval (env2 n 0) = G (n+3) 0 := by
  change (⟨0,[],rep (bits "1010") 3 ++ (rep (bits "1010") n ++ bits "101010" ++ [])⟩ : HZ) = G (n+3) 0
  simp only [List.append_nil,List.append_assoc,← rep_add,G,Nat.mul_zero,Nat.zero_add]
  rw [← List.append_assoc, ← rep_add, Nat.add_comm 3 n]
  rfl
theorem exitEnd_eval (n : Nat) : exitEnd.eval (env2 n 0) = F (2*n+6) := by
  change (⟨3,(bits "0011" ++ rep (bits "01") 9) ++ (rep (bits "01" ++ bits "01") n ++ [] ++ []),[]⟩ : HZ) = F (2*n+6)
  simp only [List.append_nil,rep_double,List.append_assoc,← rep_add,F]
  rw [show 9+2*n=2*n+6+3 by omega]

def Reach (p : PartialMachine) (a b : HZ) : Prop := ∃ t, hrun p t a = some b
theorem reach_trans {p : PartialMachine} {a b c : HZ} : Reach p a b → Reach p b c → Reach p a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,hjoin h g⟩
theorem init_reach (p : PartialMachine) (c d : Nat) (h : runM p (initOps c d) initStart = some initEnd) (n : Nat) : Reach p (F n) (G 0 (n+3)) := by
  obtain ⟨t,_,ht⟩ := runM_sound p (initOps c d) initStart initEnd h (env2 n 0)
  exact ⟨t,by simpa only [initStart_eval,initEnd_eval] using ht⟩
theorem inner_reach (p : PartialMachine) (h : runM p innerOps innerStart = some innerEnd) (i j : Nat) : Reach p (G i (j+1)) (G (i+1) j) := by
  obtain ⟨t,_,ht⟩ := runM_sound p innerOps innerStart innerEnd h (env2 i j)
  exact ⟨t,by simpa only [innerStart_eval,innerEnd_eval] using ht⟩
theorem inner_iter (p : PartialMachine) (h : runM p innerOps innerStart = some innerEnd) (i j : Nat) : Reach p (G i j) (G (i+j) 0) := by
  induction j generalizing i with
  | zero => exact ⟨0,by simp [hrun]⟩
  | succ j ih =>
    have H := reach_trans (inner_reach p h i j) (ih (i+1))
    simpa only [show i+1+j=i+(j+1) by omega] using H
theorem epoch (p : PartialMachine) (c d : Nat) (hi : runM p (initOps c d) initStart = some initEnd) (hm : runM p innerOps innerStart = some innerEnd) (he : runM p exitOps exitStart = some exitEnd) (n : Nat) : ∃ t, 0<t ∧ hrun p t (F n) = some (F (2*n+6)) := by
  obtain ⟨a,ha⟩ := init_reach p c d hi n
  obtain ⟨b,hb⟩ := inner_iter p hm 0 (n+3)
  simp only [Nat.zero_add] at hb
  obtain ⟨t,ht,Ht⟩ := runM_sound p exitOps exitStart exitEnd he (env2 n 0)
  rw [exitStart_eval,exitEnd_eval] at Ht
  have hpos : 0<lowerM exitOps := by decide
  exact ⟨a+b+t,by omega,hjoin (hjoin ha hb) Ht⟩
theorem entry1007 : hrun p1007 30 ⟨0,[],[]⟩ = some (F 0) := by decide
theorem entry1021 : hrun p1021 30 ⟨0,[],[]⟩ = some (F 0) := by decide
theorem arbitrary (p : PartialMachine) (c d : Nat) (hi : runM p (initOps c d) initStart = some initEnd) (hm : runM p innerOps innerStart = some innerEnd) (he : runM p exitOps exitStart = some exitEnd) (hs : hrun p 30 ⟨0,[],[]⟩ = some (F 0)) (k : Nat) : ∃ n t, k≤t ∧ hrun p t ⟨0,[],[]⟩ = some (F n) := by
  induction k with
  | zero => exact ⟨0,30,by decide,hs⟩
  | succ k ih =>
    obtain ⟨n,t,ht,Ht⟩ := ih
    obtain ⟨u,hu,Hu⟩ := epoch p c d hi hm he n
    exact ⟨2*n+6,t+u,by omega,hjoin Ht Hu⟩
open BB6Coverage.Agent50Zipper
theorem never_of_arbitrary (p : PartialMachine) (h : ∀ k, ∃ n t, k≤t ∧ hrun p t ⟨0,[],[]⟩ = some (F n)) : ∀ m, compatible p m → NeverHalts m := by
  intro m hm n
  obtain ⟨a,k,hk,Hk⟩ := h n
  obtain ⟨h',H'⟩ := hrun_sound p k _ _ 0 Hk
  have H := zrun_sound p m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
theorem never1007 : ∀ m, compatible p1007 m → NeverHalts m := never_of_arbitrary p1007 (arbitrary p1007 2 7 init1007 inner1007 exit1007 entry1007)
theorem never1021 : ∀ m, compatible p1021 m → NeverHalts m := never_of_arbitrary p1021 (arbitrary p1021 4 13 init1021 inner1021 exit1021 entry1021)
#print axioms epoch
#print axioms arbitrary
#print axioms never1007
#print axioms never1021
end BB6.Agent2NestedLB
