import Agent2NestedLB
open BB6Coverage BB6Coverage.Agent50Pump BB6.Agent2MultiPump
open BB6.Agent2NestedLE (unary rep_unary unary_add unary_tail env2)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2NestedLA70

def p70 : PartialMachine := BB6.Agent2NestedLB.fromRows [some (some ⟨true,true,1⟩),some (some ⟨false,false,1⟩),some (some ⟨true,true,2⟩),some (some ⟨true,true,5⟩),some (some ⟨false,true,3⟩),some (some ⟨false,false,1⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,0⟩)]
def p116 : PartialMachine := BB6.Agent2NestedLB.fromRows [some (some ⟨true,true,1⟩),some (some ⟨false,false,1⟩),some (some ⟨true,true,2⟩),some (some ⟨true,true,5⟩),some (some ⟨false,true,3⟩),some (some ⟨false,true,0⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨false,true,0⟩),some (some ⟨false,false,0⟩)]
def G (i j : Nat) : HZ := ⟨3,bits "001101" ++ rep (bits "0101") i ++ unary true j,[]⟩
def F (n : Nat) : HZ := G 0 (3*n+1)
def innerStart : MShape := ⟨3,⟨bits "001101",[⟨bits "0101",bits "1",0⟩,⟨bits "1",[],1⟩]⟩,⟨[],[]⟩⟩
def innerEnd : MShape := ⟨3,⟨bits "0011010101",[⟨bits "0101",[],0⟩,⟨bits "1",[],1⟩]⟩,⟨[],[]⟩⟩
def innerOps : List MOp := [.left 0 16 (bits "1111")] ++ List.replicate 12 .step ++ [.right 3 12 (bits "0101")] ++ List.replicate 19 .step
def exitStart : MShape := ⟨3,⟨bits "0011010101",[⟨bits "010101010101",[],0⟩]⟩,⟨[],[]⟩⟩
def exitEnd : MShape := ⟨3,⟨bits "0011011111111111",[⟨bits "111111111111",[],0⟩]⟩,⟨[],[]⟩⟩
def exitOps (c d : Nat) : List MOp := [.left 0 48 (bits "111111111111")] ++ List.replicate 38 .step ++ [.right 1 c (bits "111111111111")] ++ List.replicate d .step ++ [.rewriteL exitEnd.l]
theorem inner70 : runM p70 innerOps innerStart = some innerEnd := by decide
theorem inner116 : runM p116 innerOps innerStart = some innerEnd := by decide
theorem exit70 : runM p70 (exitOps 44 40) exitStart = some exitEnd := by decide
theorem exit116 : runM p116 (exitOps 36 32) exitStart = some exitEnd := by decide

theorem rep_add (w : List Bool) (a b : Nat) : rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,rep,rep,ih,List.append_assoc]
theorem rep_triple (w : List Bool) (n : Nat) : rep (w++(w++w)) n = rep w (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 3*(n+1)=3+3*n by omega,rep_add]
    simp [rep,List.append_assoc]
theorem innerStart_eval (i j : Nat) : innerStart.eval (env2 i j) = G i (j+1) := by
  change (⟨3,bits "001101" ++ (rep (bits "0101") i ++ [true] ++ (rep (unary true 1) j ++ [] ++ [])),[]⟩ : HZ) = G i (j+1)
  simp only [List.append_nil,rep_unary,Nat.one_mul,List.append_assoc,G]
  change (⟨3,bits "001101" ++ (rep (bits "0101") i ++ (unary true 1 ++ unary true j)),[]⟩ : HZ) = _
  rw [unary_add,Nat.add_comm 1 j]
theorem innerEnd_eval (i j : Nat) : innerEnd.eval (env2 i j) = G (i+1) j := by
  change (⟨3,(bits "001101" ++ bits "0101") ++ (rep (bits "0101") i ++ [] ++ (rep (unary true 1) j ++ [] ++ [])),[]⟩ : HZ) = G (i+1) j
  simp [List.append_assoc,rep_unary,rep,G]
theorem exitStart_eval (n : Nat) : exitStart.eval (env2 n 0) = G (3*n+1) 0 := by
  change (⟨3,(bits "001101" ++ bits "0101") ++ (rep (bits "0101"++bits "0101"++bits "0101") n ++ [] ++ []),[]⟩ : HZ) = G (3*n+1) 0
  simp [List.append_assoc,rep_triple,rep,G,unary]
theorem exitEnd_eval (n : Nat) : exitEnd.eval (env2 n 0) = F (4*n+3) := by
  change (⟨3,(bits "001101" ++ unary true 10) ++ (rep (unary true 12) n ++ [] ++ []),[]⟩ : HZ) = G 0 (3*(4*n+3)+1)
  simp only [List.append_nil,List.append_assoc,rep_unary,unary_add,G,rep,List.nil_append]
  rw [show 10+12*n=3*(4*n+3)+1 by omega]

def Reach (p : PartialMachine) (a b : HZ) : Prop := ∃ t, hrun p t a = some b
theorem reach_trans {p : PartialMachine} {a b c : HZ} : Reach p a b → Reach p b c → Reach p a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩; exact ⟨t+u,hjoin h g⟩
theorem inner_reach (p : PartialMachine) (h : runM p innerOps innerStart = some innerEnd) (i j : Nat) : Reach p (G i (j+1)) (G (i+1) j) := by
  obtain ⟨t,_,ht⟩ := runM_sound p innerOps innerStart innerEnd h (env2 i j)
  exact ⟨t,by simpa only [innerStart_eval,innerEnd_eval] using ht⟩
theorem inner_iter (p : PartialMachine) (h : runM p innerOps innerStart = some innerEnd) (i j : Nat) : Reach p (G i j) (G (i+j) 0) := by
  induction j generalizing i with
  | zero => exact ⟨0,by simp [hrun]⟩
  | succ j ih =>
    have H := reach_trans (inner_reach p h i j) (ih (i+1))
    simpa only [show i+1+j=i+(j+1) by omega] using H
theorem epoch (p : PartialMachine) (c d : Nat) (hi : runM p innerOps innerStart = some innerEnd) (he : runM p (exitOps c d) exitStart = some exitEnd) (hp : 0 < lowerM (exitOps c d)) (n : Nat) : ∃ t, 0<t ∧ hrun p t (F n) = some (F (4*n+3)) := by
  obtain ⟨a,ha⟩ := inner_iter p hi 0 (3*n+1)
  simp only [Nat.zero_add] at ha
  obtain ⟨b,hb,Hb⟩ := runM_sound p (exitOps c d) exitStart exitEnd he (env2 n 0)
  rw [exitStart_eval,exitEnd_eval] at Hb
  exact ⟨a+b,by omega,hjoin ha Hb⟩
theorem entry70 : hrun p70 35 ⟨0,[],[]⟩ = some (F 1) := by decide
theorem entry116 : hrun p116 31 ⟨0,[],[]⟩ = some (F 1) := by decide
theorem arbitrary (p : PartialMachine) (c d e : Nat) (hi : runM p innerOps innerStart = some innerEnd) (he : runM p (exitOps c d) exitStart = some exitEnd) (hp : 0 < lowerM (exitOps c d)) (hs : hrun p e ⟨0,[],[]⟩ = some (F 1)) (k : Nat) : ∃ n t, k≤t ∧ hrun p t ⟨0,[],[]⟩ = some (F n) := by
  induction k with
  | zero => exact ⟨1,e,by omega,hs⟩
  | succ k ih =>
    obtain ⟨n,t,ht,Ht⟩ := ih
    obtain ⟨u,hu,Hu⟩ := epoch p c d hi he hp n
    exact ⟨4*n+3,t+u,by omega,hjoin Ht Hu⟩
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
theorem never70 : ∀ m, compatible p70 m → NeverHalts m := never_of_arbitrary p70 (arbitrary p70 44 40 35 inner70 exit70 (by decide) entry70)
theorem never116 : ∀ m, compatible p116 m → NeverHalts m := never_of_arbitrary p116 (arbitrary p116 36 32 31 inner116 exit116 (by decide) entry116)
#print axioms arbitrary
#print axioms never70
#print axioms never116
end BB6.Agent2NestedLA70
