import Agent2MultiPump
open BB6Coverage BB6Coverage.Agent50Pump BB6.Agent2MultiPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2NestedLE

def p5261 : PartialMachine := fun s => ([some (some ⟨true,true,1⟩),some (some ⟨false,false,4⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨false,true,2⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,5⟩),some (some ⟨true,true,2⟩),some (some ⟨true,false,4⟩)] : List (Option (Option Move)))[2*s.1.val+s.2.toNat]?.getD none

def unary (b : Bool) (n : Nat) : List Bool := List.replicate n b
theorem rep_unary (b : Bool) (k n : Nat) : rep (unary b k) n = unary b (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih]
    simp only [unary,List.replicate_append_replicate,Nat.mul_succ]
    congr 1
    omega
theorem unary_add (b : Bool) (a c : Nat) : unary b a ++ unary b c = unary b (a+c) := by
  simp [unary,List.replicate_append_replicate]
theorem unary_tail (b : Bool) (a c : Nat) (xs : List Bool) : unary b a ++ (unary b c ++ xs) = unary b (a+c) ++ xs := by
  rw [← List.append_assoc,unary_add]
def env2 (i j : Nat) : Nat → Nat := fun k => if k=0 then i else j

def F (n : Nat) : HZ := ⟨0,bits "01100" ++ unary true (2*n+2),[]⟩
def G (i j : Nat) : HZ := ⟨0,bits "01100" ++ unary true (7+8*i) ++ unary false (2+2*j) ++ [true],[]⟩
def initStart : MShape := ⟨0,⟨bits "0110011",[⟨bits "11",[],0⟩]⟩,⟨[],[]⟩⟩
def initEnd : MShape := ⟨0,⟨bits "01100111111100",[⟨bits "00",bits "1",0⟩]⟩,⟨[],[]⟩⟩
def initOps : List MOp := List.replicate 32 .step ++ [.left 0 2 (bits "11")] ++ List.replicate 4 .step ++ [.right 1 2 (bits "00")] ++ List.replicate 69 .step
def innerStart : MShape := ⟨0,⟨bits "011001111111",[⟨bits "11111111",bits "0000",0⟩,⟨bits "00",bits "1",1⟩]⟩,⟨[],[]⟩⟩
def innerEnd : MShape := ⟨0,⟨bits "01100111111111111111",[⟨bits "11111111",bits "00",0⟩,⟨bits "00",bits "1",1⟩]⟩,⟨[],[]⟩⟩
def innerOps : List MOp := List.replicate 32 .step ++ [.left 0 8 (bits "11111111")] ++ List.replicate 6 .step ++ [.right 4 72 (bits "11111111")] ++ List.replicate 152 .step
def exitStart : MShape := ⟨0,⟨bits "011001111111",[⟨bits "11111111",bits "001",0⟩]⟩,⟨[],[]⟩⟩
def exitEnd : MShape := ⟨0,⟨bits "011001111111111111111",[⟨bits "11111111",[],0⟩]⟩,⟨[],[]⟩⟩
def exitOps : List MOp := innerOps ++ [.rewriteL exitEnd.l]

theorem init_check : runM p5261 initOps initStart = some initEnd := by decide
theorem inner_check : runM p5261 innerOps innerStart = some innerEnd := by decide
theorem exit_check : runM p5261 exitOps exitStart = some exitEnd := by decide

theorem initStart_eval (n : Nat) : initStart.eval (env2 n 0) = F n := by
  change (⟨0,(bits "01100" ++ unary true 2) ++ (rep (unary true 2) n ++ [] ++ []),[]⟩ : HZ) = F n
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_add,F]
  rw [show 2+2*n=2*n+2 by omega]
theorem initEnd_eval (n : Nat) : initEnd.eval (env2 n 0) = G 0 n := by
  change (⟨0,(bits "01100" ++ unary true 7 ++ unary false 2) ++ (rep (unary false 2) n ++ [true] ++ []),[]⟩ : HZ) = G 0 n
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G,Nat.mul_zero,Nat.add_zero]
theorem innerStart_eval (i j : Nat) : innerStart.eval (env2 i j) = G i (j+1) := by
  change (⟨0,(bits "01100" ++ unary true 7) ++ (rep (unary true 8) i ++ unary false 4 ++ (rep (unary false 2) j ++ [true] ++ [])),[]⟩ : HZ) = G i (j+1)
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G]
  rw [show 4+2*j=2+2*(j+1) by omega]
theorem innerEnd_eval (i j : Nat) : innerEnd.eval (env2 i j) = G (i+1) j := by
  change (⟨0,(bits "01100" ++ unary true 15) ++ (rep (unary true 8) i ++ unary false 2 ++ (rep (unary false 2) j ++ [true] ++ [])),[]⟩ : HZ) = G (i+1) j
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G]
  rw [show 15+8*i=7+8*(i+1) by omega]
theorem exitStart_eval (i : Nat) : exitStart.eval (env2 i 0) = G i 0 := by
  change (⟨0,(bits "01100" ++ unary true 7) ++ (rep (unary true 8) i ++ ([false,false,true] : List Bool) ++ []),[]⟩ : HZ) = G i 0
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G,Nat.mul_zero,Nat.add_zero]
  rfl
theorem exitEnd_eval (i : Nat) : exitEnd.eval (env2 i 0) = F (4*i+7) := by
  change (⟨0,(bits "01100" ++ unary true 16) ++ (rep (unary true 8) i ++ [] ++ []),[]⟩ : HZ) = F (4*i+7)
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_add,F]
  rw [show 16+8*i=2*(4*i+7)+2 by omega]

def Reach (a b : HZ) : Prop := ∃ t, hrun p5261 t a = some b
theorem reach_trans {a b c : HZ} : Reach a b → Reach b c → Reach a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,hjoin h g⟩
theorem init_reach (n : Nat) : Reach (F n) (G 0 n) := by
  obtain ⟨t,_,ht⟩ := runM_sound p5261 initOps initStart initEnd init_check (env2 n 0)
  exact ⟨t,by simpa only [initStart_eval,initEnd_eval] using ht⟩
theorem inner_reach (i j : Nat) : Reach (G i (j+1)) (G (i+1) j) := by
  obtain ⟨t,_,ht⟩ := runM_sound p5261 innerOps innerStart innerEnd inner_check (env2 i j)
  exact ⟨t,by simpa only [innerStart_eval,innerEnd_eval] using ht⟩
theorem inner_iter (i j : Nat) : Reach (G i j) (G (i+j) 0) := by
  induction j generalizing i with
  | zero => exact ⟨0,by simp [hrun]⟩
  | succ j ih =>
    have H := reach_trans (inner_reach i j) (ih (i+1))
    simpa only [show i+1+j=i+(j+1) by omega] using H
theorem epoch (n : Nat) : ∃ t, 0<t ∧ hrun p5261 t (F n) = some (F (4*n+7)) := by
  obtain ⟨a,ha⟩ := init_reach n
  obtain ⟨b,hb⟩ := inner_iter 0 n
  simp only [Nat.zero_add] at hb
  obtain ⟨c,hc,Hc⟩ := runM_sound p5261 exitOps exitStart exitEnd exit_check (env2 n 0)
  rw [exitStart_eval,exitEnd_eval] at Hc
  have hpos : 0<lowerM exitOps := by decide
  exact ⟨a+b+c,by omega,hjoin (hjoin ha hb) Hc⟩
theorem entry : hrun p5261 77 ⟨0,[],[]⟩ = some (F 2) := by decide
theorem arbitrary (k : Nat) : ∃ n t, k≤t ∧ hrun p5261 t ⟨0,[],[]⟩ = some (F n) := by
  induction k with
  | zero => exact ⟨2,77,by decide,entry⟩
  | succ k ih =>
    obtain ⟨n,t,ht,Ht⟩ := ih
    obtain ⟨u,hu,Hu⟩ := epoch n
    exact ⟨4*n+7,t+u,by omega,hjoin Ht Hu⟩

open BB6Coverage.Agent50Zipper
theorem never : ∀ m, compatible p5261 m → NeverHalts m := by
  intro m hm n
  obtain ⟨a,k,hk,Hk⟩ := arbitrary n
  obtain ⟨h',H'⟩ := hrun_sound p5261 k _ _ 0 Hk
  have H := zrun_sound p5261 m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms epoch
#print axioms arbitrary
#print axioms never
end BB6.Agent2NestedLE
