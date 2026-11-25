import Agent2NestedLE
open BB6Coverage BB6Coverage.Agent50Pump BB6.Agent2MultiPump
open BB6.Agent2NestedLE (unary rep_unary unary_add unary_tail env2)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2NestedLA2025

def p2025 : PartialMachine := fun s => ([some (some ⟨true,true,1⟩),some (some ⟨true,false,4⟩),some (some ⟨true,true,2⟩),some (some ⟨false,false,0⟩),some (some ⟨false,true,3⟩),some (some ⟨false,true,2⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,true,2⟩),some (some ⟨true,false,5⟩),none,some (some ⟨true,false,0⟩)] : List (Option (Option Move)))[2*s.1.val+s.2.toNat]?.getD none

def env3 (i m j : Nat) : Nat → Nat := fun k => if k=0 then i else if k=1 then m else j
def F (m n : Nat) : HZ := ⟨4,bits "0100" ++ unary true (5+6*m) ++ unary false (2+2*n) ++ [true],[]⟩
def G (i m j : Nat) : HZ := ⟨3,unary false (6+6*i) ++ bits "10" ++ unary true (5+6*m) ++ unary false (2+2*j) ++ [true],[]⟩
def initStart : MShape := ⟨4,⟨bits "010011111",[⟨bits "111111",bits "00",0⟩,⟨bits "00",bits "1",1⟩]⟩,⟨[],[]⟩⟩
def initEnd : MShape := ⟨3,⟨bits "0000001011111",[⟨bits "111111",bits "00",0⟩,⟨bits "00",bits "1",1⟩]⟩,⟨[],[]⟩⟩
def initOps : List MOp := List.replicate 14 .step

def innerStart : MShape := ⟨3,⟨bits "000000",[⟨bits "000000",bits "1011111",0⟩,⟨bits "111111",bits "0000",1⟩,⟨bits "00",bits "1",2⟩]⟩,⟨[],[]⟩⟩
def innerEnd : MShape := ⟨3,⟨bits "000000000000",[⟨bits "000000",bits "1011111",0⟩,⟨bits "111111",bits "00",1⟩,⟨bits "00",bits "1",2⟩]⟩,⟨[],[]⟩⟩
def innerOps : List MOp := [.left 0 6 (bits "111111")] ++ List.replicate 11 .step ++ [.left 0 6 (bits "111111")] ++ List.replicate 4 .step ++ [.right 4 54 (bits "111111")] ++ List.replicate 46 .step ++ [.right 1 6 (bits "000000")] ++ List.replicate 7 .step ++ [.left 0 6 (bits "111111")] ++ List.replicate 13 .step ++ [.right 1 6 (bits "000000")] ++ List.replicate 11 .step

def exitStart : MShape := ⟨3,⟨bits "000000",[⟨bits "000000",bits "1011111",0⟩,⟨bits "111111",bits "001",1⟩]⟩,⟨[],[]⟩⟩
def exitEnd : MShape := ⟨4,⟨bits "010011111111111",[⟨bits "111111",bits "000000",0⟩,⟨bits "000000",bits "1",1⟩]⟩,⟨[],[]⟩⟩
def exitOps : List MOp := innerOps ++ [.left 0 6 (bits "111111")] ++ List.replicate 17 .step ++ [.left 0 6 (bits "111111")] ++ List.replicate 8 .step ++ [.right 1 6 (bits "000000")] ++ List.replicate 6 .step ++ [.right 1 54 (bits "111111")] ++ List.replicate 102 .step

theorem init_check : runM p2025 initOps initStart = some initEnd := by decide
theorem inner_check : runM p2025 innerOps innerStart = some innerEnd := by decide
theorem exit_check : runM p2025 exitOps exitStart = some exitEnd := by decide

theorem initStart_eval (m n : Nat) : initStart.eval (env2 m n) = F m n := by
  change (⟨4,(bits "0100" ++ unary true 5) ++ (rep (unary true 6) m ++ unary false 2 ++ (rep (unary false 2) n ++ [true] ++ [])),[]⟩ : HZ) = F m n
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,F]
theorem initEnd_eval (m n : Nat) : initEnd.eval (env2 m n) = G 0 m n := by
  change (⟨3,(unary false 6 ++ bits "10" ++ unary true 5) ++ (rep (unary true 6) m ++ unary false 2 ++ (rep (unary false 2) n ++ [true] ++ [])),[]⟩ : HZ) = G 0 m n
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G,Nat.mul_zero,Nat.add_zero]
theorem innerStart_eval (i m j : Nat) : innerStart.eval (env3 i m j) = G i m (j+1) := by
  change (⟨3,unary false 6 ++ (rep (unary false 6) i ++ (bits "10" ++ unary true 5) ++ (rep (unary true 6) m ++ unary false 4 ++ (rep (unary false 2) j ++ [true] ++ []))),[]⟩ : HZ) = G i m (j+1)
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G]
  rw [show 4+2*j=2+2*(j+1) by omega]
theorem innerEnd_eval (i m j : Nat) : innerEnd.eval (env3 i m j) = G (i+1) m j := by
  change (⟨3,unary false 12 ++ (rep (unary false 6) i ++ (bits "10" ++ unary true 5) ++ (rep (unary true 6) m ++ unary false 2 ++ (rep (unary false 2) j ++ [true] ++ []))),[]⟩ : HZ) = G (i+1) m j
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G]
  rw [show 12+6*i=6+6*(i+1) by omega]
theorem exitStart_eval (i m : Nat) : exitStart.eval (env2 i m) = G i m 0 := by
  change (⟨3,unary false 6 ++ (rep (unary false 6) i ++ (bits "10" ++ unary true 5) ++ (rep (unary true 6) m ++ (unary false 2 ++ [true]) ++ [])),[]⟩ : HZ) = G i m 0
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,G,Nat.mul_zero,Nat.add_zero]
theorem exitEnd_eval (i m : Nat) : exitEnd.eval (env2 i m) = F (i+1) (3*m+2) := by
  change (⟨4,(bits "0100" ++ unary true 11) ++ (rep (unary true 6) i ++ unary false 6 ++ (rep (unary false 6) m ++ [true] ++ [])),[]⟩ : HZ) = F (i+1) (3*m+2)
  simp only [List.append_nil,rep_unary,List.append_assoc,unary_tail,F]
  rw [show 11+6*i=5+6*(i+1) by omega,show 6+6*m=2+2*(3*m+2) by omega]

def Reach (a b : HZ) : Prop := ∃ t, hrun p2025 t a = some b
theorem reach_trans {a b c : HZ} : Reach a b → Reach b c → Reach a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,hjoin h g⟩
theorem init_reach (m n : Nat) : Reach (F m n) (G 0 m n) := by
  obtain ⟨t,_,ht⟩ := runM_sound p2025 initOps initStart initEnd init_check (env2 m n)
  exact ⟨t,by simpa only [initStart_eval,initEnd_eval] using ht⟩
theorem inner_reach (i m j : Nat) : Reach (G i m (j+1)) (G (i+1) m j) := by
  obtain ⟨t,_,ht⟩ := runM_sound p2025 innerOps innerStart innerEnd inner_check (env3 i m j)
  exact ⟨t,by simpa only [innerStart_eval,innerEnd_eval] using ht⟩
theorem inner_iter (i m j : Nat) : Reach (G i m j) (G (i+j) m 0) := by
  induction j generalizing i with
  | zero => exact ⟨0,by simp [hrun]⟩
  | succ j ih =>
    have H := reach_trans (inner_reach i m j) (ih (i+1))
    simpa only [show i+1+j=i+(j+1) by omega] using H
theorem epoch (m n : Nat) : ∃ t, 0<t ∧ hrun p2025 t (F m n) = some (F (n+1) (3*m+2)) := by
  obtain ⟨a,ha⟩ := init_reach m n
  obtain ⟨b,hb⟩ := inner_iter 0 m n
  simp only [Nat.zero_add] at hb
  obtain ⟨c,hc,Hc⟩ := runM_sound p2025 exitOps exitStart exitEnd exit_check (env2 n m)
  rw [exitStart_eval,exitEnd_eval] at Hc
  have hpos : 0<lowerM exitOps := by decide
  exact ⟨a+b+c,by omega,hjoin (hjoin ha hb) Hc⟩
theorem entry : hrun p2025 163 ⟨0,[],[]⟩ = some (F 0 2) := by decide
theorem arbitrary (k : Nat) : ∃ m n t, k≤t ∧ hrun p2025 t ⟨0,[],[]⟩ = some (F m n) := by
  induction k with
  | zero => exact ⟨0,2,163,by decide,entry⟩
  | succ k ih =>
    obtain ⟨m,n,t,ht,Ht⟩ := ih
    obtain ⟨u,hu,Hu⟩ := epoch m n
    exact ⟨n+1,3*m+2,t+u,by omega,hjoin Ht Hu⟩
open BB6Coverage.Agent50Zipper
theorem never : ∀ m, compatible p2025 m → NeverHalts m := by
  intro m hm n
  obtain ⟨a,b,k,hk,Hk⟩ := arbitrary n
  obtain ⟨h',H'⟩ := hrun_sound p2025 k _ _ 0 Hk
  have H := zrun_sound p2025 m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms epoch
#print axioms arbitrary
#print axioms never
end BB6.Agent2NestedLA2025
