import Agent2MultiPump
open BB6Coverage BB6Coverage.Agent50Pump BB6.Agent2MultiPump BB6Coverage.Agent50Zipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Nested

def fromRows (xs : List (Option (Option Move))) : PartialMachine := fun s => (xs[2*s.1.val+s.2.toNat]?).getD none

def initStart : MShape := ⟨5,⟨bits "111111",[⟨bits "11",bits "",0⟩]⟩,⟨bits "",[]⟩⟩
def initEnd (q : Fin 6) : MShape := ⟨q,⟨bits "1111",[⟨bits "11",bits "01",0⟩]⟩,⟨bits "11",[]⟩⟩
def initOps : List MOp := [.step,.step,.step,.left 0 2 (bits "11"),.step,.step,.step,.step,.step,.step,.step,.step,.step,.right 1 2 (bits "11"),.step,.step,.step,.step,.step]
def innerStart (q : Fin 6) : MShape := ⟨q,⟨bits "1111",[⟨bits "11",bits "01",0⟩,⟨bits "1",bits "",1⟩]⟩,⟨bits "11",[⟨bits "1",bits "",2⟩]⟩⟩
def innerEnd (q : Fin 6) : MShape := ⟨q,⟨bits "11",[⟨bits "11",bits "011",0⟩,⟨bits "1",bits "",1⟩]⟩,⟨bits "111",[⟨bits "1",bits "",2⟩]⟩⟩
def innerOps : List MOp := [.step,.step,.step,.step,.left 1 2 (bits "11"),.step,.rewriteR ⟨bits "1",[⟨bits "11",bits "1011",0⟩,⟨bits "1",bits "",2⟩]⟩,.step,.rewriteR ⟨bits "1",[⟨bits "11",bits "011",0⟩,⟨bits "1",bits "",2⟩]⟩,.step,.step,.step,.right 1 2 (bits "11"),.step,.step,.rewriteL ⟨bits "11",[⟨bits "11",bits "011",0⟩,⟨bits "1",bits "",1⟩]⟩]
def exitStart (q : Fin 6) : MShape := ⟨q,⟨bits "1101",[⟨bits "1",bits "",0⟩]⟩,⟨bits "11",[⟨bits "1",bits "",1⟩]⟩⟩
def exitEnd : MShape := ⟨5,⟨bits "111111",[⟨bits "1",bits "",1⟩,⟨bits "1",bits "",0⟩]⟩,⟨bits "",[]⟩⟩
def exitOps : List MOp := [.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.step,.right 6 1 (bits "1")]
def p341 : PartialMachine := fromRows [some (some ⟨true,true,1⟩),some (some ⟨false,false,1⟩),some (some ⟨true,true,2⟩),some (some ⟨true,false,1⟩),some (some ⟨false,true,3⟩),some (some ⟨false,true,3⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨true,false,0⟩),some (some ⟨true,true,5⟩)]
theorem init341 : runM p341 initOps initStart = some (initEnd 0) := by decide
theorem inner341 : runM p341 innerOps (innerStart 0) = some (innerEnd 0) := by decide
theorem exit341 : runM p341 exitOps (exitStart 0) = some exitEnd := by decide
def p923 : PartialMachine := fromRows [some (some ⟨true,true,1⟩),some (some ⟨true,false,0⟩),some (some ⟨true,true,2⟩),some (some ⟨false,true,3⟩),some (some ⟨false,true,3⟩),some (some ⟨false,false,0⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),none,some (some ⟨true,false,5⟩),some (some ⟨true,false,2⟩),some (some ⟨true,true,5⟩)]
theorem init923 : runM p923 initOps initStart = some (initEnd 2) := by decide
theorem inner923 : runM p923 innerOps (innerStart 2) = some (innerEnd 2) := by decide
theorem exit923 : runM p923 exitOps (exitStart 2) = some exitEnd := by decide

def ones (n : Nat) : List Bool := List.replicate n true

theorem rep_ones (k n : Nat) : rep (ones k) n = ones (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih]
    simp only [ones,List.replicate_append_replicate,Nat.mul_succ]
    congr 1
    omega

theorem ones_add (a b : Nat) : ones a ++ ones b = ones (a+b) := by
  simp [ones,List.replicate_append_replicate]

def F (n : Nat) : HZ := ⟨5,ones (2*n+6),[]⟩
def G (q : Fin 6) (k b c : Nat) : HZ := ⟨q,ones (2*k+2) ++ [false] ++ ones (b+1),ones (c+2)⟩
def env3 (a b c : Nat) : Nat → Nat := fun i => if i = 0 then a else if i = 1 then b else c

theorem initStart_eval (n : Nat) : initStart.eval (env3 n 0 0) = F n := by
  change (⟨5,ones 6 ++ (rep (ones 2) n ++ [] ++ []),[]⟩ : HZ) = F n
  simp [List.append_nil,rep_ones,ones_add,F,Nat.add_comm]

theorem initEnd_eval (q : Fin 6) (n : Nat) : (initEnd q).eval (env3 n 0 0) = G q (n+1) 0 0 := by
  change (⟨q,ones 4 ++ (rep (ones 2) n ++ [false,true] ++ []),ones 2⟩ : HZ) = G q (n+1) 0 0
  rw [List.append_nil,← List.append_assoc,rep_ones,ones_add]
  have h : 4+2*n = 2*(n+1)+2 := by omega
  rw [h]
  simp [G,List.append_assoc]
  rfl

theorem innerStart_eval (q : Fin 6) (k b c : Nat) : (innerStart q).eval (env3 k b c) = G q (k+1) b c := by
  change (⟨q,ones 4 ++ (rep (ones 2) k ++ [false,true] ++ (rep (ones 1) b ++ [] ++ [])),ones 2 ++ (rep (ones 1) c ++ [] ++ [])⟩ : HZ) = G q (k+1) b c
  simp only [List.append_nil,rep_ones,Nat.one_mul,G]
  have hl : ones 4 ++ (ones (2*k) ++ [false,true]) ++ ones b = ones (2*(k+1)+2) ++ [false] ++ ones (b+1) := by
    rw [← List.append_assoc (ones 4) (ones (2*k)) [false,true],ones_add]
    have h : 4+2*k = 2*(k+1)+2 := by omega
    rw [h]
    change (ones (2*(k+1)+2) ++ ([false] ++ ones 1)) ++ ones b = _
    simp only [List.append_assoc,ones_add,show 1+b=b+1 by omega]
  rw [← List.append_assoc (ones 4) (ones (2*k) ++ [false,true]) (ones b),hl,ones_add,Nat.add_comm 2 c]

theorem innerEnd_eval (q : Fin 6) (k b c : Nat) : (innerEnd q).eval (env3 k b c) = G q k (b+1) (c+1) := by
  change (⟨q,ones 2 ++ (rep (ones 2) k ++ [false,true,true] ++ (rep (ones 1) b ++ [] ++ [])),ones 3 ++ (rep (ones 1) c ++ [] ++ [])⟩ : HZ) = G q k (b+1) (c+1)
  simp only [List.append_nil,rep_ones,Nat.one_mul,G]
  have hl : ones 2 ++ (ones (2*k) ++ [false,true,true]) ++ ones b = ones (2*k+2) ++ [false] ++ ones (b+1+1) := by
    rw [← List.append_assoc (ones 2) (ones (2*k)) [false,true,true],ones_add,Nat.add_comm 2 (2*k)]
    change (ones (2*k+2) ++ ([false] ++ ones 2)) ++ ones b = _
    simp only [List.append_assoc,ones_add,show 2+b=b+1+1 by omega]
  rw [← List.append_assoc (ones 2) (ones (2*k) ++ [false,true,true]) (ones b),hl,ones_add,show 3+c=c+1+2 by omega]

theorem exitStart_eval (q : Fin 6) (b c : Nat) : (exitStart q).eval (env3 b c 0) = G q 0 b c := by
  change (⟨q,[true,true,false,true] ++ (rep (ones 1) b ++ [] ++ []),ones 2 ++ (rep (ones 1) c ++ [] ++ [])⟩ : HZ) = G q 0 b c
  simp only [List.append_nil,rep_ones,Nat.one_mul,G]
  change (⟨q, (ones 2 ++ [false]) ++ (ones 1 ++ ones b),ones 2++ones c⟩ : HZ) = _
  rw [ones_add,ones_add,Nat.add_comm 1 b,Nat.add_comm 2 c]

theorem exitEnd_eval (b c : Nat) : exitEnd.eval (env3 b c 0) = (⟨5,ones (b+c+6),[]⟩ : HZ) := by
  change (⟨5,ones 6 ++ (rep (ones 1) c ++ [] ++ (rep (ones 1) b ++ [] ++ [])),[]⟩ : HZ) = _
  simp only [List.append_nil,rep_ones,Nat.one_mul,ones_add]
  rw [show 6+(c+b)=b+c+6 by omega]

def Reach (p : PartialMachine) (a b : HZ) : Prop := ∃ t, hrun p t a = some b

theorem reach_trans {p : PartialMachine} {a b c : HZ} : Reach p a b → Reach p b c → Reach p a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,hjoin h g⟩

theorem init_reach (p : PartialMachine) (q : Fin 6)
    (h : runM p initOps initStart = some (initEnd q)) (n : Nat) : Reach p (F n) (G q (n+1) 0 0) := by
  obtain ⟨t,_,ht⟩ := runM_sound p initOps initStart (initEnd q) h (env3 n 0 0)
  exact ⟨t,by simpa only [initStart_eval,initEnd_eval] using ht⟩

theorem inner_reach (p : PartialMachine) (q : Fin 6)
    (h : runM p innerOps (innerStart q) = some (innerEnd q)) (k b c : Nat) : Reach p (G q (k+1) b c) (G q k (b+1) (c+1)) := by
  obtain ⟨t,_,ht⟩ := runM_sound p innerOps (innerStart q) (innerEnd q) h (env3 k b c)
  exact ⟨t,by simpa only [innerStart_eval,innerEnd_eval] using ht⟩

theorem inner_iter (p : PartialMachine) (q : Fin 6)
    (h : runM p innerOps (innerStart q) = some (innerEnd q)) (k b c : Nat) : Reach p (G q k b c) (G q 0 (b+k) (c+k)) := by
  induction k generalizing b c with
  | zero => exact ⟨0,by simp [hrun]⟩
  | succ k ih =>
    have H := reach_trans (inner_reach p q h k b c) (ih (b+1) (c+1))
    simpa only [show b+1+k=b+(k+1) by omega,show c+1+k=c+(k+1) by omega] using H

theorem epoch (p : PartialMachine) (q : Fin 6)
    (hi : runM p initOps initStart = some (initEnd q))
    (hm : runM p innerOps (innerStart q) = some (innerEnd q))
    (he : runM p exitOps (exitStart q) = some exitEnd) (n : Nat) : ∃ t, 0<t ∧ hrun p t (F n) = some (F (n+1)) := by
  obtain ⟨a,ha⟩ := init_reach p q hi n
  obtain ⟨b,hb⟩ := inner_iter p q hm (n+1) 0 0
  simp only [Nat.zero_add] at hb
  obtain ⟨c,hc,Hc⟩ := runM_sound p exitOps (exitStart q) exitEnd he (env3 (n+1) (n+1) 0)
  rw [exitStart_eval,exitEnd_eval] at Hc
  have hlen : n+1+(n+1)+6=2*(n+1)+6 := by omega
  rw [hlen] at Hc
  have hpos : 0<lowerM exitOps := by decide
  exact ⟨a+b+c,by omega,hjoin (hjoin ha hb) Hc⟩

theorem entry341 : hrun p341 34 ⟨0,[],[]⟩ = some (F 0) := by decide
theorem entry923 : hrun p923 34 ⟨0,[],[]⟩ = some (F 0) := by decide

theorem live (p : PartialMachine) (q : Fin 6)
    (hi : runM p initOps initStart = some (initEnd q))
    (hm : runM p innerOps (innerStart q) = some (innerEnd q))
    (he : runM p exitOps (exitStart q) = some exitEnd)
    (hs : hrun p 34 ⟨0,[],[]⟩ = some (F 0)) (n : Nat) : ∃ t, n≤t ∧ hrun p t ⟨0,[],[]⟩ = some (F n) := by
  induction n with
  | zero => exact ⟨34,by decide,hs⟩
  | succ n ih =>
    obtain ⟨a,ha,Ha⟩ := ih
    obtain ⟨b,hb,Hb⟩ := epoch p q hi hm he n
    exact ⟨a+b,by omega,hjoin Ha Hb⟩

theorem never_of_live (p : PartialMachine) (h : ∀ n : Nat, ∃ t, n≤t ∧ hrun p t ⟨0,[],[]⟩ = some (F n))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨k,hk,Hk⟩ := h n
  obtain ⟨h',H'⟩ := hrun_sound p k _ _ 0 Hk
  have H := zrun_sound p m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem never341 : ∀ m, compatible p341 m → NeverHalts m :=
  never_of_live p341 (live p341 0 init341 inner341 exit341 entry341)
theorem never923 : ∀ m, compatible p923 m → NeverHalts m :=
  never_of_live p923 (live p923 2 init923 inner923 exit923 entry923)

#print axioms epoch
#print axioms live
#print axioms never341
#print axioms never923
end BB6.Agent2Nested
