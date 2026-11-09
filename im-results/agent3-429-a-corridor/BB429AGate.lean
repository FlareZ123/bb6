import BB429FatalB
import Lean.Elab.Tactic.Omega

namespace BB429AGate
open BB6Coverage BB429PhysicalFrontier

private def A : Fin 6 := ⟨0, by decide⟩
private def B : Fin 6 := ⟨1, by decide⟩
private def C : Fin 6 := ⟨2, by decide⟩

/-- State B scanning the corridor (01)^k001, represented on the original
    bi-infinite tape. The zero at every pair's start is a B/0 input. -/
def bGate (k : Nat) (b : Config) : Prop :=
  readSlot b=(B,false) ∧
  (∀ i : Nat, i<k → b.tape (b.head+2*(i:Int))=false ∧
    b.tape (b.head+2*(i:Int)+1)=true) ∧
  b.tape (b.head+2*(k:Int))=false ∧
  b.tape (b.head+2*(k:Int)+1)=false ∧
  b.tape (b.head+2*(k:Int)+2)=true

/-- A single state A scanning 0(01)^k001 (at head through head+2k+3).
    The corridor has arbitrary unbounded natural length k. -/
def aGate (k : Nat) (a : Config) : Prop :=
  readSlot a=(A,false) ∧
  (∀ i : Nat, i<k → a.tape (a.head+1+2*(i:Int))=false ∧
    a.tape (a.head+2+2*(i:Int))=true) ∧
  a.tape (a.head+2*(k:Int)+1)=false ∧
  a.tape (a.head+2*(k:Int)+2)=false ∧
  a.tape (a.head+2*(k:Int)+3)=true

private theorem target429_B_parents (s : Slot) (mv : Move)
    (h : target429 s=some mv) (hn : mv.next=B) :
    (s=(A,false) ∨ s=(C,true)) ∧ mv.right=true := by
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hh := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    simp [BB429PhysicalFrontier.target429, BB429PhysicalFrontier.prefix11,
      BB429PhysicalFrontier.prefix10, BB429PhysicalFrontier.prefix9,
      BB429PhysicalFrontier.prefix8, BB429PhysicalFrontier.prefix7,
      BB429PhysicalFrontier.prefix6, BB429PhysicalFrontier.prefix5,
      BB429PhysicalFrontier.prefix4, BB429PhysicalFrontier.prefix3,
      BB429PhysicalFrontier.prefix2, BB429PhysicalFrontier.prefix1,
      BB429PhysicalFrontier.prefix0, refine, emptyTable] at h <;>
    cases h <;> simp_all [A,B,C]

private theorem target429_C_parent (s : Slot) (mv : Move)
    (h : target429 s=some mv) (hn : mv.next=C) :
    s=(B,false) ∧ mv.right=true := by
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hh := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    simp [BB429PhysicalFrontier.target429, BB429PhysicalFrontier.prefix11,
      BB429PhysicalFrontier.prefix10, BB429PhysicalFrontier.prefix9,
      BB429PhysicalFrontier.prefix8, BB429PhysicalFrontier.prefix7,
      BB429PhysicalFrontier.prefix6, BB429PhysicalFrontier.prefix5,
      BB429PhysicalFrontier.prefix4, BB429PhysicalFrontier.prefix3,
      BB429PhysicalFrontier.prefix2, BB429PhysicalFrontier.prefix1,
      BB429PhysicalFrontier.prefix0, refine, emptyTable] at h <;>
    cases h <;> simp_all [A,B,C]

private theorem B_prev (n : Nat) (b : Config)
    (hr : run target429 (n+1) blank=some b) (hb : b.state=B) :
    ∃ a mv, run target429 n blank=some a ∧
      (readSlot a=(A,false) ∨ readSlot a=(C,true)) ∧
      mv.right=true ∧ b=applyMove a mv := by
  cases hp : run target429 n blank with
  | none => simp [run,hp] at hr
  | some a =>
    have step : rawStep target429 a=some b := by simpa [run,hp] using hr
    cases ht : target429 (readSlot a) with
    | none => simp [rawStep,ht] at step
    | some mv =>
      have heq : b=applyMove a mv := by simpa [rawStep,ht] using step.symm
      have hn : mv.next=B := by rw [heq] at hb; exact hb
      obtain ⟨hs,hd⟩ := target429_B_parents (readSlot a) mv ht hn
      exact ⟨a,mv,by simpa using hp,hs,hd,heq⟩

private theorem C_prev (n : Nat) (c : Config)
    (hr : run target429 (n+1) blank=some c) (hc : c.state=C) :
    ∃ a mv, run target429 n blank=some a ∧
      readSlot a=(B,false) ∧ mv.right=true ∧ c=applyMove a mv := by
  cases hp : run target429 n blank with
  | none => simp [run,hp] at hr
  | some a =>
    have step : rawStep target429 a=some c := by simpa [run,hp] using hr
    cases ht : target429 (readSlot a) with
    | none => simp [rawStep,ht] at step
    | some mv =>
      have heq : c=applyMove a mv := by simpa [rawStep,ht] using step.symm
      have hn : mv.next=C := by rw [heq] at hc; exact hc
      obtain ⟨hs,hd⟩ := target429_C_parent (readSlot a) mv ht hn
      exact ⟨a,mv,by simpa using hp,hs,hd,heq⟩

/-- A right move cannot rewrite any cell strictly ahead of its old head. -/
theorem untouchedRight (a : Config) (mv : Move) (hr : mv.right=true)
    (x : Int) (hx : a.head<x) : (applyMove a mv).tape x=a.tape x := by
  have ne : x≠a.head := by omega
  simp [applyMove,ne]

theorem A_parent_to_aGate (a b : Config) (mv : Move) (k : Nat)
    (heq : b=applyMove a mv) (hdir:mv.right=true)
    (ha : readSlot a=(A,false)) (hb : bGate k b) : aGate k a := by
  rcases hb with ⟨hb0,hpair,hs0,hs1,hs2⟩
  have hhead : b.head=a.head+1 := by rw [heq];simp [applyMove,hdir]
  have hrgt : ∀ x, a.head<x → b.tape x=a.tape x := by
    intro x hx; rw [heq]; exact untouchedRight a mv hdir x hx
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := hpair i hi
    constructor
    · have hx : b.head+2*(i:Int)=a.head+1+2*(i:Int) := by omega
      rw [←hx, ←hrgt (b.head+2*(i:Int)) (by omega)]
      exact h.1
    · have hx : b.head+2*(i:Int)+1=a.head+2+2*(i:Int) := by omega
      rw [←hx, ←hrgt (b.head+2*(i:Int)+1) (by omega)]
      exact h.2
  · have hx : b.head+2*(k:Int)=a.head+2*(k:Int)+1 := by omega
    rw [←hx, ←hrgt (b.head+2*(k:Int)) (by omega)]
    exact hs0
  · have hx : b.head+2*(k:Int)+1=a.head+2*(k:Int)+2 := by omega
    rw [←hx, ←hrgt (b.head+2*(k:Int)+1) (by omega)]
    exact hs1
  · have hx : b.head+2*(k:Int)+2=a.head+2*(k:Int)+3 := by omega
    rw [←hx, ←hrgt (b.head+2*(k:Int)+2) (by omega)]
    exact hs2

/-- Two consecutive right moves preserve every cell at or beyond head+2. -/
theorem twoRightTail (e : Config) (mB mC : Move)
    (hrB : mB.right=true) (hrC : mC.right=true)
    (x : Int) (hx : e.head+2≤x) :
    (applyMove (applyMove e mB) mC).tape x = e.tape x := by
  have ne0 : x ≠ e.head := by omega
  have ne1 : x ≠ e.head + 1 := by omega
  have he : (applyMove e mB).head = e.head+1 := by simp [applyMove,hrB]
  simp [applyMove,hrB,hrC,he,ne0,ne1]

/-- The exact backward C1/B0 pair adds one alternating corridor block. -/
theorem C_parent_to_bGate_succ (e c b : Config) (mB mC : Move) (k : Nat)
    (heqc : c=applyMove e mB) (heqb : b=applyMove c mC)
    (hrB : mB.right=true) (hrC : mC.right=true)
    (he : readSlot e=(B,false)) (hc : readSlot c=(C,true))
    (hb : bGate k b) : bGate (k+1) e := by
  rcases hb with ⟨hb0,hpair,hs0,hs1,hs2⟩
  have hcpos : c.head=e.head+1 := by rw [heqc];simp [applyMove,hrB]
  have hbpos : b.head=e.head+2 := by
    rw [heqb]
    simp only [applyMove,hrC,ite_true]
    omega
  have he1 : e.tape (e.head+1)=true := by
    have hc1 : c.tape c.head=true := by
      have hh := congrArg Prod.snd hc
      simpa [readSlot] using hh
    have htt : c.tape c.head=e.tape (e.head+1) := by
      rw [heqc]
      have ne : e.head+1≠e.head := by omega
      simp [applyMove,hrB,ne]
    exact htt.symm.trans hc1
  have ht : ∀ x, e.head+2≤x → b.tape x=e.tape x := by
    intro x hx
    rw [heqb,heqc]
    exact twoRightTail e mB mC hrB hrC x hx
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero =>
        constructor
        · have h0 := congrArg Prod.snd he
          simpa [readSlot] using h0
        · simpa using he1
    | succ j =>
        have hj : j<k := by omega
        obtain ⟨hh0,hh1⟩ := hpair j hj
        have hzero : b.head+2*(j:Int)=e.head+2*((j+1:Nat):Int) := by
          rw [hbpos]; omega
        have hone : b.head+2*(j:Int)+1=e.head+2*((j+1:Nat):Int)+1 := by
          rw [hbpos];omega
        constructor
        · rw [←hzero, ←ht (b.head+2*(j:Int)) (by omega)]
          exact hh0
        · rw [←hone, ←ht (b.head+2*(j:Int)+1) (by omega)]
          exact hh1
  · have hx : b.head+2*(k:Int)=e.head+2*((k+1:Nat):Int) := by rw [hbpos];omega
    rw [←hx, ←ht (b.head+2*(k:Int)) (by omega)]
    exact hs0
  · have hx : b.head+2*(k:Int)+1=e.head+2*((k+1:Nat):Int)+1 := by rw [hbpos];omega
    rw [←hx, ←ht (b.head+2*(k:Int)+1) (by omega)]
    exact hs1
  · have hx : b.head+2*(k:Int)+2=e.head+2*((k+1:Nat):Int)+2 := by rw [hbpos];omega
    rw [←hx, ←ht (b.head+2*(k:Int)+2) (by omega)]
    exact hs2

/-- Strong induction on genuine blank-run time collapses every rightward
    B0/C1 chain to a strictly earlier A0 origin with a full exact corridor.
    This is independent of any bound on the alternating block length. -/
theorem bGate_has_A_ancestor (n : Nat) :
    ∀ k b, run target429 n blank = some b → bGate k b →
      ∃ j k' a, j<n ∧ run target429 j blank=some a ∧ aGate k' a := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k b hr hgate
    have hbst : b.state=B := by
      have h := congrArg Prod.fst hgate.1
      simpa [readSlot] using h
    cases n with
    | zero =>
      have heq : b=blank := by simpa [run] using hr.symm
      subst b
      simp [blank,B] at hbst
    | succ t =>
      obtain ⟨a,mv,ha,hslot,hdir,hb⟩ := B_prev t b hr hbst
      rcases hslot with hA|hC
      · exact ⟨t,k,a,Nat.lt_succ_self t,ha,
          A_parent_to_aGate a b mv k hb hdir hA hgate⟩
      · cases t with
        | zero =>
          have heq : a=blank := by simpa [run] using ha.symm
          subst a
          simp [readSlot,blank,C] at hC
        | succ l =>
          have hcstate : a.state=C := by
            have h := congrArg Prod.fst hC
            simpa [readSlot] using h
          obtain ⟨e,mB,he,hBe,hdirB,hce⟩ := C_prev l a ha hcstate
          have hG : bGate (k+1) e :=
            C_parent_to_bGate_succ e a b mB mv k hce hb hdirB hdir hBe hC hgate
          obtain ⟨j,k',x,hj,hjrun,hx⟩ := ih l (by omega) (k+1) e he hG
          exact ⟨j,k',x,by omega,hjrun,hx⟩
