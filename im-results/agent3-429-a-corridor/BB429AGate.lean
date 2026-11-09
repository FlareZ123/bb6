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
