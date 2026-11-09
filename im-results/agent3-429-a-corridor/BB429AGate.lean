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

/-- The exact A0 right move enters the associated B corridor on the
    original physical tape, preserving every cell ahead of its head. -/
theorem aGate_to_bGate (a : Config) (k : Nat) (ha : aGate k a) :
    ∃ b, rawStep target429 a=some b ∧ bGate k b := by
  rcases ha with ⟨ha0,hpair,hs0,hs1,hs2⟩
  let mv : Move := ⟨true,true,B⟩
  let b := applyMove a mv
  have hrow : target429 (readSlot a) = some mv := by
    simpa [ha0,mv] using
      (show target429 (A,false)=some ⟨true,true,B⟩ by decide)
  have step : rawStep target429 a=some b := by
    simp [rawStep,hrow,b]
  have hhead : b.head=a.head+1 := rfl
  have ht : ∀ x, a.head<x → b.tape x=a.tape x := by
    intro x hx
    exact untouchedRight a mv rfl x hx
  have hslot : readSlot b=(B,false) := by
    change (b.state,b.tape b.head)=(B,false)
    apply Prod.ext
    · rfl
    · have ha1 : a.tape (a.head+1)=false := by
        cases k with
        | zero => simpa using hs0
        | succ k =>
          have hh := hpair 0 (by omega : 0<k+1)
          simpa using hh.1
      change b.tape b.head = false
      rw [hhead, ht (a.head+1) (by omega)]
      exact ha1
  refine ⟨b,step,hslot,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hi0,hi1⟩ := hpair i hi
    constructor
    · have heq : b.head+2*(i:Int)=a.head+1+2*(i:Int) := by omega
      rw [heq,ht _ (by omega)]
      exact hi0
    · have heq : b.head+2*(i:Int)+1=a.head+2+2*(i:Int) := by omega
      rw [heq,ht _ (by omega)]
      exact hi1
  · have heq : b.head+2*(k:Int)=a.head+2*(k:Int)+1 := by omega
    rw [heq,ht _ (by omega)]
    exact hs0
  · have heq : b.head+2*(k:Int)+1=a.head+2*(k:Int)+2 := by omega
    rw [heq,ht _ (by omega)]
    exact hs1
  · have heq : b.head+2*(k:Int)+2=a.head+2*(k:Int)+3 := by omega
    rw [heq,ht _ (by omega)]
    exact hs2

/-- One B/0 and C/1 pair consumes precisely one 01 corridor block. -/
theorem bGate_succ_step (b : Config) (k : Nat) (hg : bGate (k+1) b) :
    ∃ d, run target429 2 b=some d ∧ bGate k d := by
  rcases hg with ⟨hb0,hpair,hs0,hs1,hs2⟩
  let mB : Move := ⟨true,true,C⟩
  let mC : Move := ⟨false,true,B⟩
  let c := applyMove b mB
  let d := applyMove c mC
  have hrowB : target429 (readSlot b)=some mB := by
    simpa [hb0,mB] using
      (show target429 (B,false)=some ⟨true,true,C⟩ by decide)
  have stepB : rawStep target429 b=some c := by
    simp [rawStep,hrowB,c]
  have hc1 : readSlot c=(C,true) := by
    change (c.state,c.tape c.head)=(C,true)
    apply Prod.ext
    · rfl
    · have h1 := (hpair 0 (by omega : 0<k+1)).2
      have hx : c.tape c.head=b.tape (b.head+1) := by
        have ne : b.head+1≠b.head := by omega
        simp [c,applyMove,mB,ne]
      exact hx.trans (by simpa using h1)
  have hrowC : target429 (readSlot c)=some mC := by
    simpa [hc1,mC] using
      (show target429 (C,true)=some ⟨false,true,B⟩ by decide)
  have stepC : rawStep target429 c=some d := by
    simp [rawStep,hrowC,d]
  have hrun : run target429 2 b=some d := by
    change (rawStep target429 b).bind (rawStep target429)=some d
    rw [stepB]
    simpa only [Option.bind_some] using stepC
  have hhead : d.head=b.head+2 := by
    simp [d,c,applyMove,mB,mC]; omega
  have ht : ∀ x, b.head+2≤x → d.tape x=b.tape x := by
    intro x hx
    exact twoRightTail b mB mC rfl rfl x hx
  have hd0 : readSlot d=(B,false) := by
    change (d.state,d.tape d.head)=(B,false)
    apply Prod.ext
    · rfl
    · have hbit : b.tape (b.head+2)=false := by
        cases k with
        | zero => simpa using hs0
        | succ k =>
          have hh := hpair 1 (by omega)
          simpa using hh.1
      rw [ht _ (by omega)]
      simpa [hhead] using hbit
  refine ⟨d,hrun,hd0,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hi0,hi1⟩ := hpair (i+1) (by omega)
    constructor
    · have heq : d.head+2*(i:Int)=b.head+2*((i+1:Nat):Int) := by rw [hhead];omega
      rw [heq,ht _ (by omega)]
      exact hi0
    · have heq : d.head+2*(i:Int)+1=b.head+2*((i+1:Nat):Int)+1 := by rw [hhead];omega
      rw [heq,ht _ (by omega)]
      exact hi1
  · have heq : d.head+2*(k:Int)=b.head+2*((k+1:Nat):Int) := by rw [hhead];omega
    rw [heq,ht _ (by omega)]
    exact hs0
  · have heq : d.head+2*(k:Int)+1=b.head+2*((k+1:Nat):Int)+1 := by rw [hhead];omega
    rw [heq,ht _ (by omega)]
    exact hs1
  · have heq : d.head+2*(k:Int)+2=b.head+2*((k+1:Nat):Int)+2 := by rw [hhead];omega
    rw [heq,ht _ (by omega)]
    exact hs2

theorem run_plus (m : Machine) (a b : Nat) (c : Config) :
    run m (a+b) c = (run m a c).bind (fun d => run m b d) := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    have hs : a+(b+1)=(a+b)+1 := by omega
    rw [hs]
    change (run m (a+b) c).bind (rawStep m) = _
    rw [ih]
    cases hc : run m a c with
    | none => simp [hc]
    | some d => simp [hc,run]

/-- For every natural k, the genuine B corridor deterministically enters
    a B/001 physical gate exactly 2k moves later. -/
theorem bGate_reaches_B001 (k n : Nat) (b : Config)
    (hr : run target429 n blank=some b) (hg : bGate k b) :
    ∃ d, run target429 (n+2*k) blank=some d ∧ bGate 0 d := by
  induction k generalizing n b with
  | zero => exact ⟨b,by simpa using hr,by simpa using hg⟩
  | succ k ih =>
    obtain ⟨c,hstep,hnew⟩ := bGate_succ_step b k hg
    have hc : run target429 (n+2) blank=some c := by
      rw [run_plus,hr]
      simpa using hstep
    obtain ⟨d,hd,hg0⟩ := ih (n+2) c hc hnew
    refine ⟨d,?_,hg0⟩
    have heq : n+2*(k+1)=(n+2)+2*k := by omega
    simpa [heq] using hd

private theorem bGate_zero_iff_fatalB (b : Config) :
    bGate 0 b ↔ BB429FatalB.fatalB b := by
  constructor
  · rintro ⟨hslot,_,h0,h1,h2⟩
    have hs : b.state=BB429FatalB.B := by
      simpa [readSlot, BB429FatalB.B, B] using congrArg Prod.fst hslot
    exact ⟨hs, by simpa using h0, by simpa using h1, by simpa using h2⟩
  · rintro ⟨hs,h0,h1,h2⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · change (b.state,b.tape b.head)=(B,false)
      exact Prod.ext (by simpa [BB429FatalB.B,B] using hs) h0
    · intro i hi; omega
    · simpa using h0
    · simpa using h1
    · simpa using h2

/-- All-time exact blank-origin #429 halt criterion. For some k, a
    genuine A/0 visit must read 0(01)^k001 ahead on its physical tape.
    Every such visit also forces the authentic halt. -/
theorem halts_iff_earlier_A_corridor :
    (∃ n, HaltsAfter target429 n) ↔
    (∃ n k a, run target429 n blank=some a ∧ aGate k a) := by
  rw [BB429FatalB.target429_halts_iff_root_B001]
  constructor
  · rintro ⟨n,b,hb,hfatal⟩
    have hGate : bGate 0 b := (bGate_zero_iff_fatalB b).mpr hfatal
    obtain ⟨j,k,a,hlt,hj,hgate⟩ := bGate_has_A_ancestor n 0 b hb hGate
    exact ⟨j,k,a,hj,hgate⟩
  · rintro ⟨n,k,a,ha,hgate⟩
    obtain ⟨b,hab,hbgate⟩ := aGate_to_bGate a k hgate
    have hb : run target429 (n+1) blank=some b := by
      change (run target429 n blank).bind (rawStep target429)=some b
      rw [ha]
      simpa using hab
    obtain ⟨c,hc,hfatal⟩ := bGate_reaches_B001 k (n+1) b hb hbgate
    exact ⟨n+1+2*k,c,hc,(bGate_zero_iff_fatalB c).mp hfatal⟩

#print axioms bGate_has_A_ancestor
#print axioms bGate_succ_step
#print axioms bGate_reaches_B001
#print axioms halts_iff_earlier_A_corridor

end BB429AGate
