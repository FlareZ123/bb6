import LaneClockSource
import CountedOrdinaryLow
import WordBlockSource

namespace BB6.Agent12LanePathSource

open BB6.Agent12WordBlock
open BB6.Agent12BitEventWord
open BB6.Agent12LaneWord
open BB6.Agent12LaneClock
open BB6.Agent12LaneGenerator
open BB6.Agent12WeightedWord
open BB6.Agent12CountedOrdinaryLow
open BB6.Agent47ThinCounted
open BB6.Agent12Clock

/-- The low-output guard needed by the exact inverse section theorem.
    Unlike outputOK, it permits the genuine source cases y=5,6,7. -/
def outputOK5 (s : BitState) : Prop :=
  2+s.o≤s.b ∧ s.b+8≤s.m+s.o

structure LaneSpec5 (q N : Nat) (u : Nat → BitState) : Prop where
  next : ∀ j<N, u j=tick (q.testBit j) (u (j+1))
  input : ∀ j, 0<j → j≤N → (j=N ∨ q.testBit j=true) →
    inputOK (u j) (q.testBit (j-1))
  output : ∀ j<N, q.testBit j=true → outputOK5 (u j)
  closed : q.testBit 0=true

structure EdgeData5 (r : Nat) (s : State) where
  a k x y : Nat
  dec : decode s=(a,k)
  decNext : decode (step r s)=(x,y)
  ha : 2≤a
  hk : 1≤k
  hy : 5≤y
  branch : if r=1 then 2*k≤a else a<2*k
  mass : x+2*y=a+2*k+3*r+1
  area : (2:Int)^r*((a:Int)+2+(a%2:Nat))=2*(x:Int)+2*(y:Int)+2*(a%2:Nat)
  a_eq : (a:Int)=s.a
  m_eq : a+2*k=s.m
  x_eq : (x:Int)=(step r s).a
  gap_eq : gap s=2*k
  parity_eq : parity s=(a%2:Nat)

/-- The exact input and low-output guards determine the unique ordinary
    section edge, with no global mass lower bound. -/
theorem edgeData5_of_guards (r : Nat) (s : State) (hr : 1≤r)
    (hi : inputOK (lift s) (r==1))
    (ho : outputOK5 (lift (step r s))) : EdgeData5 r s := by
  obtain ⟨ha0,hg0,hp0,hb0⟩ := hi
  obtain ⟨hx0,hg1⟩ := ho
  simp only [lift] at ha0 hg0 hp0 hb0 hx0 hg1
  have ha : 2≤s.a := by omega
  have hkGap : 2≤gap s := by unfold gap; omega
  have hp : consistent s := by unfold consistent parity at *; omega
  have hv : valid s := ⟨by omega,by omega,hp⟩
  have hx : 0≤(step r s).a := by omega
  have hg : 10≤gap (step r s) := by unfold gap; omega
  have hb : if r=1 then (s.m:Int)≤2*s.a else 2*s.a<(s.m:Int) := by
    by_cases h : r=1 <;> simp [h] at hb0 ⊢ <;> omega
  have hv' : valid (step r s) :=
    ⟨hx,by omega,step_consistent r s hr⟩
  obtain ⟨_,ha0',hk0,hm0⟩ := decode_coords s hv
  obtain ⟨_,hx0',hy0,hm1⟩ := decode_coords (step r s) hv'
  let a := (decode s).1
  let k := (decode s).2
  let x := (decode (step r s)).1
  let y := (decode (step r s)).2
  change (a:Int)=s.a at ha0'
  change 2*(k:Int)=gap s at hk0
  change a+2*k=s.m at hm0
  change (x:Int)=(step r s).a at hx0'
  change 2*(y:Int)=gap (step r s) at hy0
  change x+2*y=(step r s).m at hm1
  have hpar : parity s=(a%2:Nat) := by
    unfold consistent at hp
    omega
  have hM : x+2*y=a+2*k+3*r+1 := by
    change x+2*y=s.m+3*r+1 at hm1
    omega
  have hA : (2:Int)^r*((a:Int)+2+(a%2:Nat))=
      2*(x:Int)+2*(y:Int)+2*(a%2:Nat) := by
    have hrel : (2:Int)^r*(s.a+2+parity s)=
        (step r s).a+(step r s).m+2*parity s := by
      simp [step]
      omega
    rw [←ha0',hpar,←hx0',←hm1] at hrel
    push_cast at hrel
    simpa [Int.add_assoc,Int.two_mul] using hrel
  have hbranch : if r=1 then 2*k≤a else a<2*k := by
    by_cases h : r=1
    · simp [h] at hb
      unfold gap at hk0
      omega
    · simp [h] at hb
      unfold gap at hk0
      omega
  have hy : 5≤y := by
    have hgi : (10:Int)≤gap (step r s) := by exact_mod_cast hg
    omega
  refine ⟨a,k,x,y,rfl,rfl,?_,?_,hy,hbranch,hM,hA,ha0',hm0,hx0',?_,hpar⟩
  · omega
  · omega
  · omega

/-- Source section edge law for the relaxed low-output guard. -/
theorem source_step_of_exact_guards5 (next : State → Option State)
    (law : EdgeLaw next) (r : Nat) (s : State) (hr : 1≤r)
    (hi : inputOK (lift s) (r==1))
    (ho : outputOK5 (lift (step r s))) :
    next (decode s)=some (decode (step r s)) := by
  let e := edgeData5_of_guards r s hr hi ho
  exact law e.a e.k e.x e.y r hr e.ha e.hk e.hy e.branch e.mass
    (by exact_mod_cast e.area)

/-- Primitive CLine path for one ordinary section edge, valid down to y=5. -/
theorem ordinary_step_path5 (r : Nat) (s : State) (hr : 1≤r)
    (hi : inputOK (lift s) (r==1))
    (ho : outputOK5 (lift (step r s))) :
    ∃ T W, Path T W (enc s) (enc (step r s)) ∧
      (T:Int)=edgeClock r s ∧ 6*(W:Int)=edgeWeight6 r s := by
  let e := edgeData5_of_guards r s hr hi ho
  obtain ⟨T,W,hpath,hcalls,hweight⟩ :=
    BB6.Agent12CountedOrdinaryLow.ordinary_edge5 e.a e.k e.x e.y r hr
      e.ha e.hk e.hy e.branch e.mass e.area
  refine ⟨T,W,?_,?_,?_⟩
  · simpa [enc,e.dec,e.decNext] using hpath
  · simpa [edgeClock,e.gap_eq,e.parity_eq] using hcalls
  · simpa [edgeWeight6,e.a_eq,e.m_eq,e.x_eq,e.parity_eq] using hweight

/-- The exact section run and its lane endpoint are determined by a LaneSpec5. -/
theorem lane_word5 (next : State → Option State) (law : EdgeLaw next)
    (q N : Nat) (u : Nat → BitState) (spec : LaneSpec5 q N u)
    (n d : Nat) (s : State) (hn : n+d≤N)
    (hstart : u (n+d)=lift s) (hevent : n+d=N ∨ q.testBit (n+d)=true)
    (hidle : u n=idle d (lift s))
    (hfirst : 0<d → q.testBit (n+d-1)=false)
    (h0 : n=0 → d=0) :
    runNext next n (some (decode s))=some (decode (run (word q d n) s)) ∧
    u 0=lift (run (word q d n) s) := by
  induction n generalizing d s with
  | zero =>
      have hd : d=0 := h0 rfl
      subst d
      simp [word,run,runNext,idle_zero] at hidle ⊢
      exact hidle
  | succ n ih =>
      have hnext := spec.next n (by omega)
      rw [hidle] at hnext
      cases hbit : q.testBit n
      · have hn0 : n≠0 := by
          intro h
          subst n
          rw [spec.closed] at hbit
          contradiction
        have heq : n+(d+1)=n+1+d := by omega
        simp only [word,hbit,Bool.false_eq_true,ite_false]
        rw [hbit,tick_false_idle] at hnext
        apply ih (d+1) s (by omega) (by rwa [heq]) (by rwa [heq]) hnext
          (by
            intro _
            rw [show n+(d+1)-1=n+d by omega]
            exact hfirst (by omega))
          (by
            intro h
            exact False.elim (hn0 h))
      · rw [hbit,tick_true_lift] at hnext
        have hi := spec.input (n+1+d) (by omega) hn hevent
        rw [hstart] at hi
        have hdir : q.testBit (n+1+d-1)=((d+1)==1) := by
          by_cases hd : d=0
          · simpa [hd] using hbit
          · rw [hfirst (by omega)]
            simp [hd]
        rw [hdir] at hi
        have ho := spec.output n (by omega) hbit
        rw [hnext] at ho
        have hedge := source_step_of_exact_guards5 next law (d+1) s (by omega) hi ho
        have htail := ih 0 (step (d+1) s) (by omega)
          (by simpa using hnext) (Or.inr (by simpa using hbit))
          (by simpa [idle_zero] using hnext) (by omega) (by simp)
        constructor
        · rw [hedge] at htail.1
          simpa [word,run] using htail.1
        · simpa [word,run] using htail.2

/-- The raw primitive path and its exact aggregate section clocks. -/
theorem lane_path5 (q N : Nat) (u : Nat → BitState)
    (spec : LaneSpec5 q N u)
    (n d : Nat) (s : State) (hn : n+d≤N)
    (hstart : u (n+d)=lift s) (hevent : n+d=N ∨ q.testBit (n+d)=true)
    (hidle : u n=idle d (lift s))
    (hfirst : 0<d → q.testBit (n+d-1)=false)
    (h0 : n=0 → d=0) :
    ∃ T W, Path T W (enc s) (enc (run (word q d n) s)) ∧
      (T:Int)=clocks (word q d n) s .1 ∧
      6*(W:Int)=clocks (word q d n) s .2 := by
  induction n generalizing d s with
  | zero =>
      have hd : d=0 := h0 rfl
      subst d
      refine ⟨0,0,Path.nil _,?_,?_⟩ <;> simp [word,run,clocks,idle_zero]
  | succ n ih =>
      have hnext := spec.next n (by omega)
      rw [hidle] at hnext
      cases hbit : q.testBit n
      · have hn0 : n≠0 := by
          intro h
          subst n
          rw [spec.closed] at hbit
          contradiction
        have heq : n+(d+1)=n+1+d := by omega
        simp only [word,hbit,Bool.false_eq_true,ite_false]
        rw [hbit,tick_false_idle] at hnext
        obtain ⟨T,W,hpath,hcalls,hweight⟩ :=
          ih (d+1) s (by omega) (by rwa [heq]) (by rwa [heq]) hnext
            (by
              intro _
              rw [show n+(d+1)-1=n+d by omega]
              exact hfirst (by omega))
            (by
              intro h
              exact False.elim (hn0 h))
        exact ⟨T,W,by simpa [run] using hpath,
          by simpa [clocks] using hcalls,
          by simpa [clocks] using hweight⟩
      · rw [hbit,tick_true_lift] at hnext
        have hi := spec.input (n+1+d) (by omega) hn hevent
        rw [hstart] at hi
        have hdir : q.testBit (n+1+d-1)=((d+1)==1) := by
          by_cases hd : d=0
          · simpa [hd] using hbit
          · rw [hfirst (by omega)]
            simp [hd]
        rw [hdir] at hi
        have ho := spec.output n (by omega) hbit
        rw [hnext] at ho
        obtain ⟨T1,W1,hpath1,hcalls1,hweight1⟩ :=
          ordinary_step_path5 (d+1) s (by omega) hi ho
        obtain ⟨T2,W2,hpath2,hcalls2,hweight2⟩ :=
          ih 0 (step (d+1) s) (by omega) (by simpa using hnext)
            (Or.inr (by simpa using hbit))
            (by simpa [idle_zero] using hnext) (by omega) (by simp)
        refine ⟨T1+T2,W1+W2,?_,?_,?_⟩
        · have hp : Path (T1+T2) (W1+W2) (enc s)
              (enc (run (word q 0 n) (step (d+1) s))) := by
            simpa using hpath1.append hpath2
          simpa [word,run,hbit] using hp
        · simp [clocks,word,hbit,hcalls1,hcalls2]
        · simp [clocks,word,hbit,hweight1,hweight2]

theorem lift_injective : Function.Injective lift := by
  intro s t h
  have hm := congrArg BitState.m h
  have hb := congrArg BitState.b h
  cases s with
  | mk sa sm =>
    cases t with
    | mk ta tm =>
      simp [lift,parity] at hm hb
      omega

/-- A LaneSpec5 plus its two endpoints yields an authentic CLine Path. -/
theorem source_path5_of_spec (q N : Nat) (u : Nat → BitState)
    (spec : LaneSpec5 q N u) (s t : State)
    (hstart : u N=lift s) (hend : u 0=lift t) :
    ∃ T W, Path T W (enc s) (enc t) ∧
      (T:Int)=clocks (word q 0 N) s .1 ∧
      6*(W:Int)=clocks (word q 0 N) s .2 := by
  obtain ⟨T,W,hpath,hcalls,hweight⟩ :=
    lane_path5 q N u spec N 0 s (by omega)
      (by simpa using hstart) (Or.inl (by omega))
      (by simpa [idle_zero] using hstart) (by omega) (by simp)
  have hrun := lane_word5 BB6.Agent12WordBlock.secNext
    BB6.Agent12WordBlock.source_edge_law q N u spec N 0 s (by omega)
      (by simpa using hstart) (Or.inl (by omega))
      (by simpa [idle_zero] using hstart) (by omega) (by simp)
  have hLift : lift t=lift (run (word q 0 N) s) := by
    calc
      lift t= u 0 := hend.symm
      _=lift (run (word q 0 N) s) := hrun.2
  have hrunEq : run (word q 0 N) s=t := (lift_injective hLift).symm
  rw [hrunEq] at hpath
  exact ⟨T,W,hpath,hcalls,hweight⟩

/-- Join the primitive Path to the bit-plane clock, yielding an exact
    primitive-step count for any aligned low-output event segment. -/
theorem source_path5_and_bitplane_clock (q N : Nat)
    (v : BB6.Agent12LaneCertificate.Trace) (w : BB6.Agent12LaneClock.Aligned)
    (spec : LaneSpec5 q N (lane v)) (hq : q<2^N)
    (ha : alignmentChecked N q v w) (s t : State)
    (hstart : lane v N=lift s) (hend : lane v 0=lift t) :
    ∃ T W, Path T W (enc s) (enc t) ∧
      (T:Int)=sumTerms N q (callsTerms N w) ∧
      6*(W:Int)=sumTerms N q (weightTerms N w) := by
  obtain ⟨T,W,hpath,hcalls,hweight⟩ :=
    source_path5_of_spec q N (lane v) spec s t hstart hend
  have ts : TickSpec q N (lane v) := ⟨spec.next⟩
  have os0 := BB6.Agent12LaneClock.origin_spec N q v w ha
  let os : OriginRecurrence q N (lane v) (origin w) (value w.age) :=
    ⟨os0.event,os0.idle⟩
  have hState : origin w N=lift s := ha.1.trans hstart
  have hAge : value w.age N=0 := ha.2.1
  have hBoundary : lane v N=idle 0 (origin w N) := by
    rcases os0.top with ⟨ho,ha'⟩
    calc
      lane v N=origin w N := ho.symm
      _=idle (value w.age N) (origin w N) := by
        rw [ha']
        exact (idle_zero _).symm
  have hclock := clock_word q N 0 (lane v) (origin w) (value w.age)
    ts os s hState hAge hBoundary
  have hcallsSum := BB6.Agent12LaneClock.calls_sum N q v w ha hq
  have hweightSum := BB6.Agent12LaneClock.weight_sum N q v w ha hq
  have hsumCalls : sumTerms N q (callsTerms N w)=(clocks (word q 0 N) s).1 :=
    hcallsSum.trans (congrArg Prod.fst hclock).symm
  have hsumWeights : sumTerms N q (weightTerms N w)=(clocks (word q 0 N) s).2 :=
    hweightSum.trans (congrArg Prod.snd hclock).symm
  exact ⟨T,W,hpath,hcalls.trans hsumCalls.symm,hweight.trans hsumWeights.symm⟩

end BB6.Agent12LanePathSource
