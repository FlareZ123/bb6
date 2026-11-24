import Q0ConeCarry
import Std.Data.HashSet.Lemmas

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 10000000

structure StripState where
  q : Nat
  e : Nat
  Q : Nat
  f : Nat
  l : Nat
  c1 : Int
  c2 : Int
  deriving BEq, Hashable, ReflBEq, LawfulBEq, Repr

def stepState (a b : Nat) (s : StripState) (r d z : Digit) : StripState :=
  ⟨s.q+cost d,carryY a s.q s.e r d,s.Q+cost z,carryY a s.Q s.f d z,
    s.l-cost r,(s.c1+lowCoeff b s.l r)/16,(s.c2-3*lowCoeff b s.l r)/16⟩

def nextStates (a b q1 n : Nat) (s : StripState) : List StripState :=
  if s.q+3*n≤q1 ∧ q1≤s.q+6*n ∧ 3*n≤s.l ∧ s.l≤6*n then
    digits.flatMap fun d => digits.flatMap fun r =>
      if cost r≤s.l ∧ carryNum a s.q s.e r d%16=0 then
        digits.filterMap fun z =>
          if carryNum a s.Q s.f d z%16=0 then some (stepState a b s r d z) else none
      else []
  else []

def advance (a b q1 n : Nat) (ss : List StripState) : List StripState :=
  (Std.HashSet.ofList (ss.flatMap (nextStates a b q1 n))).toList

theorem mem_advance {a b q1 n : Nat} {ss : List StripState} {s s' : StripState}
    (hm : s∈ss) (hs : s'∈nextStates a b q1 n s) : s'∈advance a b q1 n ss := by
  unfold advance
  rw [Std.HashSet.mem_toList,Std.HashSet.mem_ofList]
  apply List.contains_iff_mem.mpr
  exact List.mem_flatMap.mpr ⟨s,hm,hs⟩

theorem mem_nextStates (a b q1 n : Nat) (s : StripState) (r d z : Digit)
    (hb : s.q+3*n≤q1 ∧ q1≤s.q+6*n ∧ 3*n≤s.l ∧ s.l≤6*n)
    (hl : cost r≤s.l) (hd : carryNum a s.q s.e r d%16=0)
    (hz : carryNum a s.Q s.f d z%16=0) :
    stepState a b s r d z∈nextStates a b q1 n s := by
  unfold nextStates
  rw [ite_eq_left hb]
  apply List.mem_flatMap.mpr
  refine ⟨d,mem_digits d,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r,mem_digits r,?_⟩
  rw [ite_eq_left (And.intro hl hd)]
  exact List.mem_filterMap.mpr ⟨z,mem_digits z,by simp [hz]⟩

def runLayers (a b q1 : Nat) : Nat → List StripState → List StripState
  | 0,ss => ss
  | n+1,ss => runLayers a b q1 n (advance a b q1 (n+1) ss)

def acceptState (a e0 q1 e1 : Nat) (s : StripState) : Bool :=
  (s.q==q1) && (s.e==e1) && (s.l==0) && decide (s.c1<(e0:Int)) &&
    decide (s.c2<(a:Int)-3*e0)

theorem L_bounds (w : List Digit) : 3*w.length≤L w ∧ L w≤6*w.length := by
  induction w with
  | nil => decide
  | cons r w ih =>
    have hr : 3≤cost r ∧ cost r≤6 := by cases r <;> decide
    simp only [L,List.length_cons]
    omega

theorem dp_complete {a b e0 q1 e1 q e Q f Qf ff l : Nat} {c1 c2 : Int}
    {w v z : List Digit} (h : Carry a w v q e q1 e1)
    (h2 : Carry a v z Q f Qf ff) (he : 3*e≤q+a)
    (hc : coneCarry a b e0 l c1 c2 w)
    (ss : List StripState) (hm : (⟨q,e,Q,f,l,c1,c2⟩ : StripState) ∈ ss) :
    (runLayers a b q1 w.length ss).any (acceptState a e0 q1 e1)=true := by
  induction h generalizing Q f Qf ff z l c1 c2 ss with
  | nil q e =>
    obtain ⟨hl,h1,h2⟩ := (coneCarry_nil a b e0 l c1 c2).mp hc
    apply List.any_eq_true.mpr
    exact ⟨_,hm,by simp [acceptState,hl,h1,h2]⟩
  | @cons r d w v q e Q1 F1 hd ht ih =>
    cases h2 with
    | @cons _ t _ _ _ _ _ _ hdz htail =>
      have hb := carry_bounds (Carry.cons r d hd ht) he
      have hL := L_bounds (r::w)
      have hl := hc.1
      have hbound : q+3*(w.length+1)≤Q1 ∧ Q1≤q+6*(w.length+1) ∧
          3*(w.length+1)≤l ∧ l≤6*(w.length+1) := by
        simp only [List.length_cons] at hb hL
        omega
      obtain ⟨hl',hc'⟩ := (coneCarry_cons a b e0 l c1 c2 r w).mp hc
      have hm' := mem_advance hm (mem_nextStates a b Q1 (w.length+1) ⟨q,e,Q,f,l,c1,c2⟩ r d t hbound hl' hd hdz)
      simp only [List.length_cons,runLayers]
      apply ih htail (carry_step_bound a q e r d he hd) hc' _
      exact hm'

def hasCrossDP (a b k : Nat) : Bool :=
  (List.range (3*k+1)).any fun j =>
    let q1 := b+3*k+j
    (List.range ((a+q1)/3+1)).any fun e1 =>
      (List.range ((a+b)/3+1)).any fun e0 =>
        let ss : List StripState := (List.range (3*k+1)).map fun j =>
          let l := 3*k+j
          ⟨b,e0,q1,e1,l,0,(l:Int)-b⟩
        (runLayers a b q1 k ss).any (acceptState a e0 q1 e1)

theorem hasCrossDP_complete {a b k : Nat} (h : Cross2 a b k) : hasCrossDP a b k=true := by
  obtain ⟨w,v,z,p,y,Y,P2,Y2,P3,Y3,hw,hv,hz,hy,hc,ht,hs,hs2⟩ := h
  have hP : ((a*16^k+b : Nat):Int)=(a:Int)*M w+b := by
    simp [M,hw,Int.natCast_add,Int.natCast_mul,Int.natCast_pow]
  obtain ⟨e,he,hY⟩ := near_power ht hy hc hP
  have hY' : Y=a*Dn w+e := by rw [←Dn_cast] at hY; exact_mod_cast hY
  have hs' : Trace v (a*16^(w++[]).length+b) (a*Dn (w++[])+e) P2 Y2 := by
    simpa [hw,←hY'] using hs
  obtain ⟨q,f,hcarry,hq,hf⟩ := carry_of_trace a b e w v [] P2 Y2 (by omega) hs'
  simp [hw] at hq hf
  have hs2' : Trace z (a*16^(v++[]).length+q) (a*Dn (v++[])+f) P3 Y3 := by
    simpa [hv,←hq,←hf] using hs2
  obtain ⟨Q,F,hcarry2,_,_⟩ := carry_of_trace a q f v z [] P3 Y3 (by omega) hs2'
  obtain ⟨_,hlo,hhi,hfe⟩ := carry_bounds hcarry (by omega)
  obtain ⟨hp,hform⟩ := trace_formula ht
  have hp' : ((a*16^k+b : Nat):Int)=(p:Int)+L w := by exact_mod_cast hp
  have hy' : (y:Int)=M w*e-b*D w-E w := by grind
  have hcone : cone a b e w := by
    unfold cone
    constructor <;> omega
  have hcc := (initial_coneCarry a b e w).mp hcone
  have hL := L_bounds w
  unfold hasCrossDP
  apply List.any_eq_true.mpr
  refine ⟨q-(b+3*k),List.mem_range.mpr (by omega),?_⟩
  have hq' : b+3*k+(q-(b+3*k))=q := by omega
  simp only [hq']
  apply List.any_eq_true.mpr
  refine ⟨f,List.mem_range.mpr (by omega),?_⟩
  apply List.any_eq_true.mpr
  refine ⟨e,List.mem_range.mpr (by omega),?_⟩
  let ss : List StripState := (List.range (3*k+1)).map fun j =>
    let l := 3*k+j
    ⟨b,e,q,f,l,0,(l:Int)-b⟩
  have hm : (⟨b,e,q,f,L w,0,(L w:Int)-b⟩ : StripState) ∈ ss := by
    apply List.mem_map.mpr
    refine ⟨L w-3*k,List.mem_range.mpr (by omega),?_⟩
    have hL' : 3*k+(L w-3*k)=L w := by omega
    simp [hL']
  simpa [hw,ss] using dp_complete hcarry hcarry2 (by omega) hcc ss hm

def barrierDP (a k : Nat) : Bool := (List.range 6).all fun b => !(hasCrossDP a b k)

theorem barrierDP_sound {a k : Nat} (h : barrierDP a k=true) {b : Nat} (hb : b<6) : ¬ Cross2 a b k := by
  intro hc
  have ht := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  simp [hasCrossDP_complete hc] at ht

#print axioms dp_complete
#print axioms hasCrossDP_complete
#print axioms barrierDP_sound
end BB429Q0Macro.RankBarrier
