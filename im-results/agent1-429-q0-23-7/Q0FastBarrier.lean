import Q0DoubleBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 8000000

def rowNext (a : Nat) (s : Nat×Nat) : List (Nat×Nat) :=
  digits.flatMap fun d => digits.filterMap fun r =>
    if carryNum a s.1 s.2 r d%16=0 then
      some (s.1+cost d,carryY a s.1 s.2 r d) else none

def rowLayers (a : Nat) : Nat → List (Nat×Nat) → List (Nat×Nat)
  | 0,ss => ss
  | n+1,ss => rowLayers a n (ss.flatMap (rowNext a)).eraseDups

theorem rowLayers_complete {a q e Q f : Nat} {w v : List Digit}
    (h : Carry a w v q e Q f) (ss : List (Nat×Nat)) (hm : (q,e)∈ss) :
    (Q,f)∈rowLayers a w.length ss := by
  induction h generalizing ss with
  | nil => exact hm
  | @cons r d w v q e Q f hd ht ih =>
    simp only [List.length_cons,rowLayers]
    apply ih
    apply List.mem_eraseDups.mpr
    apply List.mem_flatMap.mpr
    refine ⟨(q,e),hm,?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨d,mem_digits d,?_⟩
    exact List.mem_filterMap.mpr ⟨r,mem_digits r,by simp [hd]⟩

def hasCrossFast (a b k : Nat) : Bool :=
  (List.range ((a+b)/3+1)).any fun e0 =>
    (rowLayers a k [(b,e0)]).any fun s =>
      strip a b e0 s.1 s.2 k b e0 s.1 s.2 []

theorem hasCrossFast_complete {a b k : Nat} (h : Cross2 a b k) : hasCrossFast a b k=true := by
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
  obtain ⟨hp,hform⟩ := trace_formula ht
  have hp' : ((a*16^k+b : Nat):Int)=(p:Int)+L w := by exact_mod_cast hp
  have hy' : (y:Int)=M w*e-b*D w-E w := by grind
  have hcone : cone a b e ([] ++ w) := by
    simp only [List.nil_append,cone]
    constructor <;> omega
  unfold hasCrossFast
  apply List.any_eq_true.mpr
  refine ⟨e,List.mem_range.mpr (by omega),?_⟩
  apply List.any_eq_true.mpr
  refine ⟨(q,f),?_,?_⟩
  · simpa [hw] using rowLayers_complete hcarry [(b,e)] (by simp)
  · simpa [hw] using strip_complete hcarry hcarry2 (by omega) [] hcone

def barrierFast (a k : Nat) : Bool := (List.range 6).all fun b => !(hasCrossFast a b k)

theorem barrierFast_sound {a k : Nat} (h : barrierFast a k=true) {b : Nat} (hb : b<6) : ¬ Cross2 a b k := by
  intro hc
  have ht := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  simp [hasCrossFast_complete hc] at ht

#print axioms rowLayers_complete
#print axioms hasCrossFast_complete
#print axioms barrierFast_sound
end BB429Q0Macro.RankBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro

theorem q0_fast_barrier {Reach : Nat→Nat→Prop} (src : Source Reach)
    {a k u n x y : Nat} (hb : barrierFast a k=true)
    (hl : 24*u+22+6*k≤a*16^k)
    (hh : a*16^k+5+12*k≤48*u+37)
    (hn : n=23+32*u) (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) :
    ¬ Reach x y := by
  intro h
  have hp := q0_path src u n x y hn hx hy h
  exact path_barrier_of_noCross2 (fun _ h => barrierFast_sound hb h) (by omega) (by omega) hl (by omega) hp

#print axioms q0_fast_barrier
end BB429Q0Macro.RankBarrier
