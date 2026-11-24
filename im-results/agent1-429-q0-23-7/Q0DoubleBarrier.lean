import Q0RankBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 8000000

def digits : List Digit := [.zero,.one,.four,.five]
theorem mem_digits (d : Digit) : d ∈ digits := by cases d <;> decide

def cone (a b e : Nat) (w : List Digit) : Prop :=
  0 < M w*e-b*D w-E w ∧
  3*(M w*e-b*D w-E w)<(a:Int)*M w+b-L w

instance (a b e : Nat) (w : List Digit) : Decidable (cone a b e w) := by
  unfold cone
  infer_instance

def strip (a b e0 q1 e1 : Nat) : Nat → Nat → Nat → Nat → Nat → List Digit → Bool
  | 0,q,e,_,_,pre => (q==q1) && (e==e1) && decide (cone a b e0 pre.reverse)
  | n+1,q,e,Q,f,pre =>
    if q+3*(n+1)≤q1 ∧ q1≤q+6*(n+1) then
      digits.any fun d => digits.any fun r =>
        if carryNum a q e r d % 16=0 then
          digits.any fun z =>
            if carryNum a Q f d z % 16=0 then
              strip a b e0 q1 e1 n (q+cost d) (carryY a q e r d)
                (Q+cost z) (carryY a Q f d z) (r::pre)
            else false
        else false
    else false

theorem strip_complete {a b e0 q1 e1 q e Q f Qf ff : Nat}
    {w v z : List Digit} (h : Carry a w v q e q1 e1)
    (h2 : Carry a v z Q f Qf ff) (he : 3*e≤q+a)
    (pre : List Digit) (hc : cone a b e0 (pre.reverse++w)) :
    strip a b e0 q1 e1 w.length q e Q f pre=true := by
  induction h generalizing Q f Qf ff z pre with
  | nil q e =>
    simpa [strip] using hc
  | @cons r d w v q e Q1 F1 hd ht ih =>
    cases h2 with
    | @cons _ t _ _ _ _ _ _ hdz htail =>
      have hb := carry_bounds (Carry.cons r d hd ht) he
      have hv : w.length=v.length := by
        exact (carry_bounds ht (carry_step_bound a q e r d he hd)).1
      have hbound : q+3*(w.length+1)≤Q1 ∧ Q1≤q+6*(w.length+1) := by
        simp only [List.length_cons] at hb
        omega
      simp only [List.length_cons,strip,ite_eq_left hbound]
      apply List.any_eq_true.mpr
      refine ⟨d,mem_digits d,?_⟩
      apply List.any_eq_true.mpr
      refine ⟨r,mem_digits r,?_⟩
      rw [ite_eq_left hd]
      apply List.any_eq_true.mpr
      refine ⟨t,mem_digits t,?_⟩
      rw [ite_eq_left hdz]
      apply ih htail (carry_step_bound a q e r d he hd) (r::pre)
      simpa [List.reverse_cons,List.append_assoc] using hc

def hasCross2 (a b k : Nat) : Bool :=
  (List.range (3*k+1)).any fun j =>
    let q1 := b+3*k+j
    (List.range ((a+q1)/3+1)).any fun e1 =>
      (List.range ((a+b)/3+1)).any fun e0 =>
        strip a b e0 q1 e1 k b e0 q1 e1 []

def Cross2 (a b k : Nat) : Prop :=
  ∃ (w v z : List Digit) (p y Y P2 Y2 P3 Y3 : Nat),
    w.length=k ∧ v.length=k ∧ z.length=k ∧ 0<y ∧ 3*y<p ∧
    Trace w p y (a*16^k+b) Y ∧ Trace v (a*16^k+b) Y P2 Y2 ∧
    Trace z P2 Y2 P3 Y3

theorem hasCross2_complete {a b k : Nat} (h : Cross2 a b k) : hasCross2 a b k=true := by
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
  have hcone : cone a b e ([] ++ w) := by
    simp only [List.nil_append,cone]
    constructor <;> omega
  unfold hasCross2
  apply List.any_eq_true.mpr
  refine ⟨q-(b+3*k),List.mem_range.mpr (by omega),?_⟩
  have hq' : b+3*k+(q-(b+3*k))=q := by omega
  simp only [hq']
  apply List.any_eq_true.mpr
  refine ⟨f,List.mem_range.mpr (by omega),?_⟩
  apply List.any_eq_true.mpr
  refine ⟨e,List.mem_range.mpr (by omega),?_⟩
  simpa [hw] using strip_complete hcarry hcarry2 (by omega) [] hcone

def barrier (a k : Nat) : Bool := (List.range 6).all fun b => !(hasCross2 a b k)

theorem barrier_sound {a k : Nat} (h : barrier a k=true) {b : Nat} (hb : b<6) : ¬ Cross2 a b k := by
  intro hc
  have ht := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  simp [hasCross2_complete hc] at ht

#print axioms strip_complete
#print axioms hasCross2_complete
#print axioms barrier_sound
end BB429Q0Macro.RankBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 8000000

private theorem cost_bounds (d : Digit) : 3≤cost d ∧ cost d≤6 := by cases d <;> decide

theorem trace_rank {w p y P Y} (h : Trace w p y P Y) :
    p+3*w.length≤P ∧ P≤p+6*w.length := by
  induction h with
  | nil => simp
  | cons d hd ht ih =>
    have hc := cost_bounds d
    simp only [List.length_cons]
    unfold nextP at ih
    omega

theorem trace_strict {w p y P Y} (h : Trace w p y P Y)
    (hy : 0<y) (hc : 3*y<p) : 0<Y ∧ 3*Y<P := by
  induction h with
  | nil => exact ⟨hy,hc⟩
  | cons d hd ht ih =>
    obtain ⟨hy',hc'⟩ := interior_step d _ _ hy hc hd
    exact ih hy' hc'

theorem trace_split {w p y P Y} (h : Trace w p y P Y) (n : Nat) :
    ∃ q e, Trace (w.take n) p y q e ∧ Trace (w.drop n) q e P Y := by
  induction n generalizing w p y with
  | zero => exact ⟨p,y,by simpa using Trace.nil p y,by simpa using h⟩
  | succ n ih =>
    cases h with
    | nil => exact ⟨_,_,by simp; exact .nil ..,by simp; exact .nil ..⟩
    | cons d hd ht =>
      obtain ⟨q,e,h1,h2⟩ := ih ht
      exact ⟨q,e,by simpa using Trace.cons d hd h1,by simpa using h2⟩

theorem rank_cross {w p y P Y} (h : Trace w p y P Y) (B : Nat)
    (hlo : p≤B) (hhi : B≤P) :
    ∃ i q e, i≤w.length ∧ B≤q ∧ q<B+6 ∧
      Trace (w.take i) p y q e ∧ Trace (w.drop i) q e P Y := by
  induction h with
  | nil p y =>
    exact ⟨0,p,y,by simp,by omega,by omega,by simp; exact .nil ..,by simp; exact .nil ..⟩
  | @cons d w p y P Y hd ht ih =>
    by_cases he : p=B
    · exact ⟨0,p,y,by simp,by omega,by omega,by simpa using Trace.nil p y,by simpa using Trace.cons d hd ht⟩
    by_cases hn : nextP d p≤B
    · obtain ⟨i,q,e,hi,hq,hq',h1,h2⟩ := ih hn hhi
      exact ⟨i+1,q,e,by simp; omega,hq,hq',by simpa using Trace.cons d hd h1,by simpa using h2⟩
    · have hc := cost_bounds d
      have hq : nextP d p<B+6 := by unfold nextP; omega
      refine ⟨1,nextP d p,nextY d p y,by simp,by omega,hq,?_,?_⟩
      · simpa using Trace.cons d hd (Trace.nil (nextP d p) (nextY d p y))
      · simpa using ht

/-- A certified barrier cuts a whole rank interval, irrespective of the
    intermediate path digits. -/
theorem path_barrier_of_noCross2 {a k m p y : Nat} (hb : ∀ b, b<6 → ¬ Cross2 a b k)
    (hy : 0<y) (hc : 3*y<p)
    (hl : p+6*k≤a*16^k) (hh : a*16^k+5+12*k≤p+3*m) :
    ¬ Path m p y := by
  intro hp
  obtain ⟨w,P,Y,hw,ht⟩ := trace_of_path hp
  have hr := trace_rank ht
  obtain ⟨i,q,e,hi,hq,hq',hpre,hpost⟩ := rank_cross ht (a*16^k) (by omega) (by omega)
  have hlen : (w.take i).length=i := by simp [Nat.min_eq_left hi]
  have hlen2 : (w.drop i).length=m-i := by simp [hw]
  have hr1 := trace_rank hpre
  have hr2 := trace_rank hpost
  have hk : k≤i := by omega
  have hk2 : 2*k≤m-i := by omega
  obtain ⟨r,s,hpre1,hpre2⟩ := trace_split hpre (i-k)
  obtain ⟨q2,e2,hpost1,hpost2⟩ := trace_split hpost k
  obtain ⟨q3,e3,hpost3,hpost4⟩ := trace_split hpost2 k
  obtain ⟨hs,hstrict⟩ := trace_strict hpre1 hy hc
  let b := q-a*16^k
  have hb' : b<6 := by dsimp [b]; omega
  have hqeq : q=a*16^k+b := by dsimp [b]; omega
  apply hb b hb'
  refine ⟨(w.take i).drop (i-k),(w.drop i).take k,((w.drop i).drop k).take k,
    r,s,e,q2,e2,q3,e3,?_,?_,?_,hs,hstrict,?_,?_,hpost3⟩
  · simp [hlen]; omega
  · simp [hlen2,Nat.min_eq_left (show k≤m-i by omega)]
  · simp; omega
  · rwa [←hqeq]
  · rwa [←hqeq]

theorem path_barrier {a k m p y : Nat} (hb : barrier a k=true)
    (hy : 0<y) (hc : 3*y<p)
    (hl : p+6*k≤a*16^k) (hh : a*16^k+5+12*k≤p+3*m) :
    ¬ Path m p y := by
  exact path_barrier_of_noCross2 (fun _ h => barrier_sound hb h) hy hc hl hh

/-- Each positive finite certificate excludes every q0 parameter in an
    explicit interval, with no enumeration of those parameters. -/
theorem q0_barrier {Reach : Nat→Nat→Prop} (src : Source Reach)
    {a k u n x y : Nat} (hb : barrier a k=true)
    (hl : 24*u+22+6*k≤a*16^k)
    (hh : a*16^k+5+12*k≤48*u+37)
    (hn : n=23+32*u) (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) :
    ¬ Reach x y := by
  intro h
  have hp := q0_path src u n x y hn hx hy h
  exact path_barrier hb (by omega) (by omega) hl (by omega) hp

#print axioms path_barrier
#print axioms q0_barrier
end BB429Q0Macro.RankBarrier
