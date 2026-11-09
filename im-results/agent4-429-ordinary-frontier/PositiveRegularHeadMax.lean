import W4HeadPrefix
import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429PositiveRegularHeadMax

open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4HeadPrefix

/-- Exact four-step preparation, with no rightward head excursion. -/
theorem juncPos_prep4_max (u v w : Nat) :
 runWithMax 4 (junc (u+1) v w) =
  some (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
    (true :: (pairs01 v ++ ones w ++ [false,true])), 0, 0) := by rfl

/-- A/0,B/1 pair advances two cells without overshooting its endpoint. -/
theorem shift_A01_pair_max (left suffix : List Bool) :
 runWithMax 2 (z 0 left false (true :: suffix)) =
 some (z 0 (true::true::left) (suffix.headD false) suffix.tail, 2, 2) := by
 cases suffix <;> rfl

/-- Entire A/0,B/1 sweep: its endpoint is the rightmost position visited. -/
theorem shift_A01_max (v : Nat) (left suffix : List Bool) :
 runWithMax (2*(v+1))
  (z 0 left false (true :: (pairs01 v ++ (true :: suffix)))) =
 some (z 0 (ones (2*(v+1)) ++ left) true suffix,
   ((2*(v+1) : Nat) : Int), ((2*(v+1) : Nat) : Int)) := by
 induction v generalizing left suffix with
 | zero =>
     simpa [pairs01,ones] using (shift_A01_pair_max left (true :: suffix))
 | succ v ih =>
     have hpair : runWithMax 2
       (z 0 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
         some (z 0 (true :: true :: left) false
           (true :: (pairs01 v ++ (true :: suffix))),2,2) := by rfl
     rw [show 2*(v+2)=2+2*(v+1) by omega,runWithMax_add,hpair]
     simp only [Option.bind_some]
     rw [ih (true :: true :: left) suffix]
     simp only [Option.map_some]
     have hones : ones (2*(v+1)) ++ (true :: true :: left) =
       ones (2*(v+2)) ++ left := by
       change List.replicate (2*(v+1)) true ++ (true :: true :: left) =
         List.replicate (2*(v+2)) true ++ left
       rw [show 2*(v+2)=(2*(v+1))+2 by omega]
       rw [← List.replicate_append_replicate (n:=2*(v+1)) (m:=2) (a:=true)]
       simp [List.append_assoc]
     rw [hones, show 2+2*(v+1) = 2*(v+2) by omega]
     simp only [Option.some.injEq,Prod.mk.injEq]
     constructor
     · trivial
     · constructor <;> simp [Int.max_def] <;> omega

/-- The A/1,F/1 pair moves left twice and never beyond its entry head. -/
theorem shift_A11_pair_max (tail suffix : List Bool) :
 runWithMax 2 (z 0 (true :: true :: true :: tail) true (true :: suffix)) =
  some (z 0 (true :: tail) true (true :: false :: true :: suffix), -2, 0) := by rfl

/-- All A/1,F/1 pairs remain at or to the left of their entry head. -/
theorem shift_A11_max (p : Nat) (left suffix : List Bool) :
 runWithMax (2*p) (z 0 (true :: (ones (2*p) ++ left)) true (true :: suffix)) =
  some (z 0 (true :: left) true (true :: (pairs01 p ++ suffix)), -((2*p : Nat) : Int), 0) := by
 induction p generalizing left suffix with
 | zero => rfl
 | succ p ih =>
    have hrep : ones (2*(p+1)) = [true,true] ++ ones (2*p) := by
      change List.replicate (2*(p+1)) true = _
      rw [show 2*(p+1) = 2+2*p by omega]
      change List.replicate (2+2*p) true = _
      rw [← List.replicate_append_replicate (n:=2) (m:=2*p) (a:=true)]
      rfl
    have hpair : runWithMax 2
       (z 0 (true::true::true::(ones (2*p) ++ left)) true (true::suffix)) =
       some (z 0 (true::(ones (2*p) ++ left)) true (true::false::true::suffix),-2,0) := by
       exact shift_A11_pair_max (ones (2*p) ++ left) suffix
    rw [show 2*(p+1)=2+2*p by omega]
    have hrep2 : ones (2+2*p) = [true,true] ++ ones (2*p) := by
       simpa only [show 2+2*p=2*(p+1) by omega] using hrep
    rw [hrep2]
    simp only [List.cons_append, List.nil_append]
    rw [runWithMax_add,hpair]
    simp only [Option.bind_some]
    rw [ih left (false::true::suffix)]
    simp only [Option.map_some]
    have hright : pairs01 p ++ (false::true::suffix) = pairs01 (p+1) ++ suffix := by
      have happ : ∀ n : Nat, pairs01 n ++ [false,true] = pairs01 (n+1) := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
            change false::true::(pairs01 n ++ [false,true]) = false::true::pairs01 (n+1)
            rw [ih]
      calc
        pairs01 p ++ (false::true::suffix) = (pairs01 p ++ [false,true]) ++ suffix := by simp [List.append_assoc]
        _ = pairs01 (p+1) ++ suffix := by rw [happ p]
    rw [hright]
    simp only [Option.some.injEq,Prod.mk.injEq]
    constructor
    · trivial
    · constructor <;> simp [Int.max_def] <;> omega

/-- The right-going half of an ordinary positive-left Junc return reaches
its maximum +2v+2 exactly at MidA, for all remaining right budgets. -/
theorem juncPos_to_midA_max (u v w : Nat) :
 runWithMax (2*v+6) (junc (u+1) v (w+2)) =
 some (midApos u v (w+2), ((2*v+2 : Nat) : Int), ((2*v+2 : Nat) : Int)) := by
 have hprep := juncPos_prep4_max u v (w+2)
 have hshift := shift_A01_max v
   (true::true::true::(pairs01 u ++ ones 5)) (ones (w+1) ++ [false,true])
 have hright : ones (w+2) = true :: ones (w+1) := by
   change List.replicate (w+2) true = true::List.replicate (w+1) true
   rw [show w+2=(w+1)+1 by omega,List.replicate_succ]
 have hinput : z 0 (true::true::true::(pairs01 u ++ ones 5)) false
   (true :: (pairs01 v ++ ones (w+2) ++ [false,true])) =
   z 0 (true::true::true::(pairs01 u ++ ones 5)) false
     (true :: (pairs01 v ++ (true :: (ones (w+1) ++ [false,true])))) := by
    rw [hright]
    simp [List.append_assoc,List.cons_append]
 have hcfg : z 0
      (ones (2*(v+1)) ++ (true::true::true::(pairs01 u ++ ones 5)))
      true (ones (w+1) ++ [false,true]) =
   midApos u v (w+2) := by
    have hprefix : ones (2*(v+1)) ++ [true,true,true] =
      true::ones (2*(v+2)) := by
      change List.replicate (2*(v+1)) true ++ [true,true,true] =
         true :: List.replicate (2*(v+2)) true
      calc
        List.replicate (2*(v+1)) true ++ [true,true,true] =
          List.replicate (2*(v+1)+3) true := by
             change List.replicate (2*(v+1)) true ++ List.replicate 3 true = _
             exact List.replicate_append_replicate
        _ = List.replicate (1+2*(v+2)) true := by congr 1 <;> omega
        _ = true :: List.replicate (2*(v+2)) true := by
          rw [show 1+2*(v+2)=(2*(v+2))+1 by omega,List.replicate_succ]
    rw [midApos]
    simp only [show (w+2)-1=w+1 by omega]
    calc
     z 0 (ones (2*(v+1)) ++ (true::true::true::(pairs01 u ++ ones 5))) true (ones (w+1) ++ [false,true]) =
       z 0 ((ones (2*(v+1)) ++ [true,true,true]) ++ (pairs01 u ++ ones 5)) true (ones (w+1) ++ [false,true]) := by simp [List.append_assoc]
     _ = z 0 (true::(ones (2*(v+2)) ++ pairs01 u ++ ones 5)) true (ones (w+1) ++ [false,true]) := by rw [hprefix]; simp [List.append_assoc]
 have ht : 2*v+6=4+2*(v+1) := by omega
 rw [ht,runWithMax_add,hprep]
 simp only [Option.bind_some]
 rw [hinput,hshift,hcfg]
 simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
 constructor
 · trivial
 · constructor <;> simp [Int.max_def] <;> omega

/-- The left-going half finishes the ordinary return while remaining at
or left of its MidA entry head. -/
theorem midApos_to_junc_max (u v w : Nat) :
 runWithMax (2*(v+2)) (midApos u v (w+2)) =
 some (junc u (v+2) w, -((2*(v+2) : Nat) : Int), 0) := by
 have hshift := shift_A11_max (v+2) (pairs01 u ++ ones 5) (ones w ++ [false,true])
 have hones : ones (w+1) = true :: ones w := by
   change List.replicate (w+1) true = true::List.replicate w true
   rw [List.replicate_succ]
 have hin : midApos u v (w+2) =
   z 0 (true :: (ones (2*(v+2)) ++ (pairs01 u ++ ones 5))) true
      (true::(ones w ++ [false,true])) := by
   simp [midApos,hones,show w+2-1=w+1 by omega,List.append_assoc]
 rw [hin,hshift]
 simp [junc,List.append_assoc]

/-- Exact original-table maximum head displacement over every primitive
prefix of every ordinary positive-left Junc return. -/
theorem juncPos_ordinary_max (u v w : Nat) :
 runWithMax (4*v+10) (junc (u+1) v (w+2)) =
 some (junc u (v+2) w, -2, ((2*v+2 : Nat) : Int)) := by
 have hfirst := juncPos_to_midA_max u v w
 have hlast := midApos_to_junc_max u v w
 have ht : 4*v+10=(2*v+6)+2*(v+2) := by omega
 rw [ht,runWithMax_add,hfirst]
 simp only [Option.bind_some]
 rw [hlast]
 simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
 constructor
 · trivial
 · constructor <;> simp [Int.max_def] <;> omega

/-- Every primitive prefix of an ordinary positive-u Junc transition
stays strictly left of the starting rightmost marked tape cell. -/
theorem juncPos_ordinary_prefix_before_old_mark
 (u v w t : Nat) (ht : t ≤ 4*v+10) (p : Zipper × Int × Int)
 (hp : runWithMax t (junc (u+1) v (w+2)) = some p) :
 p.2.1 < ((2*v+w+5 : Nat) : Int) := by
 have hsum : t+(4*v+10-t)=4*v+10 := by omega
 have hfull := juncPos_ordinary_max u v w
 rw [← hsum] at hfull
 have hbound := runWithMax_prefix_le t (4*v+10-t)
   (junc (u+1) v (w+2)) p hp
   (junc u (v+2) w,-2,((2*v+2 : Nat) : Int)) hfull
 simpa only [Prod.snd] at hbound
 omega

#print axioms shift_A01_max
#print axioms shift_A11_max
#print axioms juncPos_ordinary_max
#print axioms juncPos_ordinary_prefix_before_old_mark

end BB429PositiveRegularHeadMax
