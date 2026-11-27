import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13MirroredCounter
open BB6Coverage BB6Coverage.Agent31Pump

-- A synchronized little-endian binary counter, represented on both sides.
def p : PartialMachine := FAR.fromCodes [7,14,11,19,2,19,10,0,21,3,24,5]
abbrev Z (q : Fin 6) (l r : List Bool) : Z0 := ⟨q,l,r⟩
abbrev A := Z 0
abbrev H : List Bool := [true,true,true,true]
abbrev D0 : List Bool := [false,false,true,true]
abbrev D1 : List Bool := [true,false,true,true]
abbrev X : List Bool := [false,false,true]
abbrev Y : List Bool := [false,true,true]
abbrev U : List Bool := [true,true,true]
abbrev Q : List Bool := [false,true,false,true]
abbrev R : List Bool := [true,false,true,false]
abbrev S : List Bool := [false,true,false,true,true]
abbrev T : List Bool := [true,true,false,true,true]
abbrev pre : List Bool := [false,true,false,true,false]

theorem rep_next_tail (P : List Bool) (n : Nat) (L : List Bool) :
    rep P n ++ (P ++ L) = rep P (n+1) ++ L := by
  rw [← List.append_assoc,rep_snoc]
  rfl

theorem oneU (n : Nat) : rep U n ++ [true] = [true] ++ rep U n :=
  (rotate true [true,true] n).symm

theorem shiftQR (n : Nat) : rep Q n ++ pre = pre ++ rep R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep Q (n+1) ++ pre = Q ++ (rep Q n ++ pre) := by simp only [rep,List.append_assoc]
      _ = (Q++pre) ++ rep R n := by rw [ih,List.append_assoc]
      _ = pre ++ rep R (n+1) := by
        rw [show Q++pre=pre++R by rfl]
        simp only [rep,List.append_assoc]

def body (k : Nat) (tail : List Bool) : List Bool :=
  (rep Q (k+1) ++ [false]) ++ (rep U (k+1) ++ [true]) ++ tail

theorem body_split (k : Nat) (tail : List Bool) :
    body k tail = pre ++ rep R k ++ U ++ [true] ++ rep U k ++ tail := by
  have hq : rep Q (k+1) ++ [false] = pre ++ rep R k := by
    calc
      rep Q (k+1) ++ [false] = rep Q k ++ (Q ++ [false]) := by
        rw [← List.append_assoc,rep_snoc]
        rfl
      _ = rep Q k ++ pre := rfl
      _ = _ := shiftQR k
  have hu : rep U (k+1) ++ [true] = U ++ ([true] ++ rep U k) := by
    rw [rep,List.append_assoc,oneU]
  simp only [body,hq,hu,List.append_assoc]

-- Finite rules, all with arbitrary untouched tails, except the explicit blank edges.
theorem setupEntry (L W : List Bool) :
    run0 p 5 (A (false::L) (pre++W)) = some (Z 1 ([false,false,false,true,true,true]++L) W) := by rfl

theorem setupStep (L W : List Bool) :
    run0 p 4 (Z 1 ([false]++L) ([]++R++W)) =
      some (Z 1 ([false]++D0++L) ([]++W)) := by rfl

theorem setupExit (L W : List Bool) :
    run0 p 3 (Z 1 (false::L) (U++W)) = some (A (H++L) W) := by rfl

theorem carryEntry (L W : List Bool) :
    run0 p 9 (A (H++D0++L) (true::W)) =
      some (Z 1 ([true]++X++T++L) W) := by rfl

theorem carryStep (L W : List Bool) :
    run0 p 3 (Z 1 ([true]++L) ([]++Y++W)) =
      some (Z 1 ([true]++X++L) ([]++W)) := by rfl

theorem carryExit (L W : List Bool) :
    run0 p 2 (Z 1 (true::L) (U++W)) = some (A (U++L) (true::W)) := by rfl

theorem dropThree (L W : List Bool) :
    run0 p 3 (A (U++L) W) = some (Z 3 L ([true,false,true]++W)) := by rfl

theorem leftStep (L W : List Bool) :
    run0 p 3 (Z 3 ([]++X++L) ([]++W)) =
      some (Z 3 ([]++L) ([]++U++W)) := by rfl

theorem leftExit (L W : List Bool) :
    run0 p 5 (Z 3 (T++L) W) = some (A (H++L) (false::W)) := by rfl

theorem popStep (L W : List Bool) :
    run0 p 8 (A (H++D1++L) ([]++W)) = some (A (H++L) ([]++Q++W)) := by rfl

theorem dropHeader (L W : List Bool) :
    run0 p 4 (A (H++L) W) = some (A L (Q++W)) := by rfl

theorem overflowTurn (L : List Bool) :
    run0 p 9 (Z 1 (true::L) S) =
      some (A ([true,true,true,true,true]++X++L) [true]) := by rfl

theorem dropFive (L W : List Bool) :
    run0 p 5 (A ([true,true,true,true,true]++L) W) =
      some (Z 3 L ([true,false,true,false,true]++W)) := by rfl

theorem finishRoot (W : List Bool) :
    run0 p 14 (A (H++[true]) W) = some (A [] (Q++Q++W)) := by rfl

theorem setup (j : Nat) (L W : List Bool) :
    run0 p (4*j+8) (A (false::L) (body j W)) =
      some (A (H++rep D0 (j+1)++[true]++L) ([true]++rep U j++W)) := by
  rw [body_split]
  have h1 := setupEntry L (rep R j++U++[true]++rep U j++W)
  have h2 := sweepR p 1 [false] [] R D0 4 setupStep j
      ([false,false,true,true,true]++L) (U++[true]++rep U j++W)
  have h3 := setupExit (rep D0 (j+1)++[true]++L) ([true]++rep U j++W)
  have h2' : run0 p (4*j) (Z 1 ([false,false,false,true,true,true]++L) (rep R j++U++[true]++rep U j++W)) =
      some (Z 1 (false::(rep D0 (j+1)++[true]++L)) (U++[true]++rep U j++W)) := by
    simp only [Z,List.append_assoc,List.cons_append,List.nil_append] at ⊢
    rw [← rep_next_tail D0 j (true::L)]
    simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h2
  simpa only [A,Z,List.append_assoc,List.cons_append,List.singleton_append,show 5+4*j+3=4*j+8 by omega] using join0 (join0 h1 h2') h3

theorem carryCore (j : Nat) (L W : List Bool) :
    run0 p (6*j+22) (A (H++D0++L) ([true]++rep Y j++U++W)) =
      some (A (H++L) ([false]++rep U (j+1)++[true]++Y++W)) := by
  have h1 := carryEntry L (rep Y j++U++W)
  have h2 := sweepR p 1 [true] [] Y X 3 carryStep j (X++T++L) (U++W)
  have h2' : run0 p (3*j) (Z 1 ([true]++X++T++L) (rep Y j++U++W)) =
      some (Z 1 (true::(rep X (j+1)++T++L)) (U++W)) := by
    simp only [Z,List.append_assoc,List.cons_append,List.nil_append] at ⊢
    have hw := rep_next_tail X j (T++L)
    change rep X j ++ (false::false::true::true::true::false::true::true::L) =
      rep X (j+1) ++ (true::true::false::true::true::L) at hw
    rw [← hw]
    simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h2
  have h3 := carryExit (rep X (j+1)++T++L) W
  have h4 := dropThree (rep X (j+1)++T++L) (true::W)
  have h5 := sweepL p 3 [] [] X U 3 leftStep (j+1) (T++L) ([true]++Y++W)
  have h6 := leftExit L (rep U (j+1)++[true]++Y++W)
  simp only [List.nil_append,List.append_assoc,List.cons_append] at h1 h2' h3 h4 h5 h6 ⊢
  simpa only [show 9+3*j+2+3+3*(j+1)+5=6*j+22 by omega] using
    join0 (join0 (join0 (join0 (join0 h1 h2') h3) h4) h5) h6

theorem carryOverflowCore (k : Nat) (L : List Bool) :
    run0 p (6*k+34) (A (H++D0++L) ([true]++rep Y k++S)) =
      some (A (H++L) ([false]++rep U (k+2)++[true]++S)) := by
  have h1 := carryEntry L (rep Y k++S)
  have h2 := sweepR p 1 [true] [] Y X 3 carryStep k (X++T++L) S
  have h2' : run0 p (3*k) (Z 1 ([true]++X++T++L) (rep Y k++S)) =
      some (Z 1 (true::(rep X (k+1)++T++L)) S) := by
    simp only [Z,List.append_assoc,List.cons_append,List.nil_append] at ⊢
    have hw := rep_next_tail X k (T++L)
    change rep X k ++ (false::false::true::true::true::false::true::true::L) =
      rep X (k+1) ++ (true::true::false::true::true::L) at hw
    rw [← hw]
    simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h2
  have h3 := overflowTurn (rep X (k+1)++T++L)
  have h4 := dropFive (rep X (k+2)++T++L) [true]
  have h5 := sweepL p 3 [] [] X U 3 leftStep (k+2) (T++L) ([true]++S)
  have h6 := leftExit L (rep U (k+2)++[true]++S)
  have h3' : run0 p 9 (Z 1 (true::(rep X (k+1)++T++L)) S) =
      some (A ([true,true,true,true,true]++(rep X (k+2)++T++L)) [true]) := by
    simpa only [A,Z,rep,List.append_assoc,List.cons_append,List.singleton_append] using h3
  simp only [A,Z,List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] at h1 h2' h3' h4 h5 h6 ⊢
  simpa only [show 9+3*k+9+5+3*(k+2)+5=6*k+34 by omega,List.append_assoc] using
    join0 (join0 (join0 (join0 (join0 h1 h2') h3') h4) h5) h6

theorem pop (j : Nat) (L W : List Bool) :
    run0 p (8*j) (A (H++rep D1 j++L) W) =
      some (A (H++L) (rep Q j++W)) := by
  simpa only [List.nil_append] using sweepL p 0 H [] D1 Q 8 popStep j L W

theorem incWords (j : Nat) (L W : List Bool) :
    run0 p (18*j+34) (A (H++D0++rep D1 j++D0++L) ([true]++rep Y j++U++W)) =
      some (A (H++rep D0 (j+1)++D1++L) ([true]++rep U j++Y++W)) := by
  have h1 := carryCore j (rep D1 j++D0++L) W
  have h2 := pop j (D0++L) ([false]++rep U (j+1)++[true]++Y++W)
  have h3 := dropHeader (D0++L) (rep Q j++[false]++rep U (j+1)++[true]++Y++W)
  have h4 := setup j ([false,true,true]++L) (Y++W)
  have h3' : run0 p 4 (A (H++D0++L) (rep Q j++[false]++rep U (j+1)++[true]++Y++W)) =
      some (A (D0++L) (body j (Y++W))) := by
    simpa only [body,rep,List.append_assoc] using h3
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h1 h2 h3' h4 ⊢
  simpa only [show 6*j+22+8*j+4+(4*j+8)=18*j+34 by omega] using
    join0 (join0 (join0 h1 h2) h3') h4

def root (k : Nat) : Z0 := A [] (body k S)

theorem overflowWords (k : Nat) :
    run0 p (14*k+48) (A (H++D0++rep D1 k++[true]) ([true]++rep Y k++S)) =
      some (root (k+1)) := by
  have h1 := carryOverflowCore k (rep D1 k++[true])
  have h2 := pop k [true] ([false]++rep U (k+2)++[true]++S)
  have h3 := finishRoot (rep Q k++[false]++rep U (k+2)++[true]++S)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h1 h2 h3
  simpa only [root,body,A,Z,rep,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append,show 6*k+34+8*k+14=14*k+48 by omega] using
    join0 (join0 h1 h2) h3

def enc (f : Bool → List Bool) : List Bool → List Bool
  | [] => []
  | b::bs => f b ++ enc f bs

theorem enc_append (f : Bool → List Bool) (a b : List Bool) :
    enc f (a++b) = enc f a++enc f b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,enc,ih,List.append_assoc]

theorem enc_rep (f : Bool → List Bool) (b : Bool) (j : Nat) :
    enc f (List.replicate j b) = rep (f b) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ,enc,rep,ih]

def digit4 (b : Bool) : List Bool := if b then D1 else D0
def digit3 (b : Bool) : List Bool := if b then Y else U
def frame (bs : List Bool) : Z0 :=
  A (H++D0++enc digit4 bs++[true]) ([true]++enc digit3 bs++S)

theorem inc (j : Nat) (bs : List Bool) :
    run0 p (18*j+34) (frame (List.replicate j true++false::bs)) =
      some (frame (List.replicate j false++true::bs)) := by
  have h := incWords j (enc digit4 bs++[true]) (enc digit3 bs++S)
  simpa only [frame,enc_append,enc_rep,enc,digit4,digit3,if_true,if_false,Bool.false_eq_true,
    rep,List.append_assoc] using h

theorem replicate_right (j : Nat) (b : Bool) :
    List.replicate (j+1) b = List.replicate j b++[b] := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and]; exact ih

def fillCost : Nat → Nat
  | 0 => 0
  | j+1 => fillCost j+(18*j+34)+fillCost j

theorem fill (j : Nat) (bs : List Bool) :
    run0 p (fillCost j) (frame (List.replicate j false++bs)) =
      some (frame (List.replicate j true++bs)) := by
  induction j generalizing bs with
  | zero => rfl
  | succ j ih =>
    have h1 := ih (false::bs)
    have h2 := inc j bs
    have h3 := ih (true::bs)
    simpa only [fillCost,replicate_right,List.append_assoc,List.singleton_append] using
      join0 (join0 h1 h2) h3

theorem fillCost_closed (k : Nat) : fillCost k + 18*k + 52 = 52*2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [fillCost,Nat.pow_succ]; omega

theorem rootSetup (k : Nat) :
    run0 p (4*k+8) (root k) = some (frame (List.replicate k false)) := by
  have h := setup k [] S
  have pad (n : Nat) (W : List Bool) (hn : 0<n) :
      run0 p n (A [] W) = run0 p n (A [false] W) := by
    cases n with
    | zero => omega
    | succ n => rfl
  unfold root
  rw [pad _ _ (by omega)]
  simpa only [frame,enc_rep,digit4,digit3,if_false,Bool.false_eq_true,rep,List.append_assoc,List.append_nil] using h

theorem rootOverflow (k : Nat) :
    run0 p (14*k+48) (frame (List.replicate k true)) = some (root (k+1)) := by
  simpa only [frame,enc_rep,digit4,digit3,if_true,List.append_assoc] using overflowWords k

theorem rootGrowth (k : Nat) :
    run0 p (52*2^k+4) (root k) = some (root (k+1)) := by
  have h1 := rootSetup k
  have h2 := fill k []
  simp only [List.append_nil] at h2
  have h3 := rootOverflow k
  have hcost : 4*k+8+fillCost k+(14*k+48)=52*2^k+4 := by
    have := fillCost_closed k
    omega
  simpa only [hcost] using join0 (join0 h1 h2) h3

theorem seed : run0 p 48 (A [] []) = some (root 0) := by rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p root 48 (fun k => 52*2^k+4) seed (fun _ => by omega) rootGrowth m hm

#print axioms rootGrowth
#print axioms never
end BB6.Agent46Raw13MirroredCounter
