import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43RD1Return
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent25Raw43RD1Growth

private theorem firstTwo (k : Kind) (R : List Bool) :
    run0 (table k) 2 ⟨0,[],P++R⟩ = some ⟨2,[true,true,true],R⟩ := by
  cases k <;> rfl

private theorem cZero (k : Kind) (L : List Bool) :
    run0 (table k) 5 ⟨2,[false,true]++L,[]⟩ =
      some (E ([false,false]++L) 0) := by cases k <;> rfl

private def fastKind (b : Bool) : Kind := if b then .le else .rb
private def fastCost (b : Bool) : Nat := if b then 4 else 2
private theorem fastOne (b : Bool) (L R : List Bool) :
    run0 (table (fastKind b)) (fastCost b) ⟨2,[true,true]++L,[]++P++R⟩ =
    some ⟨2,[true,true]++P++L,[]++R⟩ := by cases b <;> rfl
private theorem fastEnd (b : Bool) (L : List Bool) :
    run0 (table (fastKind b)) (fastCost b) ⟨2,[true,true]++L,[]⟩ =
    some ⟨2,[false,true]++P++L,[]⟩ := by cases b <;> rfl
private theorem fastLeft (k : Kind) (L : List Bool) :
    run0 (table k) 4 ⟨4,[false,false,false,false,true]++L,P⟩ =
    some (E L 3) := by cases k <;> rfl

theorem fastReturn (b : Bool) (m : Nat) :
    Reaches (fastKind b) (A m) (A (2*m+3)) := by
  cases m with
  | zero => exact ⟨17,by cases b <;> rfl⟩
  | succ n =>
    let k := fastKind b
    have h0 : run0 (table k) 2 (A (n+1)) =
        some ⟨2,[true,true,true],rep P n⟩ := firstTwo k (rep P n)
    have hs := sweepR (table k) 2 [true,true] [] P P (fastCost b) (fastOne b) n [true] []
    have hs' : run0 (table k) (fastCost b*n) ⟨2,[true,true,true],rep P n⟩ =
        some ⟨2,[true,true]++rep P n++[true],[]⟩ := by
      simpa only [List.nil_append,List.append_nil,List.cons_append] using hs
    have h2 := fastEnd b (rep P n++[true])
    have h3 := cZero k (P++rep P n++[true])
    have h4 := bounce k 0 ([false,false]++P++rep P n++[true])
    have h5 := fastLeft k (rep P n++[true])
    have h6 : Reaches k (E (rep P n++[true]) 3) (A (2*(n+1)+3)) := by
      have h := chain k 0 0 n 3
      rw [show 3+(0+2)*n+0+2=2*(n+1)+3 by omega] at h
      exact h
    have h23 : Reaches k ⟨2,[true,true]++rep P n++[true],[]⟩
        (E ([false,false]++P++rep P n++[true]) 0) := by
      exact ⟨_,join0 (by simpa only [List.append_assoc] using h2)
        (by simpa only [List.append_assoc] using h3)⟩
    have h45 : Reaches k (E ([false,false]++P++rep P n++[true]) 0)
        (E (rep P n++[true]) 3) := by
      exact BB6.Agent25Raw43RD1Growth.trans h4 ⟨4,by simpa only [P,rep,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using h5⟩
    exact BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans ⟨2,h0⟩ ⟨_,hs'⟩) h23) h45) h6

private def T : List Bool := [true,false,false,false]
private theorem rcOne (L R : List Bool) :
    run0 (table .rc) 4 ⟨2,[true]++L,[]++(P++P)++R⟩ =
      some ⟨2,[true]++T++L,[]++R⟩ := by rfl
private theorem rcEnd (L : List Bool) :
    run0 (table .rc) 4 ⟨2,[true]++L,P⟩ =
      some ⟨2,[false]++T++L,[]⟩ := by rfl
private theorem rcTurn (L : List Bool) :
    run0 (table .rc) 15 ⟨2,[true,true]++L,[]⟩ =
      some (E ([false,false,false,true,false,false]++L) 0) := by rfl

private theorem tRotate (n : Nat) :
    rep T n++[true] = [true]++rep (block 1) n :=
  (rotate true [false,false,false] n).symm

theorem rcEven (n : Nat) :
    Reaches .rc (A (2*n+2)) (A (3*n+6)) := by
  have h0 : run0 (table .rc) 2 (A (2*n+2)) =
      some ⟨2,[true,true,true],rep P (2*n+1)⟩ := by
    rw [show 2*n+2=(2*n+1)+1 by omega]
    exact firstTwo .rc (rep P (2*n+1))
  have hr : rep P (2*n+1) = rep (P++P) n++P := by
    rw [rep_add,rep_double]; rfl
  rw [hr] at h0
  have hs := sweepR (table .rc) 2 [true] [] (P++P) T 4 rcOne n [true,true] P
  have hs' : run0 (table .rc) (4*n) ⟨2,[true,true,true],rep (P++P) n++P⟩ =
      some ⟨2,[true]++rep T n++[true,true],P⟩ := by
    simpa only [List.nil_append,List.cons_append] using hs
  have h2 := rcEnd (rep T n++[true,true])
  have h3 := cZero .rc ([false,false,false]++rep T n++[true,true])
  have h23 : Reaches .rc ⟨2,[true]++rep T n++[true,true],P⟩
      (E (block 2++rep (block 1) n++ending 0) 0) := by
    have h2' : run0 (table .rc) 4 ⟨2,[true]++rep T n++[true,true],P⟩ =
        some ⟨2,[false,true]++([false,false,false]++rep T n++[true,true]),[]⟩ := by
      simpa only [T,List.append_assoc,List.cons_append,List.nil_append] using h2
    have hh := join0 h2' h3
    have he : [false,false]++([false,false,false]++rep T n++[true,true]) =
        block 2++rep (block 1) n++ending 0 := by
      have h := tRotate n
      have h' := congrArg (fun a => [false,false,false,false,false]++a++[true]) h
      simpa only [block,ending,rep,Z,P,List.append_assoc,List.nil_append,List.cons_append] using h'
    rw [he] at hh
    exact ⟨_,by simpa only [List.append_assoc] using hh⟩
  have h4 := eStep .rc 2 0 (rep (block 1) n++ending 0)
  have h5 := chain .rc 1 0 n 4
  rw [show 4+(1+2)*n+0+2=3*n+6 by omega] at h5
  exact BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans ⟨2,h0⟩ ⟨_,hs'⟩) h23) (by
    simpa only [List.append_assoc] using h4)) h5

theorem rcOdd (n : Nat) :
    Reaches .rc (A (2*n+1)) (A (3*n+6)) := by
  cases n with
  | zero => exact ⟨55,rfl⟩
  | succ n =>
    have h0 : run0 (table .rc) 2 (A (2*(n+1)+1)) =
        some ⟨2,[true,true,true],rep P (2*(n+1))⟩ :=
      firstTwo .rc (rep P (2*(n+1)))
    rw [rep_double] at h0
    have hs := sweepR (table .rc) 2 [true] [] (P++P) T 4 rcOne (n+1) [true,true] []
    have hs' : run0 (table .rc) (4*(n+1)) ⟨2,[true,true,true],rep (P++P) (n+1)⟩ =
        some ⟨2,[true]++rep T (n+1)++[true,true],[]⟩ := by
      simpa only [List.nil_append,List.append_nil,List.cons_append] using hs
    have h2 := rcTurn ([false,false,false]++rep T n++[true,true])
    have h2' : Reaches .rc ⟨2,[true]++rep T (n+1)++[true,true],[]⟩
        (E (block 1++block 2++rep (block 1) n++ending 0) 0) := by
      have he : [false,false,false,true,false,false]++([false,false,false]++rep T n++[true,true]) =
          block 1++block 2++rep (block 1) n++ending 0 := by
        have h := tRotate n
        have h' := congrArg (fun a => [false,false,false,true,false,false,false,false,false]++a++[true]) h
        simpa only [block,ending,rep,Z,P,List.append_assoc,List.nil_append,List.cons_append] using h'
      rw [he] at h2
      exact ⟨15,by simpa only [rep,T,List.append_assoc,List.cons_append,List.nil_append] using h2⟩
    have h3 := eStep .rc 1 0 (block 2++rep (block 1) n++ending 0)
    have h4 := eStep .rc 2 3 (rep (block 1) n++ending 0)
    have h5 := chain .rc 1 0 n 7
    rw [show 7+(1+2)*n+0+2=3*(n+1)+6 by omega] at h5
    exact BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans ⟨2,h0⟩ ⟨_,hs'⟩) h2')
      (by simpa only [List.append_assoc] using h3))
      (by simpa only [List.append_assoc] using h4)) h5

theorem rcReturn (m : Nat) :
    Reaches .rc (A m) (A (3*((m+1)/2)+3)) := by
  by_cases hz : m = 0
  · subst m; exact ⟨17,rfl⟩
  let n := (m-1)/2
  have h : m=2*n+1 ∨ m=2*n+2 := by dsimp [n]; omega
  rcases h with h | h
  · rw [h,show 3*((2*n+1+1)/2)+3=3*n+6 by omega]
    exact rcOdd n
  · rw [h,show 3*((2*n+2+1)/2)+3=3*n+6 by omega]
    exact rcEven n

private def middleKind (b : Bool) : Kind := if b then .re else .rd
private def middleCost (b : Bool) : Nat := if b then 10 else 8
private theorem midIntro (b : Bool) (R : List Bool) :
    run0 (table (middleKind b)) (if b then 7 else 5) ⟨2,[true,true,true],P++R⟩ =
      some ⟨4,[true]++ending 1,[true]++R⟩ := by cases b <;> rfl
private theorem midOne (b : Bool) (L R : List Bool) :
    run0 (table (middleKind b)) (middleCost b) ⟨4,[true]++L,[]++X++R⟩ =
      some ⟨4,[true]++block 1++L,[]++R⟩ := by cases b <;> rfl
private def midTail (odd : Bool) : List Bool := if odd then [true,false,true] else [true]
private theorem midEnd (b odd : Bool) (L : List Bool) :
    run0 (table (middleKind b)) (if odd then middleCost b else 8)
      ⟨4,[true]++L,midTail odd⟩ =
      some (E (block 1++L) 0) := by cases b <;> cases odd <;> rfl

private theorem rightForm (n : Nat) (odd : Bool) :
    [true]++rep P (2*n+(if odd then 1 else 0)) = rep X n++midTail odd := by
  cases odd
  · change [true]++rep P (2*n+0) = rep X n++[true]
    rw [Nat.add_zero]
    have h := rotate true [false] (2*n)
    change [true]++rep P (2*n) = rep Q (2*n)++[true] at h
    rw [rep_double Q n] at h
    exact h
  · change [true]++rep P (2*n+1) = rep X n++[true,false,true]
    have h := rotate true [false] (2*n+1)
    change [true]++rep P (2*n+1) = rep Q (2*n+1)++[true] at h
    rw [rep_add Q (2*n) 1,rep_double Q n] at h
    simpa only [rep,Q,X,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using h

theorem middleLarge (b odd : Bool) (n : Nat) :
    Reaches (middleKind b) (A (2*n+2+(if odd then 1 else 0))) (A (3*n+6)) := by
  let k := middleKind b
  let j := 2*n+(if odd then 1 else 0)
  have h0 : run0 (table k) 2 (A (2*n+2+(if odd then 1 else 0))) =
      some ⟨2,[true,true,true],P++rep P j⟩ := by
    rw [show 2*n+2+(if odd then 1 else 0)=j+1+1 by dsimp [j]; omega]
    exact firstTwo k (rep P (j+1))
  have h1 := midIntro b (rep P j)
  have h1' : run0 (table k) (if b then 7 else 5) ⟨2,[true,true,true],P++rep P j⟩ =
      some ⟨4,[true]++ending 1,rep X n++midTail odd⟩ := by
    simpa only [j,rightForm] using h1
  have hs := sweepR (table k) 4 [true] [] X (block 1) (middleCost b) (midOne b) n (ending 1) (midTail odd)
  have hs' : run0 (table k) (middleCost b*n) ⟨4,[true]++ending 1,rep X n++midTail odd⟩ =
      some ⟨4,[true]++rep (block 1) n++ending 1,midTail odd⟩ := by
    simpa only [List.nil_append,List.cons_append] using hs
  have hf := midEnd b odd (rep (block 1) n++ending 1)
  have hf' : Reaches k ⟨4,[true]++rep (block 1) n++ending 1,midTail odd⟩
      (E (rep (block 1) (n+1)++ending 1) 0) := by
    exact ⟨_,by simpa only [rep,List.append_assoc] using hf⟩
  have hc := chain k 1 1 (n+1) 0
  rw [show 0+(1+2)*(n+1)+1+2=3*n+6 by omega] at hc
  exact BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans (BB6.Agent25Raw43RD1Growth.trans ⟨2,h0⟩ ⟨_,h1'⟩) ⟨_,hs'⟩) hf') hc

theorem middleReturn (b : Bool) (m : Nat) :
    Reaches (middleKind b) (A m) (A (3*(m/2)+3)) := by
  by_cases h0 : m=0
  · subst m; exact ⟨17,by cases b <;> rfl⟩
  by_cases h1 : m=1
  · subst m; exact ⟨if b then 19 else 17,by cases b <;> rfl⟩
  let n := (m-2)/2
  have h : m=2*n+2 ∨ m=2*n+3 := by dsimp [n]; omega
  rcases h with h | h
  · rw [h,show 3*((2*n+2)/2)+3=3*n+6 by omega]
    exact middleLarge b false n
  · rw [h,show 3*((2*n+3)/2)+3=3*n+6 by omega]
    exact middleLarge b true n

def next (k : Kind) (m : Nat) : Nat :=
  match k with
  | .rb => 2*m+3
  | .le => 2*m+3
  | .rc => 3*((m+1)/2)+3
  | .rd => 3*(m/2)+3
  | .re => 3*(m/2)+3

theorem returns (k : Kind) (m : Nat) : Reaches k (A m) (A (next k m)) := by
  cases k with
  | rb => exact fastReturn false m
  | le => exact fastReturn true m
  | rc => exact rcReturn m
  | rd => exact middleReturn false m
  | re => exact middleReturn true m

theorem positiveEpoch (k : Kind) (m : Nat) :
    ∃ n, 0<n ∧ run0 (table k) n (A m) = some (A (next k m)) := by
  obtain ⟨n,h⟩ := returns k m
  refine ⟨n, ?_, h⟩
  by_cases hn : n=0
  · subst n
    have hh : A m = A (next k m) := Option.some.inj h
    have hl := congrArg (fun a : Z0 => a.r.length) hh
    have ht : 2*m = 2*next k m := by simpa [A,rep_length,P] using hl
    cases k <;> simp [next] at ht <;> omega
  · omega

def orbit (k : Kind) : Nat → Nat
  | 0 => 0
  | n+1 => next k (orbit k n)
def family (k : Kind) (n : Nat) : Z0 := A (orbit k n)
noncomputable def cost (k : Kind) (n : Nat) : Nat :=
  Classical.choose (positiveEpoch k (orbit k n))
theorem never (k : Kind) (m : Machine) (hm : compatible (table k) m) : NeverHalts m :=
  never_of_growth (table k) (family k) 0 (cost k) (by rfl)
    (fun n => (Classical.choose_spec (positiveEpoch k (orbit k n))).1)
    (fun n => (Classical.choose_spec (positiveEpoch k (orbit k n))).2) m hm

#print axioms returns
#print axioms never
end BB6.Agent25Raw43RD1Return
