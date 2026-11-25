import Raw13Detour

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Frames
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent46Raw13Detour (base blank0 live)

def P : List Bool := [false,true,false,true,true]
def pair (b : Bool) : List Bool := [true,b]
def pairs : List Bool → List Bool
  | [] => []
  | b::w => pair b ++ pairs w

def A (L W : List Bool) : Z0 := ⟨0,L,P++pairs W⟩
def E (b : Bool) (X W : List Bool) : Z0 := ⟨4,b::true::true::X,pairs W⟩
def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false

def scan : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::W => (0,W)
  | [true] => (3,[])
  | [true,_] => (3,[])
  | true::_::_::W => let s := scan W; (6+s.1,s.2)

theorem pairs_append (a b : List Bool) : pairs (a++b) = pairs a++pairs b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [pairs,ih,List.append_assoc]

theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m := by
  induction n with
  | zero => simp [ones]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [ones,List.replicate_succ,List.cons_append] at ih ⊢; rw [ih]
theorem zeros_add (n m : Nat) : zeros (n+m) = zeros n ++ zeros m := by
  induction n with
  | zero => simp [zeros]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [zeros,List.replicate_succ,List.cons_append] at ih ⊢; rw [ih]

theorem rep_ones (n : Nat) : rep [true,true,true,true] n = ones (4*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 4*(n+1)=4+4*n by omega,ones_add]; rfl

theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih]; rfl

theorem e_false (b : Bool) (X W : List Bool) :
    run0 base 9 (E b X (false::W)) = some (A X W) := by cases b <;> rfl

theorem e_empty (b : Bool) (X : List Bool) :
    run0 base 13 (E b X []) = some (A X []) := by cases b <;> rfl

theorem e_single (b : Bool) (X : List Bool) :
    run0 base 18 (E b X [true]) = some (A (ones 3++X) []) := by cases b <;> rfl

theorem e_double (b c : Bool) (X : List Bool) :
    run0 base (if c then 14 else 18) (E b X [true,c]) = some (A (ones 3++X) []) := by cases b <;> cases c <;> rfl

theorem e_triple (b c d : Bool) (X W : List Bool) :
    run0 base (if c then 10 else 14) (E b X (true::c::d::W)) = some (E d (ones 6++X) W) := by cases b <;> cases c <;> cases d <;> rfl

theorem e_scan (W : List Bool) (b : Bool) (X : List Bool) :
    ∃ cost, 0<cost ∧ run0 base cost (E b X W) = some (A (ones (scan W).1 ++ X) (scan W).2) := by
  match W with
  | [] => exact ⟨13,by decide,e_empty b X⟩
  | false::W => exact ⟨9,by decide,e_false b X W⟩
  | [true] => exact ⟨18,by decide,e_single b X⟩
  | [true,c] => exact ⟨if c then 14 else 18,by cases c <;> decide,e_double b c X⟩
  | true::c::d::W =>
    obtain ⟨k,hk,hr⟩ := e_scan W d (ones 6++X)
    refine ⟨(if c then 10 else 14)+k,by omega,?_⟩
    have h := join0 (e_triple b c d X W) hr
    simpa only [scan,ones_add,Nat.add_comm 6 (scan W).1,List.append_assoc] using h

termination_by W.length

theorem a11 (L R : List Bool) :
    run0 base 2 ⟨0,[]++[true,true]++L,[]++R⟩ = some ⟨0,[]++L,[]++[false,true]++R⟩ := rfl

theorem a1000 (L R : List Bool) :
    run0 base 4 ⟨0,[]++[true,false,false,false]++L,[]++R⟩ = some ⟨0,[]++L,[]++[true,true,true,true]++R⟩ := rfl

theorem a1001 (L R : List Bool) :
    run0 base 6 ⟨0,true::false::false::true::L,R⟩ = some ⟨0,false::true::L,false::true::R⟩ := rfl

theorem b_one (L R : List Bool) :
    run0 base 1 ⟨1,[true]++L,[]++[true]++R⟩ = some ⟨1,[true]++[false]++L,[]++R⟩ := rfl

theorem a0_back (n : Nat) (L W : List Bool) (c : Bool) :
    run0 base (n+3) ⟨0,false::L,ones n ++ [false,true,c] ++ pairs W⟩ =
      some (E c (zeros n++true::L) W) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h1 : run0 base 1 ⟨0,false::L,ones (n+1) ++ [false,true,c] ++ pairs W⟩ =
        some ⟨1,true::true::L,ones n ++ [false,true,c] ++ pairs W⟩ := rfl
    have h2 := sweepR base 1 [true] [] [true] [false] 1 b_one n (true::L) ([false,true,c]++pairs W)
    have h2' : run0 base n ⟨1,true::true::L,ones n ++ [false,true,c] ++ pairs W⟩ =
        some ⟨1,true::(zeros n++true::L),[false,true,c]++pairs W⟩ := by
      simpa only [rep_single,ones,zeros,Nat.one_mul,List.nil_append,List.cons_append,List.singleton_append,List.append_assoc] using h2
    have h3 : run0 base 3 ⟨1,true::(zeros n++true::L),[false,true,c]++pairs W⟩ =
        some (E c (zeros (n+1)++true::L) W) := rfl
    have h := join0 (join0 h1 h2') h3
    simpa only [show 1+n+3=n+1+3 by omega] using h

theorem align (k : Nat) : rep [false,true] k ++ P = [false,true,false] ++ pairs (zeros k++[true]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rep,List.append_assoc,ih]
    rfl

theorem mixed_tail (k : Nat) : [true] ++ rep [false,true] k ++ P = pairs (zeros (k+2)++[true]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show k+1+2=k+2+1 by omega]
    change true::false::([true] ++ rep [false,true] k ++ P) = true::false::pairs (zeros (k+2)++[true])
    rw [ih]

theorem mixed_prefix (n : Nat) : [false,true] ++ rep [true,true,true,true] (n+1) =
    [false,true,true] ++ pairs (ones (2*n+1)) ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)+1=2+(2*n+1) by omega,ones_add,pairs_append]
    have h := congrArg (fun l => false::true::true::true::true::true::l) (List.cons.inj (List.cons.inj ih).2).2
    exact h

theorem mixed_align (n k : Nat) :
    [false,true] ++ rep [true,true,true,true] (n+1) ++ rep [false,true] k ++ P =
      [false,true,true] ++ pairs (ones (2*n+1)++zeros (k+2)++[true]) := by
  rw [mixed_prefix]
  simp only [List.append_assoc,pairs_append]
  have h := mixed_tail k
  simp only [List.append_assoc,pairs_append] at h
  rw [h]

def Path0 (x y : Z0) : Prop := ∃ k, 0<k ∧ run0 base k x = some y

theorem pathJoin {a b c : Z0} (h : Path0 a b) (g : Path0 b c) : Path0 a c := by
  obtain ⟨k,hk,hr⟩ := h
  obtain ⟨j,hj,hs⟩ := g
  exact ⟨k+j,by omega,join0 hr hs⟩

theorem pairsOne (k : Nat) : rep [true,true] k = ones (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 2*(k+1)=2+2*k by omega,ones_add];rfl

theorem preRun (k n : Nat) (L W : List Bool) :
    run0 base (2*k+4*n) (A (ones (2*k)++rep [true,false,false,false] n++L) W) =
      some ⟨0,L,rep [true,true,true,true] n++rep [false,true] k++P++pairs W⟩ := by
  have h1 := sweepL base 0 [] [] [true,true] [false,true] 2 a11 k (rep [true,false,false,false] n++L) (P++pairs W)
  have h2 := sweepL base 0 [] [] [true,false,false,false] [true,true,true,true] 4 a1000 n L (rep [false,true] k++P++pairs W)
  have h1' : run0 base (2*k) (A (ones (2*k)++rep [true,false,false,false] n++L) W) =
      some ⟨0,rep [true,false,false,false] n++L,rep [false,true] k++P++pairs W⟩ := by
    simpa only [A,pairsOne,List.nil_append,List.append_assoc] using h1
  have h2' : run0 base (4*n) ⟨0,rep [true,false,false,false] n++L,rep [false,true] k++P++pairs W⟩ =
      some ⟨0,L,rep [true,true,true,true] n++rep [false,true] k++P++pairs W⟩ := by
    simpa only [List.nil_append,List.append_assoc] using h2
  exact join0 h1' h2'

theorem main (k n : Nat) (L W : List Bool) :
    Path0 (A (ones (2*k)++rep [true,false,false,false] n++false::L) W)
      (A (ones (scan (zeros k++true::W)).1++zeros (4*n)++true::L) (scan (zeros k++true::W)).2) := by
  have h1 := preRun k n (false::L) W
  have h2 := a0_back (4*n) L (zeros k++true::W) false
  have align' : rep [true,true,true,true] n++rep [false,true] k++P++pairs W =
      ones (4*n) ++ [false,true,false] ++ pairs (zeros k++true::W) := by
    rw [rep_ones]
    have ha := congrArg (fun x => ones (4*n) ++ x ++ pairs W) (align k)
    simpa only [List.append_assoc,pairs_append,pairs,pair,List.nil_append] using ha
  rw [align'] at h1
  obtain ⟨c,hc,h3⟩ := e_scan (zeros k++true::W) false (zeros (4*n)++true::L)
  refine ⟨2*k+4*n+(4*n+3)+c,by omega,?_⟩
  simpa only [List.append_assoc] using join0 (join0 h1 h2) h3

theorem main_pos (k n : Nat) (L W : List Bool) :
    Path0 (A (ones (2*(k+1))++rep [true,false,false,false] n++false::L) W)
      (A (zeros (4*n)++true::L) (zeros k++true::W)) := by
  simpa only [zeros,List.replicate_succ, List.cons_append,scan,ones,List.replicate_zero,List.nil_append] using main (k+1) n L W

theorem mixed11 (k n : Nat) (L W : List Bool) :
    Path0 (A (ones (2*k)++rep [true,false,false,false] (n+1)++true::true::false::L) W)
      (A (ones (scan (ones (2*n+1)++zeros (k+2)++true::W)).1++true::L)
        (scan (ones (2*n+1)++zeros (k+2)++true::W)).2) := by
  have h1 := preRun k (n+1) (true::true::false::L) W
  have h2 := a11 (false::L) (rep [true,true,true,true] (n+1)++rep [false,true] k++P++pairs W)
  have h12 := join0 h1 (by simpa only [List.nil_append,List.cons_append,List.append_assoc] using h2)
  have hr : [false,true]++rep [true,true,true,true] (n+1)++rep [false,true] k++P++pairs W =
      [false,true,true]++pairs (ones (2*n+1)++zeros (k+2)++true::W) := by
    rw [mixed_align]
    simp only [pairs_append,List.append_assoc]
    rfl
  have h12' : run0 base (2*k+4*(n+1)+2) (A (ones (2*k)++rep [true,false,false,false] (n+1)++true::true::false::L) W) =
      some ⟨0,false::L,[false,true,true]++pairs (ones (2*n+1)++zeros (k+2)++true::W)⟩ := by
    have hr' : false::true::(rep [true,true,true,true] (n+1)++rep [false,true] k++P++pairs W) = [false,true,true]++pairs (ones (2*n+1)++zeros (k+2)++true::W) := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using hr
    rw [← hr']
    simpa only [List.append_assoc] using h12
  have h3 := a0_back 0 L (ones (2*n+1)++zeros (k+2)++true::W) true
  obtain ⟨c,hc,h4⟩ := e_scan (ones (2*n+1)++zeros (k+2)++true::W) true (true::L)
  refine ⟨2*k+4*(n+1)+2+3+c,by omega,?_⟩
  exact join0 (join0 h12' h3) h4

theorem special (k n : Nat) (L W : List Bool) :
    Path0 (A (ones (2*k)++rep [true,false,false,false] (n+1)++true::false::false::true::L) W)
      (A (ones (scan (ones (2*n+1)++zeros (k+2)++true::W)).1++true::true::L)
        (scan (ones (2*n+1)++zeros (k+2)++true::W)).2) := by
  have h1 := preRun k (n+1) (true::false::false::true::L) W
  have h2 := a1001 L (rep [true,true,true,true] (n+1)++rep [false,true] k++P++pairs W)
  have h12 := join0 h1 h2
  have hr : [false,true]++rep [true,true,true,true] (n+1)++rep [false,true] k++P++pairs W =
      [false,true,true]++pairs (ones (2*n+1)++zeros (k+2)++true::W) := by
    rw [mixed_align]
    simp only [pairs_append,List.append_assoc]
    rfl
  have h12' : run0 base (2*k+4*(n+1)+6) (A (ones (2*k)++rep [true,false,false,false] (n+1)++true::false::false::true::L) W) =
      some ⟨0,false::true::L,[false,true,true]++pairs (ones (2*n+1)++zeros (k+2)++true::W)⟩ := by
    have hr' : false::true::(rep [true,true,true,true] (n+1)++rep [false,true] k++P++pairs W) = [false,true,true]++pairs (ones (2*n+1)++zeros (k+2)++true::W) := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using hr
    rw [← hr']
    simpa only [List.append_assoc] using h12
  have h3 := a0_back 0 (true::L) (ones (2*n+1)++zeros (k+2)++true::W) true
  obtain ⟨c,hc,h4⟩ := e_scan (ones (2*n+1)++zeros (k+2)++true::W) true (true::true::L)
  exact ⟨2*k+4*(n+1)+6+3+c,by omega,join0 (join0 h12' h3) h4⟩

theorem special0 (k : Nat) (L W : List Bool) :
    Path0 (A (ones (2*k)++true::false::false::true::L) W)
      (A (true::true::L) (zeros k++true::W)) := by
  have h1 := preRun k 0 (true::false::false::true::L) W
  have h2 := a1001 L (rep [true,true,true,true] 0++rep [false,true] k++P++pairs W)
  have h12 := join0 h1 h2
  have hr : [false,true]++rep [false,true] k++P++pairs W =
      [false,true,false]++pairs (zeros (k+1)++true::W) := by
    have h := congrArg (fun x => x ++ pairs W) (align (k+1))
    simpa only [rep,List.append_assoc,pairs_append,pairs,pair,List.nil_append] using h
  have h12' : run0 base (2*k+6) (A (ones (2*k)++true::false::false::true::L) W) =
      some ⟨0,false::true::L,[false,true,false]++pairs (zeros (k+1)++true::W)⟩ := by
    have hr' : false::true::(rep [false,true] k++P++pairs W) = [false,true,false]++pairs (zeros (k+1)++true::W) := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using hr
    rw [← hr']
    simpa only [rep,List.nil_append,List.append_nil,List.cons_append,List.append_assoc,Nat.mul_zero,Nat.add_zero] using h12
  have h3 := a0_back 0 (true::L) (zeros (k+1)++true::W) false
  have h4 := e_false false (true::true::L) (zeros k++true::W)
  exact ⟨2*k+6+3+9,by omega,join0 (join0 h12' h3) h4⟩

#print axioms e_scan
#print axioms main
#print axioms mixed11
#print axioms special
#print axioms special0
end BB6.Agent46Raw13Frames
