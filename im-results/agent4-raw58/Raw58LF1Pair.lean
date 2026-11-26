import Raw58Live
namespace BB6Coverage.Agent4LF1Pair
open BB6Coverage Agent31Pump

def table (v : Bool) : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,5⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => none
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => if v then some (some ⟨true,true,0⟩) else some (some ⟨false,false,5⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨true,true,2⟩)
  | (4,true) => some (some ⟨false,true,0⟩)
  | (5,false) => some (some ⟨true,false,2⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

abbrev P : List Bool := [true,true,false]
abbrev T : List Bool := [true,false]
abbrev Q : List Bool := P ++ T
abbrev U : List Bool := [true,false,false]
abbrev V : List Bool := T ++ U
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
def X (n : Nat) (S : List Bool) := C [] (rep U n ++ [true,true] ++ S)
def St (k n : Nat) := rep P k ++ Q ++ rep P n

theorem scan (v : Bool) (n : Nat) (R : List Bool) (hn : 0 < n) :
    run0 (table v) (3*n) (C [] (rep U n ++ R)) = some (C (false::rep P n) R) := by
  have h := sweepR (table v) 2 [false] [] U P 3 (by intro L R; cases v <;> rfl) n [] R
  simp only [List.nil_append,List.append_nil,List.singleton_append] at h
  have eq : 3*n = (3*n-1)+1 := by omega
  rw [eq] at h ⊢
  exact h

theorem pushQ (v b : Bool) (L S : List Bool) :
    run0 (table v) 5 (C (false::L) ([true,true,false,false,b]++S)) = some (C (b::(Q++L)) S) := by cases v <;> rfl

theorem pushQEnd (v : Bool) (L : List Bool) :
    run0 (table v) 5 (C (false::L) [true,true]) = some (C (false::(Q++L)) []) := by cases v <;> rfl

theorem pushU (v b : Bool) (L S : List Bool) :
    run0 (table v) 3 (C (false::L) ([true,false,b]++S)) = some (C (b::(P++L)) S) := by cases v <;> rfl

theorem pushUEnd (v : Bool) (L : List Bool) :
    run0 (table v) 3 (C (false::L) [true]) = some (C (false::(P++L)) []) := by cases v <;> rfl

theorem turn (v : Bool) (k n : Nat) (S : List Bool) :
    run0 (table v) 7 (C (false::St k n) (false::S)) = some (C (St k n) ([true,true]++S)) := by cases k <;> cases v <;> rfl

theorem turnEnd (v : Bool) (k n : Nat) :
    run0 (table v) 7 (C (false::St k n) []) = some (C (St k n) [true,true]) := by cases k <;> cases v <;> rfl

theorem turnP (v : Bool) (n : Nat) (S : List Bool) (hn : 0<n) :
    run0 (table v) 7 (C (false::rep P n) (false::S)) = some (C (rep P n) ([true,true]++S)) := by cases n with
    | zero => omega
    | succ n => cases v <;> rfl

theorem bp (v : Bool) (L R : List Bool) (hr : v=true → R.headD false=true) :
    run0 (table v) (if v then 5 else 3) (C (P++L) R) = some (C L (U++R)) := by
  cases v with
  | false => rfl
  | true => cases R with
    | nil => simp at hr
    | cons b R => cases b with
      | false => simp at hr
      | true => rfl

theorem bt (v : Bool) (L R : List Bool) (hr : v=true → R.headD false=true) :
    run0 (table v) (if v then 4 else 2) (C (T++L) R) = some (C L (T++R)) := by
  cases v with
  | false => rfl
  | true => cases R with
    | nil => simp at hr
    | cons b R => cases b with
      | false => simp at hr
      | true => rfl

theorem backP (v : Bool) (n : Nat) (L R : List Bool) (hr : v=true → R.headD false=true) :
    run0 (table v) ((if v then 5 else 3)*n) (C (rep P n++L) R) = some (C L (rep U n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h := join0 (bp v (rep P n++L) R hr) (ih (U++R) (by intro; rfl))
    rw [Nat.mul_succ,Nat.add_comm]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep U n) U R,rep_snoc U n] using h

theorem backStack (v : Bool) (k n : Nat) (R : List Bool) (hr : v=true → R.headD false=true) :
    ∃ t, run0 (table v) t (C (St k n) R) = some (C [] (rep U n++V++rep U k++R)) := by
  have a := backP v k (Q++rep P n) R hr
  have b := bp v (T++rep P n) (rep U k++R) (by cases k <;> simpa [rep] using hr)
  have c := bt v (rep P n) (U++rep U k++R) (by intro; rfl)
  have d := backP v n [] (V++rep U k++R) (by intro; rfl)
  simp only [List.append_nil] at d
  have h := join0 (join0 (join0 a b) c) d
  exact ⟨_,by simpa only [St,Q,V,List.append_nil,List.append_assoc] using h⟩

theorem pushSt (k n : Nat) : P++St k n = St (k+1) n := by simp only [St,rep,List.append_assoc]

def word : List (Bool × Bool) → List Bool
  | [] => []
  | (a,b)::ds => [a,false,b]++word ds

def Good (S : List Bool) : Prop := ∃ b ds, [false,false]++S = [false,false,b]++word ds++[true]

theorem padGood (k : Nat) (S : List Bool) (h : Good S) : Good (rep U k++S) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨b,ds,he⟩ := ih
    refine ⟨true,(false,b)::ds,?_⟩
    change [false,false,true]++([false,false]++(rep U k++S)) = _
    rw [he]
    rfl

theorem extra (L R : List Bool) :
    run0 (table false) 4 (C (true::(P++L)) R) = some (C L (U++false::R)) := by rfl

theorem tail1375 (ds : List (Bool × Bool)) (k n : Nat) :
    ∃ t S, Good S ∧ run0 (table false) t (C (false::St k n) (word ds++[true])) = some (C [] (rep U n++V++S)) := by
  induction ds generalizing k with
  | nil =>
    have a := pushUEnd false (St k n)
    rw [pushSt] at a
    have b := turnEnd false (k+1) n
    obtain ⟨t,c⟩ := backStack false (k+1) n [true,true] (by simp)
    exact ⟨_,_,padGood (k+1) [true,true] ⟨true,[],rfl⟩,by simpa only [word,List.nil_append,List.append_assoc] using join0 (join0 a b) c⟩
  | cons d ds ih =>
    rcases d with ⟨a,b⟩
    cases a with
    | false =>
      have a := turn false k n ([false,b]++word ds++[true])
      obtain ⟨t,c⟩ := backStack false k n ([true,true,false,b]++word ds++[true]) (by simp)
      exact ⟨_,rep U k++([true,true,false,b]++word ds++[true]),padGood k _ ⟨true,(true,b)::ds,by simp only [word,List.append_assoc];rfl⟩,by simpa only [word,List.append_assoc,List.cons_append,List.nil_append] using join0 a c⟩
    | true =>
      cases b with
      | false =>
        have a := pushU false false (St k n) (word ds++[true])
        rw [pushSt] at a
        obtain ⟨t,S,h,c⟩ := ih (k+1)
        exact ⟨_,S,h,by simpa only [word,List.append_assoc,List.cons_append,List.nil_append] using join0 a c⟩
      | true =>
        have a := pushU false true (St k n) (word ds++[true])
        have b := extra (St k n) (word ds++[true])
        obtain ⟨t,c⟩ := backStack false k n (U++false::(word ds++[true])) (by simp)
        have hg : Good (rep U (k+1)++false::(word ds++[true])) := padGood (k+1) _ ⟨false,ds,rfl⟩
        have he : rep U k++(U++false::(word ds++[true])) = rep U (k+1)++false::(word ds++[true]) := by rw [← List.append_assoc,rep_snoc]; rfl
        rw [← he] at hg
        exact ⟨_,_,hg,by simpa only [word,List.append_assoc] using join0 (join0 a b) c⟩

def Valid (S : List Bool) : Prop := S=[] ∨ ∃ b ds, S=[false,false,b]++word ds++[true]

theorem phase1375 (n : Nat) (S : List Bool) (hn : 0<n) (hv : Valid S) :
    ∃ t S', Good S' ∧ run0 (table false) t (X n S) = some (C [] (rep U n++V++S')) := by
  have a := scan false n ([true,true]++S) hn
  rcases hv with rfl | ⟨b,ds,rfl⟩
  · have b := pushQEnd false (rep P n)
    have c := turnEnd false 0 n
    obtain ⟨t,d⟩ := backStack false 0 n [true,true] (by simp)
    exact ⟨_,[true,true],⟨true,[],rfl⟩,by simpa only [X,St,rep,List.nil_append,List.append_nil,List.append_assoc] using join0 (join0 (join0 a b) c) d⟩
  · cases b with
    | false =>
      have b := pushQ false false (rep P n) (word ds++[true])
      obtain ⟨t,S,h,c⟩ := tail1375 ds 0 n
      exact ⟨_,S,h,by simpa only [X,St,rep,List.nil_append,List.append_assoc] using join0 (join0 a b) c⟩
    | true =>
      have b := pushQ false true (rep P n) (word ds++[true])
      have c := extra (T++rep P n) (word ds++[true])
      have d := bt false (rep P n) (U++false::(word ds++[true])) (by simp)
      have e := backP false n [] (V++false::(word ds++[true])) (by simp)
      simp only [List.append_nil] at e
      exact ⟨_,false::(word ds++[true]),⟨false,ds,rfl⟩,by simpa only [X,Q,V,List.append_assoc] using join0 (join0 (join0 (join0 a b) c) d) e⟩

theorem phaseB1375 (n : Nat) (S : List Bool) (hn : 0<n) :
    ∃ t, run0 (table false) t (C [] (rep U n++V++S)) = some (C [] (rep U (n+1)++[false,false,false]++S)) := by
  have a := scan false n (V++S) hn
  have b := pushU false true (rep P n) ([false,false]++S)
  have c := extra (rep P n) ([false,false]++S)
  have d := backP false n [] (U++[false,false,false]++S) (by simp)
  simp only [List.append_nil] at d
  have h := join0 (join0 (join0 a b) c) d
  exact ⟨_,by simpa only [List.append_assoc,← List.append_assoc (rep U n) U ([false,false,false]++S),rep_snoc U n,rep] using h⟩

theorem phaseC (v : Bool) (n : Nat) (S : List Bool) (hn : 0<n) :
    ∃ t, run0 (table v) t (C [] (rep U n++false::S)) = some (X n S) := by
  have a := scan v n (false::S) hn
  have b := turnP v n S hn
  have c := backP v n [] ([true,true]++S) (by intro; rfl)
  simp only [List.append_nil] at c
  exact ⟨_,by simpa only [X,List.append_assoc] using join0 (join0 a b) c⟩

theorem grow1375 (n : Nat) (S : List Bool) (hn : 0<n) (hv : Valid S) :
    ∃ t S', 0<t ∧ Valid S' ∧ run0 (table false) t (X n S) = some (X (n+1) S') := by
  obtain ⟨a,S',hg,ha⟩ := phase1375 n S hn hv
  obtain ⟨b,hb⟩ := phaseB1375 n S' hn
  obtain ⟨c,hc⟩ := phaseC false (n+1) ([false,false]++S') (by omega)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at ha hb hc
  have h := join0 (join0 ha hb) hc
  refine ⟨a+b+c,_,?_,Or.inr hg,h⟩
  by_cases e : a=0
  · subst a
    simp only [run0] at ha
    have hr := congrArg Z0.r (Option.some.inj ha)
    simp only [X,C,List.append_assoc] at hr
    have he := List.append_cancel_left hr
    simp [V,T,U] at he
  · omega

theorem arbitrary1375 : ∀ n : Nat, ∃ t z, n ≤ t ∧ run0 (table false) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ n : Nat, ∃ t S, n≤t ∧ Valid S ∧ run0 (table false) t ⟨0,[],[]⟩ = some (X (n+1) S) := by
    intro n
    induction n with
    | zero => exact ⟨12,[],by omega,Or.inl rfl,by rfl⟩
    | succ n ih =>
      obtain ⟨t,S,ht,hv,hr⟩ := ih
      obtain ⟨u,S',hu,hv',hr'⟩ := grow1375 (n+1) S (by omega) hv
      exact ⟨t+u,S',by omega,hv',join0 hr hr'⟩
  intro n
  obtain ⟨t,S,ht,_,hr⟩ := h n
  exact ⟨t,_,ht,hr⟩

def wordB : List Bool → List Bool
  | [] => []
  | a::ds => [a,false,false]++wordB ds

def ValidB (S : List Bool) : Prop := S=[] ∨ ∃ ds, S=[false,false,false]++wordB ds++[true]
def TailB (S : List Bool) : Prop := S=[] ∨ ∃ ds, S=[false,false]++wordB ds++[true]

theorem tail1416 (ds : List Bool) (k n : Nat) :
    ∃ t j S, TailB S ∧ run0 (table true) t (C (false::St k n) (wordB ds++[true])) = some (C [] (rep U n++V++rep U j++[true,true]++S)) := by
  induction ds generalizing k with
  | nil =>
    have a := pushUEnd true (St k n)
    rw [pushSt] at a
    have b := turnEnd true (k+1) n
    obtain ⟨t,c⟩ := backStack true (k+1) n [true,true] (by intro; rfl)
    exact ⟨_,k+1,[],Or.inl rfl,by simpa only [wordB,List.nil_append,List.append_nil,List.append_assoc] using join0 (join0 a b) c⟩
  | cons a ds ih =>
    cases a with
    | false =>
      have a := turn true k n ([false,false]++wordB ds++[true])
      obtain ⟨t,c⟩ := backStack true k n ([true,true,false,false]++wordB ds++[true]) (by intro; rfl)
      exact ⟨_,k,_,Or.inr ⟨ds,rfl⟩,by simpa only [wordB,List.append_assoc,List.cons_append,List.nil_append] using join0 a c⟩
    | true =>
      have a := pushU true false (St k n) (wordB ds++[true])
      rw [pushSt] at a
      obtain ⟨t,j,S,h,c⟩ := ih (k+1)
      exact ⟨_,j,S,h,by simpa only [wordB,List.append_assoc] using join0 a c⟩

theorem phase1416 (n : Nat) (S : List Bool) (hn : 0<n) (hv : ValidB S) :
    ∃ t j S', TailB S' ∧ run0 (table true) t (X n S) = some (C [] (rep U n++V++rep U j++[true,true]++S')) := by
  have a := scan true n ([true,true]++S) hn
  rcases hv with rfl | ⟨ds,rfl⟩
  · have b := pushQEnd true (rep P n)
    have c := turnEnd true 0 n
    obtain ⟨t,d⟩ := backStack true 0 n [true,true] (by intro; rfl)
    exact ⟨_,0,[],Or.inl rfl,by simpa only [X,St,rep,List.nil_append,List.append_nil,List.append_assoc] using join0 (join0 (join0 a b) c) d⟩
  · have b := pushQ true false (rep P n) (wordB ds++[true])
    obtain ⟨t,j,S,h,c⟩ := tail1416 ds 0 n
    exact ⟨_,j,S,h,by simpa only [X,St,rep,List.nil_append,List.append_assoc] using join0 (join0 a b) c⟩

abbrev J : List Bool := [true,true,true]
abbrev Z : List Bool := [false,false,false]
abbrev N : List Bool := [false,false,true]

theorem shift00 (k : Nat) : [false,false]++rep U k = rep N k++[false,false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change N++([false,false]++rep U k) = _
    rw [ih]
    rfl

theorem shift0 (k : Nat) : rep Z k++[false] = false::rep Z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc,ih]
    rfl

theorem sweep1416 (n k : Nat) (S : List Bool) :
    run0 (table true) (3*(k+1)) (C (true::(P++rep P n)) ([false,false]++rep U k++[true,true]++S)) =
      some (C (true::(rep J (k+1)++P++rep P n)) (true::S)) := by
  have a := sweepR (table true) 2 [true] [] N J 3 (by intro L R; rfl) (k+1) (P++rep P n) (true::S)
  have eq : [false,false]++rep U k++[true,true]++S = rep N (k+1)++true::S := by
    rw [shift00 k]
    simp only [List.append_assoc]
    change rep N k++(N++true::S) = _
    rw [← List.append_assoc,rep_snoc N k]
    rfl
  rw [eq]
  simpa only [List.singleton_append,List.nil_append,List.append_assoc,List.cons_append] using a

theorem return1416 (n k : Nat) (S : List Bool) :
    ∃ t, run0 (table true) t (C (true::(rep J (k+1)++P++rep P n)) (true::S)) =
      some (C (rep P n) (U++rep Z (k+1)++false::true::S)) := by
  have a : run0 (table true) 3 (C (true::(rep J (k+1)++P++rep P n)) (true::S)) =
      some (⟨5,rep J (k+1)++P++rep P n,false::true::S⟩ : Z0) := by rfl
  have b := sweepL (table true) 5 [] [] J Z 3 (by intro L R; rfl) (k+1) (P++rep P n) (false::true::S)
  simp only [List.nil_append] at b
  have c : run0 (table true) 3 (⟨5,P++rep P n,rep Z (k+1)++false::true::S⟩ : Z0) =
      some (C (rep P n) (U++(rep Z (k+1)++false::true::S))) := by rfl
  simp only [List.append_assoc] at a b c
  exact ⟨_,by simpa only [List.append_assoc] using join0 (join0 a b) c⟩

theorem phaseB1416 (n k : Nat) (S : List Bool) (hn : 0<n) :
    ∃ t, run0 (table true) t (C [] (rep U n++V++rep U k++[true,true]++S)) =
      some (C [] (rep U (n+1)++false::(rep Z (k+1)++true::S))) := by
  have a := scan true n (V++rep U k++[true,true]++S) hn
  have b := pushU true true (rep P n) ([false,false]++rep U k++[true,true]++S)
  have c := sweep1416 n k S
  obtain ⟨t,d⟩ := return1416 n k S
  have e := backP true n [] (U++rep Z (k+1)++false::true::S) (by intro; rfl)
  simp only [List.append_nil,List.append_assoc] at e
  simp only [List.append_assoc,List.cons_append,List.nil_append] at a b c d e
  have h := join0 (join0 (join0 (join0 a b) c) d) e
  have eq : rep U n++(U++(rep Z (k+1)++false::true::S)) = rep U (n+1)++false::(rep Z (k+1)++true::S) := by
    have f : rep Z (k+1)++false::true::S = false::(rep Z (k+1)++true::S) := calc
      _ = (rep Z (k+1)++[false])++true::S := by rw [List.append_assoc]; rfl
      _ = _ := by rw [shift0]; rfl
    rw [f,← List.append_assoc,rep_snoc U n]
    rfl
  have hh : run0 (table true) (3*n+3+3*(k+1)+t+5*n) (C [] (rep U n++V++rep U k++[true,true]++S)) = some (C [] (rep U n++(U++(rep Z (k+1)++false::true::S)))) := by
    simpa only [if_pos True.intro,List.append_assoc,List.cons_append,List.nil_append] using h
  rw [eq] at hh
  exact ⟨_,hh⟩

theorem prependZeroB (k : Nat) (ds : List Bool) : rep Z k++wordB ds = wordB (List.replicate k false++ds) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.replicate_succ,List.cons_append,wordB,List.append_assoc,ih]

theorem validReturnB (k : Nat) (S : List Bool) (h : TailB S) : ValidB (rep Z (k+1)++true::S) := by
  right
  rcases h with rfl | ⟨ds,rfl⟩
  · refine ⟨List.replicate k false,?_⟩
    have h := prependZeroB k []
    simp only [List.append_nil,wordB] at h
    simp only [rep,List.append_assoc,h]
  · refine ⟨List.replicate k false++true::ds,?_⟩
    have h := prependZeroB k (true::ds)
    simp only [wordB,List.append_assoc] at h
    simp only [rep,List.append_assoc,← h,List.cons_append,List.nil_append]

theorem grow1416 (n : Nat) (S : List Bool) (hn : 0<n) (hv : ValidB S) :
    ∃ t S', 0<t ∧ ValidB S' ∧ run0 (table true) t (X n S) = some (X (n+1) S') := by
  obtain ⟨a,k,S',hg,ha⟩ := phase1416 n S hn hv
  obtain ⟨b,hb⟩ := phaseB1416 n k S' hn
  obtain ⟨c,hc⟩ := phaseC true (n+1) (rep Z (k+1)++true::S') (by omega)
  have h := join0 (join0 ha hb) hc
  refine ⟨a+b+c,_,?_,validReturnB k S' hg,h⟩
  by_cases e : a=0
  · subst a
    simp only [run0] at ha
    have hr := congrArg Z0.r (Option.some.inj ha)
    simp only [X,C,List.append_assoc] at hr
    have he := List.append_cancel_left hr
    simp [V,T,U] at he
  · omega

theorem arbitrary1416 : ∀ n : Nat, ∃ t z, n ≤ t ∧ run0 (table true) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ n : Nat, ∃ t S, n≤t ∧ ValidB S ∧ run0 (table true) t ⟨0,[],[]⟩ = some (X (n+1) S) := by
    intro n
    induction n with
    | zero => exact ⟨14,[],by omega,Or.inl rfl,by rfl⟩
    | succ n ih =>
      obtain ⟨t,S,ht,hv,hr⟩ := ih
      obtain ⟨u,S',hu,hv',hr'⟩ := grow1416 (n+1) S (by omega) hv
      exact ⟨t+u,S',by omega,hv',join0 hr hr'⟩
  intro n
  obtain ⟨t,S,ht,_,hr⟩ := h n
  exact ⟨t,_,ht,hr⟩
#print axioms arbitrary1375
#print axioms arbitrary1416
end BB6Coverage.Agent4LF1Pair

namespace BB6Coverage.Agent4LF11375
open BB6Coverage
abbrev table := Agent4LF1Pair.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table Agent4LF1Pair.arbitrary1375 m hm
#print axioms never
end BB6Coverage.Agent4LF11375

namespace BB6Coverage.Agent4LF11416
open BB6Coverage
abbrev table := Agent4LF1Pair.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table Agent4LF1Pair.arbitrary1416 m hm
#print axioms never
end BB6Coverage.Agent4LF11416
