import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V16Sweep
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add rep_succ rep_zero word_cons word_nil cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .B true c)
  | .E,false => some (right .D true c)
  | .E,true => some (right .E true c)
  | .F,false => some (left .A false c)
  | .F,true => some (right .F false c)
abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev A := cfg .A
abbrev F := cfg .F
abbrev ones := rep [true]
abbrev zeros := rep [false]
abbrev R (b : Nat) (r : Stream) := zeros 2 (ones b r)

theorem popOne (l r : Stream) : run 7 (A (ones 2 l) (zeros 2 r)) = some (A (ones 1 l) (zeros 2 (push true r))) := by
  simp [A,cfg,ones,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem smallCross (l r : Stream) : run 10 (A (word [true,false,true,true] (push true l)) (zeros 2 r)) =
    some (A (push true l) (word [false,false,true,true,false,true] r)) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem bigCross (l r : Stream) : run 6 (A (push true (zeros 3 (push false l))) (zeros 2 r)) =
    some (A (push false l) (word [false,false,true,true,false,true] r)) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem crossZero (l r : Stream) : run 6 (A (push true (zeros 3 l)) (zeros 2 r)) =
    some (A l (word [false,false,true,true,false,true] r)) := by
  simp [A,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem startRight0 (l r : Stream) : run 13 (A (word [false,false] l) (zeros 2 r)) = some (F (ones 3 l) (push true r)) := by
  simp [A,F,cfg,ones,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem startRight1 (l r : Stream) : run 11 (A (word [false,true] l) (zeros 2 r)) = some (F (ones 3 l) (push true r)) := by
  simp [A,F,cfg,ones,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fOne (l r : Stream) : run 1 (F l (push true r)) = some (F (push false l) r) := by
  simp [F,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fSweep (n : Nat) (l r : Stream) : run n (F l (ones n r)) = some (F (zeros n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,show ones (1+n) r = ones 1 (ones n r) from rep_add _ _ _ _,run_add]
    change (run 1 (F l (push true (ones n r)))).bind (run n) = _
    rw [fOne,Option.bind_some,ih,show 1+n=n+1 by omega,show zeros (n+1) l = zeros n (zeros 1 l) from rep_add _ _ _ _]
    rfl
theorem fExit (l r : Stream) : run 1 (F (push false l) (push false r)) = some (A l (zeros 2 r)) := by
  simp [A,F,cfg,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem rightBlock (b : Bool) (k : Nat) (l r : Stream) :
    run (if b then k+13 else k+15) (A (word [false,b] l) (R k (push false r))) = some (A (zeros k (ones 3 l)) (zeros 2 r)) := by
  have hs : run (if b then 11 else 13) (A (word [false,b] l) (R k (push false r))) = some (F (ones 3 l) (push true (ones k (push false r)))) := by
    cases b <;> first | exact startRight0 l _ | exact startRight1 l _
  rw [show (if b then k+13 else k+15) = (if b then 11 else 13) + (1+k) + 1 by cases b <;> simp <;> omega,run_add,run_add,hs,Option.bind_some]
  rw [show 1+k=k+1 by omega]
  change (run (k+1) (F (ones 3 l) (ones (k+1) (push false r)))).bind (run 1) = _
  rw [fSweep,Option.bind_some]
  exact fExit _ _

abbrev Chunk := Nat × Nat
def ltape : List Chunk → Stream
  | [] => z
  | (a,b)::xs => zeros a (ones b (ltape xs))
def Boundary (xs : List Chunk) : Prop := xs = [] ∨ ∃ i j ys, xs = (4+5*i,6+5*j)::ys
inductive Tail : List Chunk → Prop where
  | nil : Tail []
  | small (xs) : Tail xs → Tail ((1,3)::xs)
  | big (i j : Nat) (xs) : Tail xs → Boundary xs → Tail ((4+5*i,6+5*j)::xs)
  | last (j : Nat) (xs) : Tail xs → Boundary xs → Tail ((1,6+5*j)::xs)

def Good (n : Nat) : Prop := n=3 ∨ ∃ j, n=6+5*j
def lguard (n : Nat) (xs : List Chunk) : Prop := n=3 ∨ Boundary xs
abbrev rtape (r : Nat) := rep [false,true,true,true] r z
abbrev LS (a b : Nat) (xs : List Chunk) (r : Nat) := A (ones (a+1) (ltape xs)) (R b (rtape r))
abbrev RS (g n : Nat) (xs : List Chunk) (r : Nat) := A (zeros g (ones n (ltape xs))) (push false (rtape r))

inductive Safe : Config → Prop where
  | leftS (a b : Nat) (xs : List Chunk) (r : Nat) :
    Tail xs → Good (a+1+b) → lguard (a+1+b) xs → Safe (LS a b xs r)
  | firstR (g j : Nat) (xs : List Chunk) (r : Nat) :
    Tail xs → Boundary xs → Good g → Safe (RS g (6+5*j) xs r)
  | normalR (xs : List Chunk) (r : Nat) : Tail xs → Safe (RS 3 3 xs r)

theorem boundary_nil : Boundary [] := Or.inl rfl
theorem boundary_big (i j : Nat) (xs : List Chunk) : Boundary ((4+5*i,6+5*j)::xs) := Or.inr ⟨i,j,xs,rfl⟩
theorem not_boundary_small (n : Nat) (xs : List Chunk) : ¬ Boundary ((1,n)::xs) := by
  intro h; rcases h with h | ⟨i,j,ys,h⟩
  · contradiction
  · injection h with h1 h2
    have hh := congrArg Prod.fst h1
    simp at hh
    omega

theorem rtape_succ (r : Nat) : rtape (r+1) = push false (ones 3 (rtape r)) := rfl
theorem rshape (r : Nat) : push false (rtape (r+1)) = R 3 (rtape r) := rfl
theorem rzero : push false (rtape 0) = R 0 z := by simp [rtape,zeros,ones,rep,word]

theorem rtape_head (r : Nat) : rtape r 0 = false := by cases r <;> rfl
theorem rtape_decomp (r : Nat) : push false (pop (rtape r)) = rtape r := by
  rw [←rtape_head r]; exact push_pop _
theorem rightLast (b : Bool) (k : Nat) (l : Stream) (r : Nat) :
    run (if b then k+13 else k+15) (A (word [false,b] l) (R k (rtape r))) = some (A (zeros k (ones 3 l)) (push false (rtape r))) := by
  have h := rightBlock b k l (pop (rtape r))
  rw [rtape_decomp] at h
  change _ = some (A (zeros k (ones 3 l)) (push false (push false (pop (rtape r))))) at h
  rw [rtape_decomp] at h
  exact h

theorem popLS (a b : Nat) (xs : List Chunk) (r : Nat) : run 7 (LS (a+1) b xs r) = some (LS a (b+1) xs r) := by
  exact popOne (ones a (ltape xs)) (ones b (rtape r))

theorem crossSmallLS (a : Nat) (xs : List Chunk) (r : Nat) : run 10 (LS 0 2 ((1,a+3)::xs) r) = some (LS a 2 xs (r+1)) := by
  exact smallCross (ones a (ltape xs)) (ones 2 (rtape r))

theorem crossBlankLS (b r : Nat) : run 6 (LS 0 b [] r) =
    some (A z (R 2 (push false (ones (b+1) (rtape r))))) := by
  have h := crossZero z (ones b (rtape r))
  simp only [zeros,rep_succ,rep_zero,word_cons,word_nil,BB6.Agent13.Box33D14Growth.z_push] at h
  exact h

theorem crossBigLS (b i j : Nat) (xs : List Chunk) (r : Nat) : run 6 (LS 0 b ((4+5*i,6+5*j)::xs) r) =
    some (A (zeros (1+5*i) (ones (6+5*j) (ltape xs))) (R 2 (push false (ones (b+1) (rtape r))))) := by
  have h := crossZero (zeros (1+5*i) (ones (6+5*j) (ltape xs))) (ones b (rtape r))
  change run 6 (A (push true (zeros (4+5*i) (ones (6+5*j) (ltape xs)))) _) = _
  rw [show 4+5*i=3+(1+5*i) by omega,show zeros (3+(1+5*i)) (ones (6+5*j) (ltape xs)) = zeros 3 (zeros (1+5*i) (ones (6+5*j) (ltape xs))) from rep_add _ _ _ _]
  exact h

theorem twoBlank (g r : Nat) : run (g+32) (A z (R 2 (push false (ones g (rtape r))))) = some (RS g 6 [] r) := by
  have h1 := rightBlock false 2 z (ones g (rtape r))
  have h2 := rightLast false g (ones 3 z) r
  have h1' : run 17 (A z (R 2 (push false (ones g (rtape r))))) = some (A (zeros 2 (ones 3 z)) (R g (rtape r))) := by
    simpa only [word_cons,word_nil,BB6.Agent13.Box33D14Growth.z_push, Bool.false_eq_true, ite_false] using h1
  rw [show g+32=17+(g+15) by omega,run_add,h1',Option.bind_some]
  exact h2

theorem twoBigZero (g j : Nat) (xs : List Chunk) (r : Nat) :
    run (g+30) (A (zeros 1 (ones (6+5*j) (ltape xs))) (R 2 (push false (ones g (rtape r))))) =
    some (RS g (6+5*(j+1)) xs r) := by
  have h1 := rightBlock true 2 (ones (5+5*j) (ltape xs)) (ones g (rtape r))
  have h2 := rightLast false g (ones (8+5*j) (ltape xs)) r
  have hl : ones (6+5*j) (ltape xs) = push true (ones (5+5*j) (ltape xs)) := by rw [show 6+5*j=(5+5*j)+1 by omega]; rfl
  rw [hl,show g+30=15+(g+15) by omega,run_add]
  change (run 15 (A (word [false,true] (ones (5+5*j) (ltape xs))) _)).bind _ = _
  change run 15 (A (word [false,true] (ones (5+5*j) (ltape xs))) (R 2 (push false (ones g (rtape r))))) = some (A (zeros 2 (ones 3 (ones (5+5*j) (ltape xs)))) (R g (rtape r))) at h1
  rw [h1,Option.bind_some]
  have he : ones 3 (ones (5+5*j) (ltape xs)) = ones (8+5*j) (ltape xs) := by rw [show 8+5*j=3+(5+5*j) by omega]; exact (rep_add _ _ _ _).symm
  rw [he]
  change run (g+15) (A (zeros 2 (ones (8+5*j) (ltape xs))) (R g (rtape r))) = some (RS g (6+5*(j+1)) xs r)
  change run (g+15) (A (zeros 2 (ones (8+5*j) (ltape xs))) (R g (rtape r))) = some (A (zeros g (ones 3 (ones (8+5*j) (ltape xs)))) (push false (rtape r))) at h2
  rw [h2]
  congr 3
  change ones 3 (ones (8+5*j) (ltape xs)) = ones (6+5*(j+1)) (ltape xs)
  rw [show 6+5*(j+1)=3+(8+5*j) by omega]; exact (rep_add _ _ _ _).symm

theorem twoBigSucc (g i j : Nat) (xs : List Chunk) (r : Nat) :
    run (g+32) (A (zeros (1+5*(i+1)) (ones (6+5*j) (ltape xs))) (R 2 (push false (ones g (rtape r))))) =
    some (RS g 6 ((4+5*i,6+5*j)::xs) r) := by
  rw [show 1+5*(i+1)=2+(4+5*i) by omega,show zeros (2+(4+5*i)) (ones (6+5*j) (ltape xs)) = zeros 2 (ltape ((4+5*i,6+5*j)::xs)) from rep_add _ _ _ _]
  rw [show g+32=17+(g+15) by omega,run_add]
  have h1 := rightBlock false 2 (ltape ((4+5*i,6+5*j)::xs)) (ones g (rtape r))
  change run 17 (A (zeros 2 (ltape ((4+5*i,6+5*j)::xs))) (R 2 (push false (ones g (rtape r))))) = some (A (zeros 2 (ones 3 (ltape ((4+5*i,6+5*j)::xs)))) (R g (rtape r))) at h1
  rw [h1,Option.bind_some]
  exact rightLast false g (ones 3 (ltape ((4+5*i,6+5*j)::xs))) r

theorem rightNext (g n k : Nat) (xs : List Chunk) (r : Nat) :
    run (k+15) (A (zeros (g+2) (ones n (ltape xs))) (R k (rtape r))) =
      some (RS k 3 ((g,n)::xs) r) := by
  rw [show g+2=2+g by omega,show zeros (2+g) (ones n (ltape xs)) = zeros 2 (ltape ((g,n)::xs)) from rep_add _ _ _ _]
  exact rightLast false k (ltape ((g,n)::xs)) r

theorem finishR (g n : Nat) (xs : List Chunk) : run 15 (RS (g+2) n xs 0) = some (LS 2 0 ((g,n)::xs) 0) := by
  have h := rightNext g n 0 xs 0
  change run 15 (A (zeros (g+2) (ones n (ltape xs))) (push false z)) = some (A (ones 3 (ltape ((g,n)::xs))) (R 0 z))
  rw [show R 0 z = push false z by exact rzero.symm]
  exact h

theorem advanceR (g n : Nat) (xs : List Chunk) (r : Nat) : run 18 (RS (g+2) n xs (r+1)) = some (RS 3 3 ((g,n)::xs) r) := by
  change run 18 (A (zeros (g+2) (ones n (ltape xs))) (push false (rtape (r+1)))) = _
  rw [rshape]
  exact rightNext g n 3 xs r

theorem rightProgress (g n : Nat) (xs : List Chunk) (r : Nat) (h : Tail ((g,n)::xs)) :
    ∃ t c, 0<t ∧ Safe c ∧ run t (RS (g+2) n xs r) = some c := by
  cases r with
  | zero => exact ⟨15,_,by decide,Safe.leftS 2 0 _ 0 h (Or.inl rfl) (Or.inl rfl),finishR g n xs⟩
  | succ r => exact ⟨18,_,by decide,Safe.normalR _ r h,advanceR g n xs r⟩

theorem leftProgress (a b : Nat) (xs : List Chunk) (r : Nat) (hl : Tail xs) (hg : Good (a+1+b)) (hc : lguard (a+1+b) xs) :
    ∃ t c, 0<t ∧ Safe c ∧ run t (LS a b xs r) = some c := by
  cases a with
  | succ a =>
    have eq : a+1+(b+1) = a+1+1+b := by omega
    exact ⟨7,_,by decide,Safe.leftS a (b+1) xs r hl (eq ▸ hg) (eq ▸ hc),popLS a b xs r⟩
  | zero =>
    have hg' : Good (b+1) := by rw [show b+1=0+1+b by omega]; exact hg
    cases hl with
    | nil =>
      have h1 := crossBlankLS b r
      have h2 := twoBlank (b+1) r
      refine ⟨6+(b+1+32),_,by omega,Safe.firstR (b+1) 0 [] r Tail.nil boundary_nil hg',?_⟩
      rw [run_add,h1,Option.bind_some]; exact h2
    | small xs ht =>
      have hb : b=2 := by
        rcases hc with h | h
        · omega
        · exact False.elim (not_boundary_small 3 xs h)
      subst b
      exact ⟨10,_,by decide,Safe.leftS 0 2 xs (r+1) ht (Or.inl rfl) (Or.inl rfl),crossSmallLS 0 xs r⟩
    | last j xs ht hbd =>
      have hb : b=2 := by
        rcases hc with h | h
        · omega
        · exact False.elim (not_boundary_small _ xs h)
      subst b
      have hh := crossSmallLS (3+5*j) xs r
      have ee : 3+5*j+3=6+5*j := by omega
      rw [ee] at hh
      exact ⟨10,_,by decide,Safe.leftS (3+5*j) 2 xs (r+1) ht (Or.inr ⟨j,by omega⟩) (Or.inr hbd),hh⟩
    | big i j xs ht hbd =>
      have h1 := crossBigLS b i j xs r
      cases i with
      | zero =>
        have h2 := twoBigZero (b+1) j xs r
        exact ⟨6+(b+1+30),_,by omega,Safe.firstR (b+1) (j+1) xs r ht hbd hg',by rw [run_add,h1,Option.bind_some]; exact h2⟩
      | succ i =>
        have h2 := twoBigSucc (b+1) i j xs r
        exact ⟨6+(b+1+32),_,by omega,Safe.firstR (b+1) 0 _ r (Tail.big i j xs ht hbd) (boundary_big i j xs) hg',by rw [run_add,h1,Option.bind_some]; exact h2⟩

theorem progress {c : Config} (hs : Safe c) : ∃ t d, 0<t ∧ Safe d ∧ run t c = some d := by
  cases hs with
  | leftS a b xs r ht hg hc => exact leftProgress a b xs r ht hg hc
  | normalR xs r ht => exact rightProgress 1 3 xs r (Tail.small xs ht)
  | firstR g j xs r ht hb hg =>
    rcases hg with h | ⟨i,h⟩
    · subst g
      exact rightProgress 1 (6+5*j) xs r (Tail.last j xs ht hb)
    · subst g
      have eq : 6+5*i=4+5*i+2 := by omega
      rw [eq]
      exact rightProgress (4+5*i) (6+5*j) xs r (Tail.big i j xs ht hb)

theorem neverSafe (n : Nat) (c : Config) (hs : Safe c) : run n c ≠ none := by
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    intro hn
    obtain ⟨t,d,ht,hd,hr⟩ := progress hs
    by_cases hnt : n ≤ t
    · rw [←show n+(t-n)=t by omega,run_add,hn] at hr
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at hn
      exact ih (n-t) (by omega) d hd hn

theorem init : run 15 (A z z) = some (LS 2 0 [] 0) := by
  simp [LS,ltape,R,rtape,A,cfg,ones,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem neverBlank (n : Nat) : run n (A z z) ≠ none := by
  intro hn
  have hr := init
  by_cases h : n ≤ 15
  · rw [←show n+(15-n)=15 by omega,run_add,hn] at hr
    contradiction
  · rw [←show 15+(n-15)=n by omega,run_add,hr,Option.bind_some] at hn
    exact neverSafe (n-15) _ (Safe.leftS 2 0 [] 0 Tail.nil (Or.inl rfl) (Or.inl rfl)) hn
#print axioms neverBlank


open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,0,11,24,1,13,17,7,16,20,1,22]
def table : Machine := fun a => decode (codes.getD (index a).val 0)
theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map BB6.Agent13.Box33PrefixMacro.project = step (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨q,p,t⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank n
def partialTable : PartialMachine := fun a => some (table a)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun a => hm a _ rfl
  rw [he]
  exact never
#print axioms compatible_never
end BB6.Agent13.Box33D17V16Sweep
