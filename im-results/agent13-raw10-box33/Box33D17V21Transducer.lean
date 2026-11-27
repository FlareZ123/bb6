import Box33D14Growth
namespace BB6.Agent13.Box33D17V21Transducer
open C9Pair
open BB6.Agent13.Box33D14Growth (z word cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

-- Pair alphabet, nearest cell first: 0=00, 1=01, 2=10, 3=11.
abbrev P := Fin 4
abbrev V := Fin 39
def dfa : List (List (Option V)) := [
  [some 1,some 2,none,none],
  [some 3,some 4,none,none],
  [some 5,some 6,none,none],
  [some 7,some 8,none,none],
  [some 9,none,none,none],
  [none,some 10,none,none],
  [none,some 11,none,none],
  [some 12,none,none,none],
  [some 13,none,none,none],
  [some 14,some 15,none,none],
  [none,some 16,none,none],
  [none,none,some 7,some 8],
  [some 17,none,none,none],
  [some 18,some 19,none,none],
  [some 20,none,none,none],
  [none,some 21,none,none],
  [none,none,some 14,some 15],
  [some 22,none,none,none],
  [none,some 23,none,none],
  [none,some 24,none,none],
  [some 25,some 26,none,none],
  [none,some 27,none,none],
  [some 28,none,none,none],
  [some 29,none,none,none],
  [none,some 24,some 25,some 26],
  [some 30,some 31,none,none],
  [some 26,some 25,none,none],
  [none,none,some 17,none],
  [some 32,some 33,none,none],
  [none,some 34,none,none],
  [some 35,none,none,none],
  [none,some 36,none,none],
  [some 37,some 37,none,none],
  [some 32,some 33,some 28,none],
  [none,some 35,none,none],
  [some 22,some 33,none,none],
  [none,some 38,some 35,none],
  [some 37,some 37,some 37,some 37],
  [none,none,none,some 34]]
def d (q : V) (a : P) : Option V := (dfa.getD q.val []).getD a.val none
def zerosOK (q : V) : Bool := ([0,1,3,4,7,9,12,14,17,20,22,25,26,28,30,32,33,35,37] : List V).contains q
def rel : List (V × P × V) := [
  (1,0,0),
  (2,1,0),
  (3,2,2),
  (4,3,2),
  (5,1,1),
  (6,0,1),
  (9,2,5),
  (10,0,3),
  (11,3,4),
  (16,3,8),
  (7,0,9),
  (8,1,9),
  (14,0,13),
  (15,1,13),
  (12,2,15),
  (13,1,14),
  (20,2,19),
  (21,0,18),
  (18,1,20),
  (19,0,20),
  (27,3,23),
  (23,0,25),
  (24,3,26),
  (17,0,29),
  (29,2,31),
  (25,0,26),
  (26,1,26),
  (22,2,34),
  (30,2,25),
  (31,3,25),
  (36,3,30),
  (38,3,35),
  (35,0,35),
  (34,1,22),
  (22,2,33),
  (33,3,33),
  (35,0,28),
  (32,2,32),
  (33,3,32),
  (28,0,32),
  (32,2,37),
  (33,3,37),
  (28,0,37)]
def Rel (i : V) (p : P) (o : V) : Prop := (i,p,o) ∈ rel
instance (i : V) (p : P) (o : V) : Decidable (Rel i p o) := inferInstanceAs (Decidable ((i,p,o) ∈ rel))

def ob (b : Bool) : P := if b then 1 else 0
def tp (a : P) : P := if a=0 then 2 else 3
def mv (p a : P) : Option (P × Bool) :=
  if p=0 then
    if a=0 then some (2,true) else if a=1 then some (3,true) else none
  else if p=1 then
    if a=0 then some (1,false) else if a=1 then some (0,false) else none
  else if p=3 then
    some (if a=0 then 2 else if a=1 then 3 else if a=2 then 0 else 1,false)
  else none

def walk (q : V) : List P → Option V
  | [] => some q
  | a::w => (d q a).bind (fun j => walk j w)
def obligation (r : V × P × V) (a : P) : Bool :=
  let (i,p,o) := r
  match d i a with
  | none => true
  | some j =>
    if p=2 then (a==0 || a==1) && (walk o [1,1,tp a] == some j)
    else match mv p a with
      | none => false
      | some (p',b) => match d o (ob b) with
        | none => false
        | some o' => decide (Rel j p' o')

theorem cert : rel.all (fun r => (List.finRange 4).all (obligation r)) = true := by decide
theorem certAt (i : V) (p : P) (o : V) (a : P) (h : Rel i p o) :
    obligation (i,p,o) a = true := by
  have h' := List.all_eq_true.mp cert (i,p,o) h
  exact List.all_eq_true.mp h' a (List.mem_finRange a)

theorem certStart : ∀ a : P, match d 0 a with
    | none => True
    | some i => Rel i a 0 := by decide

theorem zeroStep : ∀ q : V, zerosOK q = true →
    ∃ j : V, d q 0 = some j ∧ zerosOK j = true := by decide

inductive Good : V → List P → Prop
  | nil {q : V} : zerosOK q = true → Good q []
  | cons {q j : V} {a : P} {w : List P} :
      d q a = some j → Good j w → Good q (a::w)

def hd (w : List P) : P := w.headD 0
def tl (w : List P) : List P := w.tail

theorem goodNext {q : V} {w : List P} (h : Good q w) :
    ∃ j, d q (hd w) = some j ∧ Good j (tl w) := by
  cases h with
  | nil hz =>
    obtain ⟨j,hj,hzj⟩ := zeroStep _ hz
    exact ⟨j,hj,Good.nil hzj⟩
  | cons ha hw => exact ⟨_,ha,hw⟩

theorem walk_append (q : V) (u w : List P) :
    walk q (u++w) = (walk q u).bind (fun j => walk j w) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append,walk]
    cases h : d q a <;> simp [ih]

theorem goodPrefix {q j : V} {u w : List P}
    (h : walk q u = some j) (hw : Good j w) : Good q (u++w) := by
  induction u generalizing q with
  | nil =>
    change some q = some j at h
    cases h
    exact hw
  | cons a u ih =>
    simp only [walk] at h
    cases ha : d q a with
    | none => simp [ha] at h
    | some k =>
      simp only [ha,Option.bind_some] at h
      exact Good.cons ha (ih h)

def pair (p : P) (l : Stream) : Stream := word [decide (p.val ≥ 2),decide (p.val % 2 = 1)] l
def tapePrefix : List P → Stream → Stream
  | [],l => l
  | p::w,l => pair p (tapePrefix w l)
abbrev tape (w : List P) := tapePrefix w z

theorem tapeAppend (u w : List P) (l : Stream) :
    tapePrefix (u++w) l = tapePrefix u (tapePrefix w l) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append,tapePrefix,ih]

theorem tapeSplit (w : List P) : tape w = pair (hd w) (tape (tl w)) := by
  cases w with
  | nil => simp [tape,tapePrefix,hd,tl,pair,word]
  | cons a w => rfl

def rtPair (b : Bool) (r : Stream) : Stream := word [!b,true] r
def rightTape : List Bool → Stream
  | [] => z
  | b::u => rtPair b (rightTape u)
def outWord (u : List Bool) : List P := u.reverse.map ob
abbrev A (l r : Stream) := cfg .A l r
abbrev S (l r : Stream) := A l (word [false,false] r)

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .B false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .A false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .E true c)
  | .E,false => some (left .F false c)
  | .E,true => some (left .A true c)
  | .F,false => some (right .A true c)
  | .F,true => none

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; cases h : step c <;> simp [ih]

def cost (p : P) : Nat := if p=0 then 6 else if p=1 then 14 else 10

theorem macro (p a p' : P) (b : Bool) (h : mv p a = some (p',b)) (l r : Stream) :
    run (cost p) (S (pair p (pair a l)) r) = some (S (pair p' l) (rtPair b r)) := by
  have hp : p=0 ∨ p=1 ∨ p=2 ∨ p=3 := by omega
  have ha : a=0 ∨ a=1 ∨ a=2 ∨ a=3 := by omega
  rcases hp with rfl|rfl|rfl|rfl <;> rcases ha with rfl|rfl|rfl|rfl <;>
    simp [mv] at h <;> obtain ⟨rfl,rfl⟩ := h <;>
    simp [cost,S,A,pair,rtPair,cfg,run,step,left,right,word]

theorem turnMacro (a : P) (h : a=0 ∨ a=1) (l r : Stream) :
    run 6 (S (pair 2 (pair a l)) r) =
      some (A (pair (tp a) l) (rtPair true (rtPair true r))) := by
  rcases h with rfl|rfl <;>
    simp [S,A,pair,tp,rtPair,cfg,run,step,left,right,word]

theorem rightMacro (b : Bool) (l r : Stream) :
    run 2 (A l (rtPair b r)) = some (A (pair (ob b) l) r) := by
  cases b <;> simp [A,rtPair,pair,ob,cfg,run,step,left,right,word]

theorem outCons (b : Bool) (u : List Bool) :
    outWord (b::u) = outWord u ++ [ob b] := by
  simp [outWord,List.reverse_cons]

theorem sweep (u : List Bool) (l : Stream) :
    run (2*u.length) (A l (rightTape u)) = some (A (tapePrefix (outWord u) l) z) := by
  induction u generalizing l with
  | nil => rfl
  | cons b u ih =>
    rw [List.length_cons,show 2*(u.length+1)=2+2*u.length by omega,run_add]
    simp only [rightTape,rightMacro,Option.bind_some,ih,outCons,tapeAppend,tapePrefix]

def Inv (c : Config) : Prop :=
  ∃ (i : V) (p : P) (o : V) (w : List P) (u : List Bool),
    Rel i p o ∧ Good i w ∧ walk 0 (outWord u) = some o ∧
    c = S (pair p (tape w)) (rightTape u)

theorem rootInv (w : List P) (h : Good 0 w) : Inv (A (tape w) z) := by
  obtain ⟨i,hi,hw⟩ := goodNext h
  have hr := certStart (hd w)
  rw [hi] at hr
  refine ⟨i,hd w,0,tl w,[],hr,hw,rfl,?_⟩
  rw [tapeSplit w]
  simp [S,rightTape,word]

theorem progress {c : Config} (hc : Inv c) :
    ∃ n : Nat, 0<n ∧ ∃ c', run n c = some c' ∧ Inv c' := by
  obtain ⟨i,p,o,w,u,hr,hw,ho,rfl⟩ := hc
  obtain ⟨j,hj,hw'⟩ := goodNext hw
  have h := certAt i p o (hd w) hr
  unfold obligation at h
  rw [hj] at h
  by_cases hp : p=2
  · subst p
    simp only [if_pos rfl,Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true] at h
    obtain ⟨ha,ht⟩ := h
    let v := true::true::u
    let l := pair (tp (hd w)) (tape (tl w))
    have h1 := turnMacro (hd w) ha (tape (tl w)) (rightTape u)
    have h2 := sweep v l
    have h3 : run (6+2*v.length) (S (pair 2 (tape w)) (rightTape u)) =
        some (A (tapePrefix (outWord v) l) z) := by
      rw [tapeSplit w,run_add,h1,Option.bind_some]
      exact h2
    have hv : outWord v = outWord u ++ [1,1] := by
      simp [v,outCons,ob,List.append_assoc]
    have hg : Good 0 (outWord u ++ [1,1,tp (hd w)] ++ tl w) := by
      apply goodPrefix (j:=j) (w:=tl w)
      · rw [walk_append,ho,Option.bind_some]
        exact ht
      · exact hw'
    refine ⟨6+2*v.length,by omega,_,h3,?_⟩
    have he : tapePrefix (outWord v) l = tape (outWord u ++ [1,1,tp (hd w)] ++ tl w) := by
      rw [hv]
      simp [tapeAppend,tapePrefix,l,List.append_assoc]
    rw [he]
    exact rootInv _ hg
  · simp only [if_neg hp] at h
    cases hm : mv p (hd w) with
    | none => simp [hm] at h
    | some m =>
      obtain ⟨p',b⟩ := m
      rw [hm] at h
      cases he : d o (ob b) with
      | none => simp [he] at h
      | some o' =>
        rw [he] at h
        have hrel : Rel j p' o' := of_decide_eq_true h
        refine ⟨cost p,by unfold cost; split <;> try split <;> omega,_,?_,?_⟩
        · rw [tapeSplit w]
          exact macro p (hd w) p' b hm (tape (tl w)) (rightTape u)
        · refine ⟨j,p',o',tl w,b::u,hrel,hw',?_,rfl⟩
          rw [outCons,walk_append,ho,Option.bind_some,walk,he]
          rfl

theorem never_inv (n : Nat) (c : Config) (hc : Inv c) : run n c ≠ none := by
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    intro h
    obtain ⟨t,ht,c',hr,hc'⟩ := progress hc
    by_cases hn : n ≤ t
    · rw [←show n+(t-n)=t by omega,run_add,h] at hr
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,hr,Option.bind_some] at h
      exact ih _ (by omega) c' hc' h

def blank : Config := A z z
theorem never_blank (n : Nat) : run n blank ≠ none :=
  never_inv n blank (rootInv [] (Good.nil (by decide)))
#print axioms never_blank
end BB6.Agent13.Box33D17V21Transducer
