import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LAUnaryGrammar
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

inductive Variant where
  | short | longA | longD

def table (v : Variant) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,match v with | .longA => 0 | _ => 3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨true,false,match v with | .short => 2 | _ => 5⟩)
  | _,_ => none

abbrev U (n : Nat) := List.replicate n true
def blocks : List Nat → List Bool
  | [] => []
  | n::ns => false::(U n ++ blocks ns)
def C (ls rs : List Nat) : Z0 := ⟨0,blocks ls,(blocks rs).tail⟩
def inc (b : Nat) : List Nat → List Nat
  | [] => [b]
  | a::ls => (a+b)::ls

theorem uAdd (a b : Nat) : U (a+b) = U a ++ U b := List.replicate_append_replicate.symm
theorem repU (n : Nat) : rep [true] n = U n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]

def splitCost : Variant → Nat
  | .short => 7
  | _ => 9

theorem splitZero (v : Variant) (L R : List Bool) :
    run0 (table v) (splitCost v) ⟨0,false::L,[true,true,true]++R⟩ =
      some ⟨0,L,[true,true,false,true]++R⟩ := by cases v <;> rfl

theorem splitBlank (v : Variant) (R : List Bool) :
    run0 (table v) (splitCost v) ⟨0,[],[true,true,true]++R⟩ =
      some ⟨0,[],[true,true,false,true]++R⟩ := by cases v <;> rfl

theorem aOne (v : Variant) (L R : List Bool) :
    run0 (table v) 1 ⟨0,[true]++L,R⟩ = some ⟨0,L,[true]++R⟩ := by cases v <;> rfl

theorem aSweep (v : Variant) (a : Nat) (L R : List Bool) :
    run0 (table v) a ⟨0,U a++L,R⟩ = some ⟨0,L,U a++R⟩ := by
  simpa only [repU,List.nil_append,Nat.one_mul] using
    sweepL (table v) 0 [] [] [true] [true] 1 (aOne v) a L R

theorem splitAt (v : Variant) (a k : Nat) (ls rs : List Nat) :
    run0 (table v) (splitCost v+a) (C (a::ls) ((k+3)::rs)) =
      some (C ls ((a+2)::(k+1)::rs)) := by
  have h := splitZero v (U a++blocks ls) (U k++blocks rs)
  have g := aSweep v a (blocks ls) ([true,true,false,true]++(U k++blocks rs))
  have H := join0 h g
  have he : U (a+2) ++ false::(U (k+1)++blocks rs) =
      U a ++ ([true,true,false,true]++(U k++blocks rs)) := by
    rw [uAdd a 2]
    simp only [List.append_assoc,show U 2=[true,true] by rfl,show U (k+1)=true::U k by rfl,List.cons_append,List.nil_append]
  rw [←he] at H
  exact H

theorem splitRoot (v : Variant) (k : Nat) (rs : List Nat) :
    run0 (table v) (splitCost v) (C [] ((k+3)::rs)) =
      some (C [] (2::(k+1)::rs)) := splitBlank v (U k++blocks rs)

theorem consumeOne (v : Variant) (L R : List Bool) :
    run0 (table v) 7 ⟨0,[false]++L,[true,true,false]++[true]++R⟩ =
      some ⟨0,[false]++[true]++L,[true,true,false]++R⟩ := by cases v <;> rfl

theorem consumeRun (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (table v) (7*n) ⟨0,false::L,[true,true,false]++U n++R⟩ =
      some ⟨0,false::(U n++L),[true,true,false]++R⟩ := by
  simpa only [repU,List.singleton_append,List.cons_append] using
    sweepR (table v) 0 [false] [true,true,false] [true] [true] 7 (consumeOne v) n L R

theorem consumeBlank (v : Variant) (n : Nat) (R : List Bool) :
    run0 (table v) (7*(n+1)) ⟨0,[],[true,true,false]++U (n+1)++R⟩ =
      some ⟨0,false::U (n+1),[true,true,false]++R⟩ := by
  have h : run0 (table v) 7 ⟨0,[],[true,true,false]++U (n+1)++R⟩ =
      some ⟨0,[false,true],[true,true,false]++U n++R⟩ := by cases v <;> rfl
  have g := consumeRun v n [true] R
  have H := join0 h g
  rw [show 7+7*n=7*(n+1) by omega] at H
  have he : U n++[true]=U (n+1) := (uAdd n 1).symm
  rw [he] at H
  exact H

def consumed (ls : List Nat) (n : Nat) (rs : List Nat) : Z0 :=
  ⟨0,blocks (inc (n+1) ls),[true,true,false]++blocks rs⟩

theorem consumePair (v : Variant) (ls : List Nat) (n : Nat) (rs : List Nat) :
    run0 (table v) (7*(n+1)) (C ls (2::(n+1)::rs)) =
      some (consumed ls n rs) := by
  cases ls with
  | nil => simpa only [C,consumed,inc,blocks,List.tail_cons,List.append_nil,List.append_assoc,List.cons_append] using consumeBlank v n (blocks rs)
  | cons a ls =>
    have H := consumeRun v (n+1) (U a++blocks ls) (blocks rs)
    have he : U (n+1)++(U a++blocks ls)=U (a+(n+1))++blocks ls := by
      rw [←List.append_assoc,←uAdd, Nat.add_comm (n+1) a]
    rw [he] at H
    exact H

theorem skipOne (v : Variant) (L R : List Bool) :
    run0 (table v) 6 ⟨0,false::L,[true,true,false,false,true]++R⟩ =
      some ⟨0,[false,true,true,false,true]++L,true::R⟩ := by cases v <;> rfl

theorem skipAfter (v : Variant) (ls : List Nat) (n a : Nat) (rs : List Nat) :
    run0 (table v) 6 (consumed ls n ((a+1)::rs)) =
      some (C (2::inc (n+2) ls) ((a+1)::rs)) := by
  cases ls with
  | nil => simpa only [C,consumed,inc,blocks,List.tail_cons,List.append_nil,List.append_assoc,List.cons_append] using skipOne v (U (n+1)) (U a++blocks rs)
  | cons b ls =>
    have H := skipOne v (U (b+(n+1))++blocks ls) (U a++blocks rs)
    exact H

theorem pairAdvance (v : Variant) (ls : List Nat) (n a : Nat) (rs : List Nat) :
    run0 (table v) (7*(n+1)+6) (C ls (2::(n+1)::(a+1)::rs)) =
      some (C (2::inc (n+2) ls) ((a+1)::rs)) :=
  join0 (consumePair v ls n ((a+1)::rs)) (skipAfter v ls n a rs)

theorem endZero (v : Variant) (L : List Bool) :
    run0 (table v) 9 ⟨0,false::L,[true,true]⟩ =
      some ⟨0,false::true::L,U 4⟩ := by cases v <;> rfl

theorem endBlank (v : Variant) :
    run0 (table v) 9 ⟨0,[],[true,true]⟩ =
      some ⟨0,[false,true],U 4⟩ := by cases v <;> rfl

theorem endConsumed (v : Variant) (L : List Bool) :
    run0 (table v) 9 ⟨0,false::L,[true,true,false]⟩ =
      some ⟨0,false::true::L,U 4⟩ := by cases v <;> rfl

theorem terminalSingle (v : Variant) (ls : List Nat) :
    run0 (table v) 9 (C ls [2]) = some (C (inc 1 ls) [4]) := by
  cases ls with
  | nil => exact endBlank v
  | cons a ls => exact endZero v (U a++blocks ls)

theorem terminalPair (v : Variant) (ls : List Nat) (n : Nat) :
    run0 (table v) (7*(n+1)+9) (C ls [2,n+1]) =
      some (C (inc (n+2) ls) [4]) := by
  have H := consumePair v ls n []
  cases ls with
  | nil =>
    have h : run0 (table v) 9 (consumed [] n []) = some (C (inc (n+2) []) [4]) := by
      simpa only [consumed,C,inc,blocks,List.append_nil,List.tail_cons] using endConsumed v (U (n+1))
    exact join0 H h
  | cons a ls => exact join0 H (endConsumed v (U (a+(n+1))++blocks ls))

theorem retreat (v : Variant) (ls : List Nat) (hp : ∀ a ∈ ls, 0<a)
    (k : Nat) (rs : List Nat) :
    ∃ t, 0<t ∧ run0 (table v) t (C ls ((k+3)::rs)) =
      some (C [] (2::ls.reverse++(k+1)::rs)) := by
  induction ls generalizing k rs with
  | nil =>
    refine ⟨splitCost v, ?_, splitRoot v k rs⟩
    cases v <;> decide
  | cons a ls ih =>
    have ha : 0<a := hp a (by simp)
    have hls : ∀ b ∈ ls, 0<b := by
      intro b hb
      exact hp b (by simp [hb])
    cases a with
    | zero => omega
    | succ a =>
      have h := splitAt v (a+1) k ls rs
      obtain ⟨t,ht,hr⟩ := ih hls a ((k+1)::rs)
      have H := join0 h hr
      refine ⟨splitCost v+(a+1)+t, by omega, ?_⟩
      simpa only [List.reverse_cons,List.cons_append,List.append_assoc,List.singleton_append] using H

inductive Good : List Nat → Prop
  | nil : Good []
  | two : Good [2]
  | pair (n : Nat) (rs : List Nat) : Good rs → Good (2::(n+1)::rs)
  | big (k : Nat) (rs : List Nat) : Good rs → Good ((k+3)::rs)

inductive Prefix : List Nat → Prop
  | first (n : Nat) : Prefix [n+2]
  | more (n : Nat) (p : List Nat) : Prefix p → Prefix ((n+3)::p)

theorem prefixGood {p : List Nat} (hp : Prefix p) (rs : List Nat) (hr : Good rs) :
    Good (2::p.reverse++rs) := by
  induction hp generalizing rs with
  | first n => exact Good.pair (n+1) rs hr
  | more n p hp ih =>
    simpa only [List.reverse_cons,List.cons_append,List.append_assoc,List.singleton_append] using
      ih ((n+3)::rs) (Good.big n rs hr)

theorem prefixPositive {p : List Nat} (hp : Prefix p) : ∀ a ∈ p, 0<a := by
  induction hp with
  | first n =>
    intro a ha
    simp only [List.mem_singleton] at ha
    omega
  | more n p hp ih =>
    intro a ha
    rcases List.mem_cons.mp ha with h|h
    · omega
    · exact ih a h

inductive Ctx : List Nat → Prop
  | nil : Ctx []
  | cons (p : List Nat) : Prefix p → Ctx (2::p)

theorem ctxPositive {ls : List Nat} (hc : Ctx ls) : ∀ a ∈ ls, 0<a := by
  cases hc with
  | nil => simp
  | cons p hp =>
    intro a ha
    rcases List.mem_cons.mp ha with h|h
    · omega
    · exact prefixPositive hp a h

theorem ctxAdvance {ls : List Nat} (hc : Ctx ls) (n : Nat) : Ctx (2::inc (n+2) ls) := by
  cases hc with
  | nil => exact Ctx.cons _ (Prefix.first n)
  | cons p hp =>
    have h : 2+(n+2)=(n+1)+3 := by omega
    simpa only [inc,h] using Ctx.cons _ (Prefix.more (n+1) p hp)

theorem incPositive {ls : List Nat} (hc : Ctx ls) (n : Nat) :
    ∀ a ∈ inc (n+1) ls, 0<a := by
  cases hc with
  | nil =>
    intro a ha
    simp only [inc,List.mem_singleton] at ha
    omega
  | cons p hp =>
    intro a ha
    simp only [inc,List.mem_cons] at ha
    rcases ha with h|h
    · omega
    · exact prefixPositive hp a h

def Next (v : Variant) (ls rs : List Nat) : Prop :=
  ∃ t rs', 0<t ∧ Good rs' ∧ rs'≠[] ∧
    run0 (table v) t (C ls rs) = some (C [] rs')

theorem retreatGood (v : Variant) {ls : List Nat} (hc : Ctx ls)
    (k : Nat) (rs : List Nat) (hg : Good rs) : Next v ls ((k+3)::rs) := by
  obtain ⟨t,ht,hr⟩ := retreat v ls (ctxPositive hc) k rs
  refine ⟨t,2::ls.reverse++(k+1)::rs,ht,?_,by simp,hr⟩
  cases hc with
  | nil => exact Good.pair k rs hg
  | cons p hp =>
    simpa only [List.reverse_cons,List.cons_append,List.append_assoc,List.singleton_append] using
      prefixGood hp (2::(k+1)::rs) (Good.pair k rs hg)

theorem terminalGood (v : Variant) {ls rs : List Nat} (hc : Ctx ls)
    (n t0 : Nat) (h0 : run0 (table v) t0 (C ls rs) = some (C (inc (n+1) ls) [4])) :
    Next v ls rs := by
  obtain ⟨t,ht,hr⟩ := retreat v (inc (n+1) ls) (incPositive hc n) 1 []
  refine ⟨t0+t,2::(inc (n+1) ls).reverse++[2],by omega,?_,by simp,join0 h0 hr⟩
  cases hc with
  | nil => exact Good.pair n [2] Good.two
  | cons p hp =>
    have h : 2+(n+1)=n+3 := by omega
    simpa only [inc,h,List.reverse_cons,List.cons_append,List.append_assoc,List.singleton_append] using
      prefixGood hp [n+3,2] (Good.big n [2] Good.two)

theorem epoch (v : Variant) {rs : List Nat} (hg : Good rs) (hne : rs≠[])
    (ls : List Nat) (hc : Ctx ls) : Next v ls rs := by
  induction hg generalizing ls with
  | nil => contradiction
  | two => exact terminalGood v hc 0 9 (terminalSingle v ls)
  | big k rs hg ih => exact retreatGood v hc k rs hg
  | pair n rs hg ih =>
    cases rs with
    | nil => exact terminalGood v hc (n+1) (7*(n+1)+9) (terminalPair v ls n)
    | cons a rs =>
      cases a with
      | zero => cases hg
      | succ a =>
        obtain ⟨t,r',ht,hg',hne',hr⟩ := ih (by simp) (2::inc (n+2) ls) (ctxAdvance hc n)
        exact ⟨7*(n+1)+6+t,r',by omega,hg',hne',join0 (pairAdvance v ls n a rs) hr⟩

theorem entry (v : Variant) : run0 (table v) 7 ⟨0,[],[]⟩ = some (C [] [4]) := by
  cases v <;> rfl

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ n, ∃ t rs, n≤t ∧ Good rs ∧ rs≠[] ∧
      run0 (table v) t ⟨0,[],[]⟩ = some (C [] rs) := by
    intro n
    induction n with
    | zero => exact ⟨7,[4],by omega,Good.big 1 [] Good.nil,by simp,entry v⟩
    | succ n ih =>
      obtain ⟨t,rs,ht,hg,hne,hr⟩ := ih
      obtain ⟨t',rs',ht',hg',hne',hr'⟩ := epoch v hg hne [] Ctx.nil
      exact ⟨t+t',rs',by omega,hg',hne',join0 hr hr'⟩
  intro n
  obtain ⟨t,rs,ht,_,_,hr⟩ := arbitrary n
  have hz : (zrun (table v) t start).map project = some (C [] rs) :=
    (run_project (table v) t start).trans hr
  cases h : zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z h
    rw [start_embed,show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

namespace Leaf3535
abbrev table := A1LAUnaryGrammar.table .short
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  A1LAUnaryGrammar.never .short m hm
end Leaf3535
namespace Leaf3594
abbrev table := A1LAUnaryGrammar.table .longA
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  A1LAUnaryGrammar.never .longA m hm
end Leaf3594
namespace Leaf3595
abbrev table := A1LAUnaryGrammar.table .longD
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  A1LAUnaryGrammar.never .longD m hm
end Leaf3595

#print axioms epoch
#print axioms never
end BB6.Agent19Raw40.A1LAUnaryGrammar
