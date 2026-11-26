import Lean
import SparseZipper
import FastThreeHoleAudit

namespace BB6Coverage.Agent3E0LFSweep
open BB6Coverage BB6Coverage.Agent50Zipper

/-- The exact original one-hole tables, with B1=19 or 21. -/
def table (alt : Bool) : PartialMachine :=
  FAR.fromCodes [7,10,11,(if alt then 21 else 19),14,17,24,16,20,11,3,0]

/-- A/C omit a known nearest left 1. E/Z omit a known nearest right 0.
Z additionally omits a known nearest left 0. -/
inductive Phase where
  | a | c | e | z
  deriving DecidableEq, Repr

def cfg (q : Phase) (h : Int) (l r : List Bool) : Z :=
  match q with
  | .a => ⟨0,h,r.headD false::true::l,r.tail⟩
  | .c => ⟨2,h,r.headD false::true::l,r.tail⟩
  | .e => ⟨4,h-1,l,false::r⟩
  | .z => ⟨4,h-1,false::l,false::r⟩

def off : Phase → Int
  | .e => 0
  | _ => 1

structure Rule where
  q : Phase
  u : List Bool
  v : List Bool
  q' : Phase
  x : List Bool
  y : List Bool
  cost : Nat
  deriving DecidableEq, Repr

def common : List Rule := [
  ⟨.a,[],[false,false],.c,[true,true],[],2⟩,
  ⟨.a,[],[true],.c,[false],[],3⟩,
  ⟨.c,[],[true,true],.c,[false,true],[],2⟩,
  ⟨.c,[],[true,false],.a,[true],[false],3⟩,
  ⟨.c,[],[false],.e,[],[true],2⟩,
  ⟨.e,[true],[],.e,[],[true],3⟩,
  ⟨.e,[false,false],[],.a,[],[false,false],2⟩,
  ⟨.e,[false,true,false],[],.e,[],[true,true,false],9⟩,
  ⟨.e,[false,true,true,true],[],.z,[],[true,false,false],7⟩,
  ⟨.e,[false,true,true,false,true],[],.e,[],[true,true,false,false,false],5⟩,
  ⟨.z,[false],[],.a,[],[false,false],2⟩,
  ⟨.z,[true,false],[],.e,[],[true,true,false],9⟩,
  ⟨.z,[true,true,true],[],.z,[],[true,false,false],7⟩,
  ⟨.z,[true,true,false,true],[],.e,[],[true,true,false,false,false],5⟩]

def rules (alt : Bool) : List Rule := common ++ if alt then [
  ⟨.a,[],[false,true,true],.c,[true,true,true],[],5⟩,
  ⟨.a,[],[false,true,false],.a,[false,true,true],[],3⟩]
  else [
  ⟨.a,[],[false,true,true],.c,[true,true,true],[],3⟩,
  ⟨.a,[],[false,true,false],.e,[false],[true,false],9⟩]

def input (r : Rule) (h : Int) (l t : List Bool) : Z :=
  cfg r.q h (r.u++l) (r.v++t)

def output (r : Rule) (h : Int) (l t : List Bool) : Z :=
  cfg r.q' (h+(r.x.length:Int)-(r.u.length:Int)+off r.q'-off r.q) (r.x++l) (r.y++t)

private theorem rule_zero (alt : Bool) (r : Rule) (hr : r ∈ rules alt) (l t : List Bool) :
    zrun (table alt) r.cost (input r 0 l t) = some (output r 0 l t) := by
  cases alt <;> simp [rules,common] at hr
  all_goals rcases hr with (hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr) <;> subst r <;> rfl

theorem cfg_shift (q : Phase) (h a : Int) (l r : List Bool) :
    cfg q (h+a) l r = shift a (cfg q h l r) := by
  cases q <;> simp [cfg,shift] <;> omega

theorem rule_exact (alt : Bool) (r : Rule) (hr : r ∈ rules alt) (h : Int) (l t : List Bool) :
    zrun (table alt) r.cost (input r h l t) = some (output r h l t) := by
  have H := zrun_shift (table alt) h r.cost (input r 0 l t)
  rw [rule_zero alt r hr l t] at H
  simp only [input,output,Int.zero_add,Option.map_some] at H ⊢
  rw [← cfg_shift, ← cfg_shift] at H
  simpa only [Int.zero_add,show (r.x.length:Int)-(r.u.length:Int)+off r.q'-off r.q+h = h+(r.x.length:Int)-(r.u.length:Int)+off r.q'-off r.q by omega] using H

theorem positive (alt : Bool) (r : Rule) (hr : r ∈ rules alt) : 0 < r.cost := by
  cases alt <;> simp [rules,common] at hr
  all_goals rcases hr with (hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr) <;> subst r <;> decide

/-- Both bad patterns are the same physical E excursion, with or without its
pending left zero represented in the finite control. -/
inductive Bad : Phase → List Bool → List Bool → Prop
  | e (l r : List Bool) : Bad .e ([false,true,true,false,false]++l) r
  | z (l r : List Bool) : Bad .z ([true,true,false,false]++l) r

/-- Each bad pattern reaches the D0 hole in four known primitive steps. -/
theorem bad_hit (alt : Bool) (q : Phase) (h : Int) (l r : List Bool)
    (hb : Bad q l r) :
    ∃ z' : Z, zrun (table alt) 4 (cfg q h l r) = some z' ∧ z'.q = 3 ∧ z'.l.headD false = false := by
  cases hb <;> cases alt <;> exact ⟨_,rfl,rfl,rfl⟩

def Applicable (alt : Bool) (q : Phase) (l r : List Bool) : Prop :=
  ∃ rule ∈ rules alt, rule.q = q ∧ ∃ lt rt, l = rule.u ++ lt ∧ r = rule.v ++ rt

private theorem covered (alt : Bool) (q : Phase) (a b c d e f g i : Bool) (l r : List Bool) :
    Applicable alt q (a::b::c::d::e::l) (f::g::i::r) ∨ Bad q (a::b::c::d::e::l) (f::g::i::r) := by
  cases q with
  | a =>
    cases f with
    | false =>
      cases g with
      | false =>
        left; exact ⟨⟨.a,[],[false,false],.c,[true,true],[],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true =>
        cases i with
        | false =>
          cases alt
          · left; exact ⟨⟨.a,[],[false,true,false],.e,[false],[true,false],9⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
          · left; exact ⟨⟨.a,[],[false,true,false],.a,[false,true,true],[],3⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
        | true =>
          cases alt
          · left; exact ⟨⟨.a,[],[false,true,true],.c,[true,true,true],[],3⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
          · left; exact ⟨⟨.a,[],[false,true,true],.c,[true,true,true],[],5⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
    | true =>
      left; exact ⟨⟨.a,[],[true],.c,[false],[],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
  | c =>
    cases f with
    | false =>
      left; exact ⟨⟨.c,[],[false],.e,[],[true],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
    | true =>
      cases g with
      | false =>
        left; exact ⟨⟨.c,[],[true,false],.a,[true],[false],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true =>
        left; exact ⟨⟨.c,[],[true,true],.c,[false,true],[],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
  | e =>
    cases a with
    | false =>
      cases b with
      | false =>
        left; exact ⟨⟨.e,[false,false],[],.a,[],[false,false],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true =>
        cases c with
        | false =>
          left; exact ⟨⟨.e,[false,true,false],[],.e,[],[true,true,false],9⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
        | true =>
          cases d with
          | false =>
            cases e with
            | false =>
              exact Or.inr (Bad.e _ _)
            | true =>
              left; exact ⟨⟨.e,[false,true,true,false,true],[],.e,[],[true,true,false,false,false],5⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
          | true =>
            left; exact ⟨⟨.e,[false,true,true,true],[],.z,[],[true,false,false],7⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
    | true =>
      left; exact ⟨⟨.e,[true],[],.e,[],[true],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
  | z =>
    cases a with
    | false =>
      left; exact ⟨⟨.z,[false],[],.a,[],[false,false],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
    | true =>
      cases b with
      | false =>
        left; exact ⟨⟨.z,[true,false],[],.e,[],[true,true,false],9⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true =>
        cases c with
        | false =>
          cases d with
          | false =>
            exact Or.inr (Bad.z _ _)
          | true =>
            left; exact ⟨⟨.z,[true,true,false,true],[],.e,[],[true,true,false,false,false],5⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
        | true =>
          left; exact ⟨⟨.z,[true,true,true],[],.z,[],[true,false,false],7⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩

private theorem padFive (l : List Bool) :
    ∃ a b c d e t, l ++ [false,false,false,false,false] = a::b::c::d::e::t := by
  cases l with
  | nil => exact ⟨false,false,false,false,false,[],rfl⟩
  | cons a l => cases l with
    | nil => exact ⟨a,false,false,false,false,[false],rfl⟩
    | cons b l => cases l with
      | nil => exact ⟨a,b,false,false,false,[false,false],rfl⟩
      | cons c l => cases l with
        | nil => exact ⟨a,b,c,false,false,[false,false,false],rfl⟩
        | cons d l => cases l with
          | nil => exact ⟨a,b,c,d,false,[false,false,false,false],rfl⟩
          | cons e t => exact ⟨a,b,c,d,e,t++[false,false,false,false,false],rfl⟩

private theorem padThree (l : List Bool) :
    ∃ a b c t, l ++ [false,false,false] = a::b::c::t := by
  cases l with
  | nil => exact ⟨false,false,false,[],rfl⟩
  | cons a l => cases l with
    | nil => exact ⟨a,false,false,[false],rfl⟩
    | cons b l => cases l with
      | nil => exact ⟨a,b,false,[false,false],rfl⟩
      | cons c t => exact ⟨a,b,c,t++[false,false,false],rfl⟩

theorem cover_padded (alt : Bool) (q : Phase) (l r : List Bool) :
    Applicable alt q (l++[false,false,false,false,false]) (r++[false,false,false]) ∨
    Bad q (l++[false,false,false,false,false]) (r++[false,false,false]) := by
  obtain ⟨a,b,c,d,e,t,hl⟩ := padFive l
  obtain ⟨f,g,i,u,hr⟩ := padThree r
  rw [hl,hr]
  exact covered alt q a b c d e f g i t u

private theorem getD_pad (l : List Bool) (k n : Nat) :
    (l ++ List.replicate k false).getD n false = l.getD n false := by
  induction l generalizing n with
  | nil =>
    simp only [List.nil_append,List.getD_eq_getElem?_getD,List.getElem?_replicate]
    split <;> rfl
  | cons a l ih => cases n with
    | zero => rfl
    | succ n => exact ih n

private theorem padZL (z : Z) (k : Nat) :
    embed {z with l := z.l ++ List.replicate k false} = embed z := by
  simp only [embed]
  congr 1
  funext x
  simp only [atCell]
  split <;> try rfl
  exact getD_pad _ _ _

private theorem padZR (z : Z) (k : Nat) :
    embed {z with r := z.r ++ List.replicate k false} = embed z := by
  simp only [embed]
  congr 1
  funext x
  simp only [atCell]
  split <;> try rfl
  exact getD_pad _ _ _

theorem padL (q : Phase) (h : Int) (l r : List Bool) :
    embed (cfg q h (l++[false,false,false,false,false]) r) = embed (cfg q h l r) := by
  cases q with
  | a => exact padZL (cfg .a h l r) 5
  | c => exact padZL (cfg .c h l r) 5
  | e => exact padZL (cfg .e h l r) 5
  | z => exact padZL (cfg .z h l r) 5

theorem padR (q : Phase) (h : Int) (l r : List Bool) :
    embed (cfg q h l (r++[false,false,false])) = embed (cfg q h l r) := by
  cases q with
  | a => cases r with
    | nil => exact padZR (cfg .a h l []) 2
    | cons b r => exact padZR (cfg .a h l (b::r)) 3
  | c => cases r with
    | nil => exact padZR (cfg .c h l []) 2
    | cons b r => exact padZR (cfg .c h l (b::r)) 3
  | e => exact padZR (cfg .e h l r) 3
  | z => exact padZR (cfg .z h l r) 3

/-- Exact authentic blank entry.  The finite zipper has some harmless trailing
zero padding, so the statement is at the level of physical configurations. -/
theorem seed_run (alt : Bool) (m : Machine) (hm : compatible (table alt) m) :
    run m 9 blank = some (embed (cfg .a (-1) [] [false,false,true,true])) := by
  have hz : embed (⟨0,0,[],[]⟩ : Z) = blank := by
    unfold embed blank
    congr 1
    funext x
    simp [atCell]
  have hs : zrun (table alt) 9 ⟨0,0,[],[]⟩ = some (cfg .a (-1) [] [false,false,true,true]) := by
    cases alt <;> rfl
  rw [←hz]
  exact zrun_sound _ _ hm _ _ _ hs

/-- A sweep invariant gives a universal source-level nonhalting proof for all
25 completions of the D0 hole.  No bound on the stack lengths or the number
of macro steps appears in this interface. -/
structure Stable (alt : Bool) (I : Phase → List Bool → List Bool → Prop) : Prop where
  start : I .a [] [false,false,true,true]
  padding : ∀ q l r, I q l r → I q (l++[false,false,false,false,false]) (r++[false,false,false])
  safe : ∀ q l r, I q l r → ¬ Bad q l r
  closed : ∀ rule ∈ rules alt, ∀ l r, I rule.q (rule.u++l) (rule.v++r) → I rule.q' (rule.x++l) (rule.y++r)

theorem stable_advance {alt : Bool} {I : Phase → List Bool → List Bool → Prop}
    (s : Stable alt I) (m : Machine) (hm : compatible (table alt) m)
    (q : Phase) (h : Int) (l r : List Bool) (hi : I q l r) :
    ∃ n q' h' l' r', 0 < n ∧ run m n (embed (cfg q h l r)) = some (embed (cfg q' h' l' r')) ∧ I q' l' r' := by
  have hp := s.padding q l r hi
  rcases cover_padded alt q l r with hc | hb
  · obtain ⟨rule,hr,hq,lt,rt,hl,hr'⟩ := hc
    have hi' : I rule.q (rule.u++lt) (rule.v++rt) := by simpa only [hq,←hl,←hr'] using hp
    have hs := zrun_sound (table alt) m hm rule.cost _ _ (rule_exact alt rule hr h lt rt)
    refine ⟨rule.cost,rule.q',h+(rule.x.length:Int)-(rule.u.length:Int)+off rule.q'-off rule.q,rule.x++lt,rule.y++rt,positive alt rule hr,?_,s.closed rule hr lt rt hi'⟩
    unfold input output at hs
    rw [hq,←hl,←hr',padL,padR] at hs
    simpa only [hq] using hs
  · exact False.elim (s.safe _ _ _ hp hb)

theorem stable_never {alt : Bool} {I : Phase → List Bool → List Bool → Prop}
    (s : Stable alt I) (m : Machine) (hm : compatible (table alt) m) : NeverHalts m := by
  have H : ∀ n : Nat, ∃ t q h l r, n ≤ t ∧ run m t blank = some (embed (cfg q h l r)) ∧ I q l r := by
    intro n
    induction n with
    | zero => exact ⟨9,.a,-1,[],[false,false,true,true],by omega,seed_run alt m hm,s.start⟩
    | succ n ih =>
      obtain ⟨t,q,h,l,r,ht,hr,hi⟩ := ih
      obtain ⟨k,q',h',l',r',hk,hkRun,hi'⟩ := stable_advance s m hm q h l r hi
      refine ⟨t+k,q',h',l',r',by omega,?_,hi'⟩
      rw [run_append,hr]; exact hkRun
  intro n
  obtain ⟨t,q,h,l,r,ht,hr,hi⟩ := H n
  rw [show t=n+(t-n) by omega,run_append] at hr
  cases he : run m n blank with
  | none =>
    have he' : run m n (emptyAt 0) = none := he
    simp [he'] at hr
  | some c => rfl

#print axioms bad_hit
#print axioms rule_exact
#print axioms cover_padded
#print axioms seed_run
#print axioms stable_never
end BB6Coverage.Agent3E0LFSweep
