import E0LFExcursion
import Lean

namespace BB6Coverage.Agent3E0LFMacro
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent3E0LFExcursion

inductive Phase where
  | a | c | e
  deriving DecidableEq, Repr

/-- Boundary h lies immediately before the right list. In E phase the head
is one cell left of this boundary; in A/C it is at the boundary. -/
def cfg (q : Phase) (h : Int) (l r : List Bool) : Z :=
  match q with
  | .a => ⟨0,h,r.headD false::l,r.tail⟩
  | .c => ⟨2,h,r.headD false::l,r.tail⟩
  | .e => ⟨4,h-1,l,r⟩

structure Rule where
  q : Phase
  u : List Bool -- nearest cell first
  v : List Bool
  q' : Phase
  x : List Bool -- nearest cell first
  y : List Bool
  steps : Nat
  deriving DecidableEq, Repr

def common : List Rule := [
  ⟨.a,[true],[true],.c,[true,false],[],3⟩,
  ⟨.a,[false,true],[true],.e,[],[false,true,true],3⟩,
  ⟨.a,[],[false,false],.c,[true,true],[],2⟩,
  ⟨.c,[],[true,true],.c,[true,false],[],2⟩,
  ⟨.c,[],[true,false],.a,[true],[false],3⟩,
  ⟨.c,[true],[false],.e,[],[false,true],2⟩,
  ⟨.e,[true],[false],.e,[],[false,true],3⟩,
  ⟨.e,[false,false],[false],.a,[true],[false,false],2⟩,
  ⟨.e,[false,true,false],[false],.a,[],[false,false,false,false],2⟩,
  ⟨.e,[false,true,true],[false],.a,[],[true,false,false,false],2⟩]

def rules (alt : Bool) : List Rule := common ++ if alt then [
  ⟨.a,[],[false,true,false],.a,[true,false,true],[],3⟩,
  ⟨.a,[],[false,true,true],.a,[true],[false,false],3⟩]
  else [
  ⟨.a,[],[false,true,false],.a,[],[true,false,false],4⟩,
  ⟨.a,[],[false,true,true],.c,[true,true,true],[],3⟩]

def runRule (r : Rule) (h : Int) (l rtail : List Bool) : Z :=
  cfg r.q h (r.u ++ l) (r.v ++ rtail)
def outRule (r : Rule) (h : Int) (l rtail : List Bool) : Z :=
  cfg r.q' (h + (r.x.length : Int) - (r.u.length : Int)) (r.x ++ l) (r.y ++ rtail)

theorem rule_zero (alt : Bool) (r : Rule) (hr : r ∈ rules alt) (l rt : List Bool) :
    zrun (table alt) r.steps (runRule r 0 l rt) = some (outRule r 0 l rt) := by
  cases alt <;> simp [rules,common] at hr
  all_goals rcases hr with (hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr) <;> subst r <;> rfl

theorem cfg_shift (q : Phase) (h a : Int) (l r : List Bool) :
    cfg q (h+a) l r = shift a (cfg q h l r) := by
  cases q <;> simp [cfg,shift] <;> omega

theorem rule_exact (alt : Bool) (r : Rule) (hr : r ∈ rules alt) (h : Int) (l rt : List Bool) :
    zrun (table alt) r.steps (runRule r h l rt) = some (outRule r h l rt) := by
  have H := zrun_shift (table alt) h r.steps (runRule r 0 l rt)
  rw [rule_zero alt r hr l rt] at H
  simp only [runRule,outRule,Int.zero_add,Option.map_some] at H ⊢
  rw [← cfg_shift, ← cfg_shift] at H
  simpa only [Int.zero_add,show (r.x.length : Int) - (r.u.length : Int) + h = h + (r.x.length : Int) - (r.u.length : Int) by omega] using H

theorem positive (alt : Bool) (r : Rule) (hr : r ∈ rules alt) : 0 < r.steps := by
  cases alt <;> simp [rules,common] at hr
  all_goals rcases hr with (hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr|hr) <;> subst r <;> decide

/-- The two genuine unsafe local patterns reach D0, without querying it. -/
theorem a_bad (alt : Bool) (h : Int) (l rt : List Bool) :
    zrun (table alt) 2 (cfg .a h (false::false::l) (true::rt)) =
      some ⟨3,h-1-1,false::l,[true,true]++rt⟩ := by rfl

theorem c_bad (alt : Bool) (h : Int) (l rt : List Bool) :
    zrun (table alt) 1 (cfg .c h (false::l) (false::rt)) =
      some ⟨3,h-1,false::l,true::rt⟩ := by rfl

inductive Bad : Phase → List Bool → List Bool → Prop
  | a (l r : List Bool) : Bad .a (false::false::l) (true::r)
  | c (l r : List Bool) : Bad .c (false::l) (false::r)
  | e (l r : List Bool) : Bad .e l (true::r)

def Applicable (alt : Bool) (q : Phase) (l r : List Bool) : Prop :=
  ∃ rule ∈ rules alt, rule.q = q ∧ ∃ lt rt, l = rule.u ++ lt ∧ r = rule.v ++ rt

private theorem covered (alt : Bool) (q : Phase) (a b c d e f : Bool) (l rt : List Bool) :
    Applicable alt q (a::b::c::l) (d::e::f::rt) ∨ Bad q (a::b::c::l) (d::e::f::rt) := by
  cases q with
  | a =>
    cases d with
    | false =>
      cases e with
      | false =>
        left
        exact ⟨⟨.a,[],[false,false],.c,[true,true],[],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true =>
        cases f <;> cases alt
        · left; exact ⟨⟨.a,[],[false,true,false],.a,[],[true,false,false],4⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
        · left; exact ⟨⟨.a,[],[false,true,false],.a,[true,false,true],[],3⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
        · left; exact ⟨⟨.a,[],[false,true,true],.c,[true,true,true],[],3⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
        · left; exact ⟨⟨.a,[],[false,true,true],.a,[true],[false,false],3⟩,by simp [rules,common],rfl,_,_,rfl,rfl⟩
    | true =>
      cases a with
      | false =>
        cases b with
        | false => exact Or.inr (Bad.a _ _)
        | true => left; exact ⟨⟨.a,[false,true],[true],.e,[],[false,true,true],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true => left; exact ⟨⟨.a,[true],[true],.c,[true,false],[],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
  | c =>
    cases d with
    | false =>
      cases a with
      | false => exact Or.inr (Bad.c _ _)
      | true => left; exact ⟨⟨.c,[true],[false],.e,[],[false,true],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
    | true =>
      cases e with
      | false => left; exact ⟨⟨.c,[],[true,false],.a,[true],[false],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | true => left; exact ⟨⟨.c,[],[true,true],.c,[true,false],[],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
  | e =>
    cases d with
    | true => exact Or.inr (Bad.e _ _)
    | false =>
      cases a with
      | true => left; exact ⟨⟨.e,[true],[false],.e,[],[false,true],3⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
      | false =>
        cases b with
        | false => left; exact ⟨⟨.e,[false,false],[false],.a,[true],[false,false],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
        | true =>
          cases c with
          | false => left; exact ⟨⟨.e,[false,true,false],[false],.a,[],[false,false,false,false],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩
          | true => left; exact ⟨⟨.e,[false,true,true],[false],.a,[],[true,false,false,false],2⟩,by cases alt <;> simp [rules,common],rfl,_,_,rfl,rfl⟩

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
    Applicable alt q (l++[false,false,false]) (r++[false,false,false]) ∨
    Bad q (l++[false,false,false]) (r++[false,false,false]) := by
  obtain ⟨a,b,c,t,hl⟩ := padThree l
  obtain ⟨d,e,f,u,hr⟩ := padThree r
  rw [hl,hr]
  exact covered alt q a b c d e f t u

private theorem getD_pad (l : List Bool) (n : Nat) :
    (l ++ [false,false,false]).getD n false = l.getD n false := by
  induction l generalizing n with
  | nil => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => cases n <;> rfl
  | cons a l ih => cases n with
    | zero => rfl
    | succ n => exact ih n

theorem padL (q : Phase) (h : Int) (l r : List Bool) :
    embed (cfg q h (l++[false,false,false]) r) = embed (cfg q h l r) := by
  cases q <;> simp only [cfg,embed]
  all_goals congr 1
  all_goals funext x
  all_goals simp only [atCell]
  all_goals split <;> try rfl
  · cases (h-x).toNat with
    | zero => rfl
    | succ n => exact getD_pad l n
  · cases (h-x).toNat with
    | zero => rfl
    | succ n => exact getD_pad l n
  · exact getD_pad l _

theorem padR (q : Phase) (h : Int) (l r : List Bool) :
    embed (cfg q h l (r++[false,false,false])) = embed (cfg q h l r) := by
  cases q <;> simp only [cfg,embed]
  all_goals congr 1
  all_goals funext x
  all_goals simp only [atCell]
  all_goals split
  · cases r <;> rfl
  · cases r with
    | nil => change ([false,false] : List Bool).getD _ false = false; cases (x-h-1).toNat with
      | zero => rfl
      | succ n => cases n <;> rfl
    | cons a r => exact getD_pad r _
  · cases r <;> rfl
  · cases r with
    | nil => change ([false,false] : List Bool).getD _ false = false; cases (x-h-1).toNat with
      | zero => rfl
      | succ n => cases n <;> rfl
    | cons a r => exact getD_pad r _
  · rfl
  · exact getD_pad r _

/-- Any invariant closed under exact macro rules and external blank padding,
excluding the two hole patterns and the invalid E-boundary, certifies nonhalting. -/
structure Stable (alt : Bool) (I : Phase → List Bool → List Bool → Prop) : Prop where
  start : I .a [] []
  padding : ∀ q l r, I q l r → I q (l++[false,false,false]) (r++[false,false,false])
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
    have hs := zrun_sound (table alt) m hm rule.steps _ _ (rule_exact alt rule hr h lt rt)
    refine ⟨rule.steps,rule.q',h+(rule.x.length:Int)-(rule.u.length:Int),rule.x++lt,rule.y++rt,positive alt rule hr,?_,s.closed rule hr lt rt hi'⟩
    unfold runRule outRule at hs
    rw [hq,←hl,←hr',padL,padR] at hs
    exact hs
  · exact False.elim (s.safe _ _ _ hp hb)

theorem stable_never {alt : Bool} {I : Phase → List Bool → List Bool → Prop}
    (s : Stable alt I) (m : Machine) (hm : compatible (table alt) m) : NeverHalts m := by
  have init : embed (cfg .a 0 [] []) = blank := by
    unfold cfg embed blank
    congr 1
    funext x
    simp [atCell]
    intro hx
    cases (-x).toNat <;> rfl
  have H : ∀ n : Nat, ∃ t q h l r, n ≤ t ∧ run m t blank = some (embed (cfg q h l r)) ∧ I q l r := by
    intro n
    induction n with
    | zero => exact ⟨0,.a,0,[],[],by omega,by rw [←init];rfl,s.start⟩
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

#print axioms stable_never
#print axioms rule_exact
#print axioms positive
#print axioms a_bad
#print axioms c_bad
end BB6Coverage.Agent3E0LFMacro
