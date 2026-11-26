import SweepPumping
import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw54.LA.Nested
open BB6Coverage BB6Coverage.Agent31Pump
inductive Variant where | m60 | m62 | m63 | m64 | m65 | m66
  deriving DecidableEq, Repr

def c1 : Variant → Move
  | .m60 => ⟨false,true,0⟩
  | .m62 => ⟨true,false,2⟩
  | .m63 => ⟨true,false,3⟩
  | .m64 => ⟨true,false,4⟩
  | .m65 => ⟨true,true,3⟩
  | .m66 => ⟨true,true,4⟩

def table (v : Variant) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (c1 v))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def toggle : Variant → Bool
  | .m65 | .m66 => true
  | _ => false

def suffix (v : Variant) (s : Bool) : List Bool :=
  if toggle v && s then [false,false,false,true,false,true]
  else [false,true,true,true,false,true]

def ones : List Bool := [true,true,true]
def zeros : List Bool := [false,false,false]
def word (v : Variant) (s : Bool) (n : Nat) : List Bool :=
  true :: (rep ones n ++ suffix v s)
def cfg (v : Variant) (s : Bool) (n : Nat) (L : List Bool) : Z0 :=
  ⟨0,L,word v s n⟩
def tailCost : Variant → Nat
  | .m63 | .m64 => 4
  | _ => 6

def Fill (v : Variant) (n : Nat) : Prop :=
  ∀ (s : Bool) (L : List Bool), ∃ (t : Nat) (s' : Bool), 0 < t ∧
    run0 (table v) t (cfg v s n (false::L)) = some (cfg v s' n (true::L))

theorem prep (v : Variant) (s : Bool) (n : Nat) (L : List Bool) :
    run0 (table v) (1+3*n+1+tailCost v) (cfg v s n (false::L)) =
      some (cfg v (if toggle v then !s else s) 0 (rep zeros n ++ true::L)) := by
  have h0 : run0 (table v) 1 (cfg v s n (false::L)) =
    some ⟨1,true::true::L,rep ones n ++ suffix v s⟩ := by rfl
  have h1 := sweepR (table v) 1 [true] [] ones zeros 3 (by intro X Y; rfl) n (true::L) (suffix v s)
  have h2 : run0 (table v) 1 ⟨1,true::(rep zeros n ++ true::L),suffix v s⟩ =
    some ⟨1,false::false::(rep zeros n ++ true::L),(suffix v s).tail⟩ := by
      cases v <;> cases s <;> rfl
  have h3 : run0 (table v) (tailCost v) ⟨1,false::false::(rep zeros n ++ true::L),(suffix v s).tail⟩ =
    some (cfg v (if toggle v then !s else s) 0 (rep zeros n ++ true::L)) := by
      cases v <;> cases s <;> rfl
  exact join0 (join0 (join0 h0 h1) h2) h3

theorem pop (v : Variant) (s : Bool) (n : Nat) (L : List Bool) :
    run0 (table v) 3 (cfg v s n (true::false::false::L)) =
      some (cfg v s (n+1) L) := by rfl

theorem drain (v : Variant) (N k j : Nat) (s : Bool) (L : List Bool)
    (allFill : ∀ i, i < N → Fill v i) (bound : j+k ≤ N) :
    ∃ (t : Nat) (s' : Bool),
      run0 (table v) t (cfg v s j (rep zeros k ++ L)) =
        some (cfg v s' (j+k) L) := by
  induction k generalizing j s with
  | zero => exact ⟨0,s,rfl⟩
  | succ k ih =>
    obtain ⟨u,s',hu,fill⟩ := allFill j (by omega) s (false::false::(rep zeros k ++ L))
    have h := join0 fill (pop v s' j (rep zeros k ++ L))
    obtain ⟨t,s'',ht⟩ := ih (j+1) s' (by omega)
    have h' := join0 h ht
    rw [show j+1+k=j+(k+1) by omega] at h'
    exact ⟨u+3+t,s'',h'⟩

theorem fill (v : Variant) (n : Nat) : Fill v n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s L
    obtain ⟨t,s',ht⟩ := drain v n n 0 (if toggle v then !s else s) (true::L) ih (by omega)
    rw [Nat.zero_add] at ht
    exact ⟨1+3*n+1+tailCost v+t,s',by omega,join0 (prep v s n L) ht⟩

theorem fillBlank (v : Variant) (n : Nat) (s : Bool) :
    ∃ (t : Nat) (s' : Bool), 0 < t ∧
      run0 (table v) t (cfg v s n []) = some (cfg v s' n [true]) := by
  obtain ⟨t,s',hp,h⟩ := fill v n s []
  cases t with
  | zero => omega
  | succ t => exact ⟨t+1,s',by omega,h⟩

theorem sectionReturn (v : Variant) (n : Nat) (s : Bool) :
    ∃ (t : Nat) (s' : Bool), 0 < t ∧
      run0 (table v) t (cfg v s n []) = some (cfg v s' (n+1) []) := by
  obtain ⟨t,s',hp,h⟩ := fillBlank v n s
  have h' : run0 (table v) 3 (cfg v s' n [true]) =
      some (cfg v s' (n+1) []) := by rfl
  exact ⟨t+3,s',by omega,join0 h h'⟩

def entryCost : Variant → Nat
  | .m63 | .m64 => 27
  | _ => 29

theorem entry (v : Variant) :
    run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (cfg v (toggle v) 1 []) := by
  cases v <;> rfl

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply BB6.Agent8Raw54.RAClosed.neverOfSection (table v) (Nat × Bool)
    (fun w => cfg v w.2 w.1 []) (1,toggle v) (entryCost v) (entry v) _ m hm
  intro w
  obtain ⟨t,s',hp,h⟩ := sectionReturn v w.1 w.2
  exact ⟨t,(w.1+1,s'),hp,h⟩

#print axioms fill
#print axioms sectionReturn
#print axioms entry
#print axioms never
end BB6.Agent8Raw54.LA.Nested
