import SweepPumping
import ChampionRootBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48ThreeRF
open BB6Coverage BB6Coverage.Agent48Champion BB6Coverage.Agent31Pump

def rf : PartialMachine := fun s =>
  if s = (0,true) then some (some ⟨true,true,5⟩)
  else if s = (5,false) then some (some ⟨false,true,0⟩)
  else (championTable s).map some
abbrev a : List Bool := [true,false,false]
abbrev b : List Bool := [true,false,true,false,false]
abbrev c : List Bool := [true,true,true,false]
abbrev d : List Bool := [false,true,true,true,true]
abbrev e : List Bool := [true,true,true]
abbrev f : List Bool := [true,true,true,true,false,false,true,true,true]
abbrev g : List Bool := [false,true,false,false]
abbrev h : List Bool := [true,true,true,true,false]
def pad (n : Nat) := List.replicate n false

def cfg (n j k u v : Nat) : Z0 :=
  ⟨0,a++rep b j++a++List.replicate (6+3*n) true++c.reverse++pad u,
      e++rep d k++f++pad v⟩

theorem micro (L R : List Bool) :
    run0 rf 5 ⟨0,a++L,e++d++R⟩ = some ⟨0,a++b++L,e++R⟩ := by rfl

theorem walk (n j k u v : Nat) :
    run0 rf 5 (cfg n j (k+1) u v) = some (cfg n (j+1) k u v) := by
  have H := micro (rep b j++a++List.replicate (6+3*n) true++c.reverse++pad u) (rep d k++f++pad v)
  simpa only [cfg, rep, List.append_assoc] using H

theorem entry (L : List Bool) (v : Nat) :
    run0 rf 74 ⟨0,a++L,e++f++pad v⟩ = some ⟨4,g++b++L,[false,true,true,true,true,true,true,true,true,false,false,true,true,true]++pad (v-8)⟩ := by
  cases v with
  | zero => rfl
  | succ v => cases v with
    | zero => rfl
    | succ v => cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => cases v with
          | zero => rfl
          | succ v => cases v with
            | zero => rfl
            | succ v => cases v with
              | zero => rfl
              | succ v => cases v with
                | zero => rfl
                | succ v => rfl

theorem blocks (n : Nat) (L R : List Bool) :
    run0 rf (17*n) ⟨4,g++rep b n++L,false::R⟩ = some ⟨4,g++L,false::(rep h n++R)⟩ := by
  simpa using sweepL rf 4 g [false] b h 17 (by intro L R; rfl) n L R

theorem finish (L R : List Bool) :
    run0 rf 26 ⟨4,g++a++List.replicate 6 true++L,false::true::true::true::true::R⟩ =
      some ⟨0,a++a++List.replicate 9 true++L,e++R⟩ := by rfl

theorem blocks_to_right (n : Nat) (R : List Bool) :
    rep h n ++ [true,true,true,true,true,true,true,true,false,false,true,true,true] ++ R =
      [true,true,true,true] ++ rep d n ++ f ++ R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc] at *
    rw [ih]
    rfl

theorem reset (n u v : Nat) :
    run0 rf (117+17*n) (cfg n n 0 u v) = some (cfg (n+1) 0 (n+1) u (v-8)) := by
  have H1 := entry (rep b n++a++List.replicate (6+3*n) true++c.reverse++pad u) v
  have H2 := blocks (n+1) (a++List.replicate (6+3*n) true++c.reverse++pad u) ([true,true,true,true,true,true,true,true,false,false,true,true,true]++pad (v-8))
  have H12 := join0 H1 (by simpa only [rep,List.cons_append,List.nil_append,List.append_assoc] using H2)
  have H3 := finish (List.replicate (3*n) true++c.reverse++pad u) (false::(rep h n++[true,true,true,true,true,true,true,true,false,false,true,true,true]++pad (v-8)))
  have hL : List.replicate (6+3*n) true = List.replicate 6 true ++ List.replicate (3*n) true := by rw [← List.replicate_append_replicate]
  have H123 := join0 H12 (by simpa only [hL,rep,h,List.cons_append,List.nil_append,List.append_assoc] using H3)
  have eqcost : 74+17*(n+1)+26=117+17*n := by omega
  rw [eqcost] at H123
  have hOut : 9+3*n = 6+3*(n+1) := by omega
  have hR := blocks_to_right n (pad (v-8))
  simp only [cfg,rep,List.nil_append,List.append_assoc] at ⊢
  simp only [List.append_assoc] at H123
  rw [← hOut]
  rw [hL] at H123
  simp only [← List.append_assoc (List.replicate 9 true), List.replicate_append_replicate] at H123
  simp only [List.cons_append,List.nil_append,List.append_assoc] at hR
  simp only [a,b,d,e,f,g,h,List.cons_append,List.nil_append,List.append_assoc] at H123 ⊢
  rw [← hR]
  exact H123

/-- One full stage transfers all queued blocks, then grows the unary counter
    and the queue. -/
theorem transfer (n j k u v : Nat) :
    run0 rf (5*k) (cfg n j k u v) = some (cfg n (j+k) 0 u v) := by
  induction k generalizing j with
  | zero => simp [run0]
  | succ k ih =>
    have H := join0 (walk n j k u v) (ih (j+1))
    rw [show 5+5*k=5*(k+1) by omega, show j+1+k=j+(k+1) by omega] at H
    exact H

theorem stage (n u v : Nat) :
    run0 rf (117+22*n) (cfg n 0 n u v) = some (cfg (n+1) 0 (n+1) u (v-8)) := by
  have Ht := transfer n 0 n u v
  rw [Nat.zero_add] at Ht
  have H := join0 Ht (reset n u v)
  rwa [show 5*n+(117+17*n)=117+22*n by omega] at H

theorem initial : run0 rf 223 ⟨0,[],[]⟩ = some (cfg 0 0 0 0 0) := by decide

theorem arbitrary_live_prefix (k : Nat) : ∃ t n v, k ≤ t ∧ run0 rf t ⟨0,[],[]⟩ = some (cfg n 0 n 0 v) := by
  induction k with
  | zero => exact ⟨223,0,0,by decide,initial⟩
  | succ k ih =>
    obtain ⟨t,n,v,ht,hr⟩ := ih
    refine ⟨t+(117+22*n),n+1,v-8,by omega,join0 hr (stage n 0 v)⟩

theorem rf_never (m : Machine) (hm : compatible rf m) : NeverHalts m := by
  intro n
  obtain ⟨t,i,v,ht,hr⟩ := arbitrary_live_prefix n
  have hz : (Agent50Zipper.zrun rf t start).map project = some (cfg i 0 i 0 v) :=
    (run_project rf t start).trans hr
  cases h : Agent50Zipper.zrun rf t start with
  | none => simp [h] at hz
  | some z' =>
    have H := Agent50Zipper.zrun_sound rf m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem rf_cover : Cover NeverHalts rf := .leaf _ rf_never

#print axioms arbitrary_live_prefix
#print axioms stage
#print axioms rf_never
end BB6.Agent48ThreeRF
