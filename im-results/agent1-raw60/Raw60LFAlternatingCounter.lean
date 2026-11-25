import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFAlternatingCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
abbrev A := Q 0
abbrev D := Q 3
abbrev Z (n : Nat) := List.replicate n false

def V : Nat → List Bool
  | 0 => [false,false]
  | n+1 => false::true::false::true::V n
abbrev W (n : Nat) := false::false::true::V n

theorem zeroMerge (a b : Nat) (R : List Bool) : Z a++(Z b++R)=Z (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem sweepA (n : Nat) (L R : List Bool) :
    run0 table (8*n) (A (V n++L) (true::R)) = some (A (false::false::L) (true::(Z (4*n)++R))) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 8 (A (V (n+1)++L) (true::R)) = some (A (V n++L) (true::(Z 4++R))) := by rfl
    have H := join0 h (ih (Z 4++R))
    rw [zeroMerge,show 4*n+4=4*(n+1) by omega,show 8+8*n=8*(n+1) by omega] at H
    exact H

def Fill (n : Nat) : Prop := ∀ (b : Bool) (L R : List Bool),
  Reach table (D (W n++L) (false::false::false::b::R))
    (D (b::false::true::(V (n+1)++L)) R)

theorem clear (n : Nat) (b : Bool) (L R : List Bool) :
    Reach table (D (W (n+1)++L) (false::false::false::b::R))
      (D (W 0++L) (Z (4*n+3)++true::false::false::false::b::R)) := by
  have h1 : run0 table 21 (D (W (n+1)++L) (false::false::false::b::R)) = some (A (V (n+1)++L) (true::false::true::false::false::false::b::R)) := by rfl
  have h2 := sweepA (n+1) L (false::true::false::false::false::b::R)
  have he : Z (4*(n+1))++false::true::false::false::false::b::R =
      false::false::(Z (4*n+3)++true::false::false::false::b::R) := by
    rw [show 4*(n+1)=4*n+4 by omega]
    change Z (4*n+4)++(Z 1++true::false::false::false::b::R)=_
    rw [zeroMerge]
    rfl
  rw [he] at h2
  have h3 : run0 table 7 (A (false::false::L) (true::false::false::(Z (4*n+3)++true::false::false::false::b::R))) = some (D (W 0++L) (Z (4*n+3)++true::false::false::false::b::R)) := by rfl
  exact ⟨_,join0 (join0 h1 h2) h3⟩

theorem chain (d j : Nat) (L R : List Bool) (h : ∀ i, j≤i → i<j+d → Fill i) :
    Reach table (D (W j++L) (Z (4*d)++R)) (D (W (j+d)++L) R) := by
  induction d generalizing j with
  | zero => exact ⟨0,by rfl⟩
  | succ d ih =>
    have h1 := h j (by omega) (by omega) false L (Z (4*d)++R)
    have h2 := ih (j+1) (fun i hi hi' => h i (by omega) (by omega))
    rw [show j+1+d=j+(d+1) by omega] at h2
    exact reachTrans h1 h2

theorem fill (n : Nat) : Fill n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b L R
    cases n with
    | zero => exact ⟨32,by rfl⟩
    | succ n =>
      have h1 := clear n b L R
      have he : Z (4*n+3)++true::false::false::false::b::R = Z (4*n)++false::false::false::true::false::false::false::b::R := by
        change Z (4*n+3)++true::false::false::false::b::R=Z (4*n)++(Z 3++true::false::false::false::b::R)
        rw [zeroMerge]
      rw [he] at h1
      have h2 := chain n 0 L (false::false::false::true::false::false::false::b::R) (fun i _ hi => ih i (by omega))
      rw [Nat.zero_add] at h2
      have h3 := ih n (by omega) true L (false::false::false::b::R)
      have h4 : run0 table 4 (D (true::false::true::(V (n+1)++L)) (false::false::false::b::R)) = some (D (b::false::true::(V (n+2)++L)) R) := by rfl
      exact reachTrans h1 (reachTrans h2 (reachTrans h3 ⟨4,h4⟩))

-- At a blank right edge the same induction uses implicit zero padding.
theorem clearBlank (n : Nat) (L : List Bool) :
    Reach table (D (W (n+1)++L) []) (D (W 0++L) (Z (4*n+3)++[true,false])) := by
  have h1 : run0 table 21 (D (W (n+1)++L) []) = some (A (V (n+1)++L) [true,false,true,false]) := by rfl
  have h2 := sweepA (n+1) L [false,true,false]
  have he : Z (4*(n+1))++[false,true,false] = false::false::(Z (4*n+3)++[true,false]) := by
    rw [show 4*(n+1)=4*n+4 by omega]
    change Z (4*n+4)++(Z 1++[true,false])=_
    rw [zeroMerge]
    rfl
  rw [he] at h2
  have h3 : run0 table 7 (A (false::false::L) (true::false::false::(Z (4*n+3)++[true,false]))) = some (D (W 0++L) (Z (4*n+3)++[true,false])) := by rfl
  exact ⟨_,join0 (join0 h1 h2) h3⟩

def family (n : Nat) := D (W (n+1)) []
theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h1 := clearBlank n []
  simp only [List.append_nil] at h1
  have he : Z (4*n+3)++[true,false] = Z (4*n)++[false,false,false,true,false] := by
    change Z (4*n+3)++[true,false]=Z (4*n)++(Z 3++[true,false])
    rw [zeroMerge]
  rw [he] at h1
  have h2 := chain n 0 [] [false,false,false,true,false] (fun i _ _ => fill i)
  simp only [Nat.zero_add,List.append_nil] at h2
  have h3 := fill n true [] [false]
  simp only [List.append_nil] at h3
  have h4 : run0 table 4 (D (true::false::true::V (n+1)) [false]) = some (family (n+1)) := by rfl
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  obtain ⟨c,hc⟩ := h3
  exact ⟨a+b+c+4,by omega,join0 (join0 (join0 ha hb) hc) h4⟩
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 22 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFAlternatingCounter
