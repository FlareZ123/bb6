import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LA105
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def X (n : Nat) := rep [false,true] n
def I (n : Nat) := rep [true,true] n
def Z (n : Nat) := List.replicate n false
def O (n : Nat) := List.replicate n true
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def C (L W : List Bool) : Z0 := ⟨2,W.headD false::L,W.tail⟩

inductive Left : List Bool → Prop where
  | nil : Left []
  | single : Left [true]
  | zeroPair (L : List Bool) : Left L → Left (false::false::L)
  | onePair (b : Bool) (L : List Bool) : Left L → Left (true::b::L)

inductive LiveLeft : List Bool → Prop where
  | single : LiveLeft [true]
  | onePair (b : Bool) (L : List Bool) : Left L → LiveLeft (true::b::L)
  | zeroPair (L : List Bool) : LiveLeft L → LiveLeft (false::false::L)

theorem liveLeft (L : List Bool) (h : LiveLeft L) : Left L := by
  induction h with
  | single => exact Left.single
  | onePair b L h => exact Left.onePair b L h
  | zeroPair L h ih => exact Left.zeroPair L ih

theorem decompose (L : List Bool) (h : LiveLeft L) :
    ∃ k T, L = Z (2*k) ++ true::T ∧ Left (true::T) := by
  induction h with
  | single => exact ⟨0,[],rfl,Left.single⟩
  | onePair b L h => exact ⟨0,b::L,rfl,Left.onePair b L h⟩
  | zeroPair L h ih =>
    obtain ⟨k,T,rfl,hT⟩ := ih
    exact ⟨k+1,T,rfl,hT⟩

inductive Rest : List Bool → Prop where
  | ones (n : Nat) : Rest (I n)
  | odd (n : Nat) : Rest (false::true::I (n+1))
  | double (R : List Bool) : Rest R → Rest (false::true::false::true::R)

theorem prefixRest (k n : Nat) :
    Rest (X k ++ I (n+1)) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => exact Rest.ones (n+1)
    | 1 => exact Rest.odd n
    | k+2 => exact Rest.double _ (ih k (by omega))

inductive Safe : Z0 → Prop where
  | b (L R : List Bool) : Left L → L.headD false = false → Rest R →
      Safe (B L (X 2 ++ R))

theorem xAppend (k : Nat) (R : List Bool) :
    X k ++ false::true::R = X (k+1) ++ R := by
  unfold X
  change rep [false,true] k ++ ([false,true] ++ R) = _
  rw [← List.append_assoc,rep_snoc]
  rfl

def retreatCost (b : Bool) := if b then 2 else 4
theorem retreatPair (b : Bool) (L R : List Bool) :
    run0 table (retreatCost b) (B (true::b::L) R) =
      some (B L (false::true::R)) := by cases b <;> rfl

theorem retreatSingle (R : List Bool) :
    run0 table 4 (B [true] R) = some (B [] (false::true::R)) := by rfl

theorem retreat (L R : List Bool) (h : Left L) :
    ∃ t k S, Left S ∧ S.headD false = false ∧
      (L.headD false = true → 0<k) ∧
      run0 table t (B L R) = some (B S (X k ++ R)) := by
  induction h generalizing R with
  | nil => exact ⟨0,0,[],Left.nil,rfl,by simp,rfl⟩
  | zeroPair L h => exact ⟨0,0,_,Left.zeroPair L h,rfl,by simp,rfl⟩
  | single => exact ⟨4,1,[],Left.nil,rfl,by omega,retreatSingle R⟩
  | onePair b L h ih =>
    obtain ⟨t,k,S,hS,hz,hk,hr⟩ := ih (false::true::R)
    have H := join0 (retreatPair b L R) hr
    rw [xAppend] at H
    exact ⟨retreatCost b+t,k+1,S,hS,hz,by omega,H⟩

theorem scanD (n : Nat) (T R : List Bool) :
    run0 table n ⟨3,Z n ++ true::T,R⟩ =
      some ⟨3,true::T,O n ++ R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 1 ⟨3,Z (n+1) ++ true::T,R⟩ =
      some ⟨3,Z n ++ true::T,true::R⟩ := by rfl
    have H := join0 h1 (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    have he : O (n+1) ++ R = O n ++ true::R := by
      simp only [O,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he]
    exact H

theorem i_eq (k : Nat) : O (2*k) = I k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change true::true::O (2*k) = true::true::I k
    rw [ih]

theorem endC (k : Nat) (T : List Bool) :
    run0 table (1+(2*k+2)+2) (C (Z (2*k) ++ true::T) []) =
      some (B (true::true::true::T) (I k)) := by
  have h1 : run0 table 1 (C (Z (2*k) ++ true::T) []) =
      some ⟨3,Z (2*k+2) ++ true::T,[]⟩ := by rfl
  have h2 := scanD (2*k+2) T []
  have h3 : run0 table 2 ⟨3,true::T,O (2*k+2)++[]⟩ =
      some (B (true::true::true::T) (I k)) := by
    rw [List.append_nil,show 2*k+2=2*(k+1) by omega,i_eq (k+1)]
    rfl
  exact join0 (join0 h1 h2) h3

theorem overflow (L : List Bool) (h : LiveLeft L) :
    ∃ t z, 0<t ∧ run0 table t (C (false::false::L) []) = some z ∧ Safe z := by
  obtain ⟨k,T,rfl,hT⟩ := decompose L h
  have h1 : run0 table (1+(2*(k+1)+2)+2) (C (false::false::(Z (2*k) ++ true::T)) []) =
      some (B (true::true::true::T) (I (k+1))) := by
    exact endC (k+1) T
  have h2 := retreatPair true (true::T) (I (k+1))
  obtain ⟨t,j,S,hS,hz,hj,hr⟩ := retreat (true::T) (false::true::I (k+1)) hT
  have hj1 := hj rfl
  obtain ⟨m,rfl⟩ : ∃ m, j=m+1 := ⟨j-1,by omega⟩
  rw [xAppend] at hr
  exact ⟨_,_,by omega,join0 (join0 h1 h2) hr,
    Safe.b S (X m ++ I (k+1)) hS hz (prefixRest m k)⟩

theorem eatI (L W : List Bool) :
    run0 table 2 (C L (true::true::W)) =
      some (C (false::false::L) W) := by rfl
theorem eatXX (L W : List Bool) :
    run0 table 4 (C L (false::true::false::true::W)) =
      some (C (false::false::true::false::L) W) := by rfl
theorem clearXI (L W : List Bool) :
    run0 table 9 (C L (false::true::true::true::W)) =
      some (B L (false::true::false::true::W)) := by rfl

theorem progressOnes (n : Nat) (L : List Bool) (h : LiveLeft L) :
    ∃ t z, 0<t ∧ run0 table t (C (false::false::L) (I n)) = some z ∧ Safe z := by
  induction n generalizing L with
  | zero => exact overflow L h
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hs⟩ := ih (false::false::L) (LiveLeft.zeroPair L h)
    exact ⟨2+t,z,by omega,join0 (eatI (false::false::L) (I n)) hr,hs⟩

theorem progressC (R : List Bool) (hR : Rest R) (L : List Bool) (h : LiveLeft L) :
    ∃ t z, 0<t ∧ run0 table t (C (false::false::L) R) = some z ∧ Safe z := by
  induction hR generalizing L with
  | ones n => exact progressOnes n L h
  | odd n =>
    exact ⟨9,_,by omega,clearXI (false::false::L) (I n),
      Safe.b (false::false::L) (I n) (Left.zeroPair L (liveLeft L h)) rfl (Rest.ones n)⟩
  | double R hR ih =>
    obtain ⟨t,z,ht,hr,hs⟩ := ih (true::false::false::false::L)
      (LiveLeft.onePair false (false::false::L) (Left.zeroPair L (liveLeft L h)))
    exact ⟨4+t,z,by omega,join0 (eatXX (false::false::L) R) hr,hs⟩

theorem startC (L R : List Bool) (h : Left L) (hz : L.headD false = false) :
    ∃ T, LiveLeft T ∧ run0 table 1 (B L R) = some (C T R) := by
  cases h with
  | nil => exact ⟨[true],LiveLeft.single,rfl⟩
  | zeroPair L h => exact ⟨true::false::L,LiveLeft.onePair false L h,rfl⟩
  | single => contradiction
  | onePair b L h => contradiction

theorem progress (z : Z0) (hz : Safe z) :
    ∃ t y, 0<t ∧ run0 table t z = some y ∧ Safe y := by
  cases hz with
  | b L R hL hz hR =>
    obtain ⟨T,hT,h1⟩ := startC L (X 2 ++ R) hL hz
    have h2 := eatXX T R
    obtain ⟨t,y,ht,hr,hy⟩ := progressC R hR (true::false::T)
      (LiveLeft.onePair false T (liveLeft T hT))
    exact ⟨1+4+t,y,by omega,join0 (join0 h1 h2) hr,hy⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (B [] (X 2)) := by rfl
theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ z, Safe z ∧ run0 table t ⟨0,[],[]⟩ = some z := by
    intro k
    induction k with
    | zero => exact ⟨11,by omega,_,Safe.b [] [] Left.nil rfl (Rest.ones 0),entry⟩
    | succ k ih =>
      obtain ⟨t,ht,z,hz,hr⟩ := ih
      obtain ⟨u,y,hu,hy,hys⟩ := progress z hz
      exact ⟨t+u,by omega,y,hys,join0 hr hy⟩
  obtain ⟨t,ht,z,_,hr⟩ := h n
  exact ⟨t,ht,z,hr⟩
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA105
