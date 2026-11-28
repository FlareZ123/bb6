import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE180
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/- Certificate data from Google LLC, 2026, Apache-2.0. Adapted to the repository's original SweepPumping semantics. Upstream cryptids commit f7f883d7292cf43d817f14fb1780554171dbd049. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none

inductive Block where
  | b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7 | b8 | b9 | b10 | b11 | b12 | b13 | b14 | b15

def bits : Block → List Bool
  | .b0 => (false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: [])
  | .b1 => (false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: [])
  | .b2 => (false :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: true :: [])
  | .b3 => (false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: [])
  | .b4 => (false :: true :: false :: true :: true :: true :: true :: false :: false :: true :: false :: false :: true :: [])
  | .b5 => (false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: [])
  | .b6 => (false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: [])
  | .b7 => (false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: [])
  | .b8 => (false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: [])
  | .b9 => (false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: true :: [])
  | .b10 => (false :: true :: false :: true :: true :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: [])
  | .b11 => (false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: [])
  | .b12 => (false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: [])
  | .b13 => (false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: [])
  | .b14 => (false :: true :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: [])
  | .b15 => (false :: true :: false :: true :: true :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: [])

def enc : List Block → List Bool
  | [] => (false :: true :: false :: true :: true :: true :: true :: false :: true :: false :: true :: true :: true :: [])
  | b::bs => bits b ++ false::enc bs

def collar : Bool → List Bool
  | false => (false :: false :: false :: true :: [])
  | true => (false :: true :: [])

def boxIn (xs : List Block) (L : List Bool) : Z0 := ⟨0,false::false::false::L,enc xs⟩
def boxOut (c : Bool) (xs : List Block) (L : List Bool) : Z0 := ⟨4,L,collar c ++ false::enc xs⟩
def hub (xs : List Block) : Z0 := ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: []) ++ enc xs⟩

def Live (a b : Z0) : Prop := ∃ n, 0 < n ∧ run0 table n a = some b
theorem exactLive {a b : Z0} {n : Nat} (h : run0 table n a = some b) (hn : 0 < n) : Live a b := ⟨n,hn,h⟩
theorem joinLive {a b c : Z0} (h : Live a b) (j : Live b c) : Live a c := by
  obtain ⟨n,hn,hr⟩ := h
  obtain ⟨k,hk,hs⟩ := j
  exact ⟨n+k,by omega,join0 hr hs⟩

theorem b0s (L R : List Bool) : run0 table 64 ⟨0,(false :: false :: false :: L),(false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: L),(R)⟩ := by rfl
theorem b0s0 (L R : List Bool) : run0 table 12 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b0s1 (L R : List Bool) : run0 table 12 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b1s (L R : List Bool) : run0 table 52 ⟨0,(false :: false :: false :: L),(false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: L),(R)⟩ := by rfl
theorem b1s0 (L R : List Bool) : run0 table 12 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b1s1 (L R : List Bool) : run0 table 12 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b2s (L R : List Bool) : run0 table 48 ⟨0,(false :: false :: false :: L),(false :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: L),(R)⟩ := by rfl
theorem b2s0 (L R : List Bool) : run0 table 22 ⟨4,(false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b2s1 (L R : List Bool) : run0 table 22 ⟨4,(false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b3s (L R : List Bool) : run0 table 37 ⟨0,(false :: false :: false :: L),(false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: true :: true :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b4s (L R : List Bool) : run0 table 50 ⟨0,(false :: false :: false :: L),(false :: true :: false :: true :: true :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: L),(R)⟩ := by rfl
theorem b4s0 (L R : List Bool) : run0 table 86 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b4s1 (L R : List Bool) : run0 table 69 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: L),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L),(R)⟩ := by rfl
theorem b4s10 (L R : List Bool) : run0 table 14 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b4s11 (L R : List Bool) : run0 table 14 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b5s (L R : List Bool) : run0 table 79 ⟨0,(false :: false :: false :: L),(false :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b6s (L R : List Bool) : run0 table 41 ⟨0,(false :: false :: false :: L),(false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b7s (L R : List Bool) : run0 table 67 ⟨0,(false :: false :: false :: L),(false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b8s (L R : List Bool) : run0 table 42 ⟨0,(false :: false :: false :: L),(false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: L),(R)⟩ := by rfl
theorem b8s0 (L R : List Bool) : run0 table 60 ⟨4,(false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b8s1 (L R : List Bool) : run0 table 43 ⟨4,(false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: L),(R)⟩ := by rfl
theorem b8s10 (L R : List Bool) : run0 table 14 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b8s11 (L R : List Bool) : run0 table 14 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b9s (L R : List Bool) : run0 table 42 ⟨0,(false :: false :: false :: L),(false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L),(R)⟩ := by rfl
theorem b9s0 (L R : List Bool) : run0 table 98 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b9s1 (L R : List Bool) : run0 table 81 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: true :: true :: L),(R)⟩ := by rfl
theorem b9s10 (L R : List Bool) : run0 table 14 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b9s11 (L R : List Bool) : run0 table 14 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b10s (L R : List Bool) : run0 table 112 ⟨0,(false :: false :: false :: L),(false :: true :: false :: true :: true :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: true :: L),(R)⟩ := by rfl
theorem b10s0 (L R : List Bool) : run0 table 62 ⟨4,(false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b10s1 (L R : List Bool) : run0 table 43 ⟨4,(false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L),(R)⟩ := by rfl
theorem b10s10 (L R : List Bool) : run0 table 16 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b10s11 (L R : List Bool) : run0 table 16 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b11s (L R : List Bool) : run0 table 37 ⟨0,(false :: false :: false :: L),(false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: true :: true :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b12s (L R : List Bool) : run0 table 41 ⟨0,(false :: false :: false :: L),(false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b13s (L R : List Bool) : run0 table 110 ⟨0,(false :: false :: false :: L),(false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: L),(R)⟩ := by rfl
theorem b13s0 (L R : List Bool) : run0 table 24 ⟨4,(false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b13s1 (L R : List Bool) : run0 table 24 ⟨4,(false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b14s (L R : List Bool) : run0 table 41 ⟨0,(false :: false :: false :: L),(false :: true :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b15s (L R : List Bool) : run0 table 32 ⟨0,(false :: false :: false :: L),(false :: true :: false :: true :: true :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: L),(R)⟩ := by rfl
theorem b15s0 (L R : List Bool) : run0 table 108 ⟨4,(false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem b15s1 (L R : List Bool) : run0 table 43 ⟨4,(false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: L),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L),(R)⟩ := by rfl
theorem b15s10 (L R : List Bool) : run0 table 62 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L),(false :: false :: false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem b15s11 (L R : List Bool) : run0 table 62 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L),(false :: true :: false :: R)⟩ = some ⟨4,(L),(false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem hs (R : List Bool) : run0 table 91 ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: true :: true :: []),(R)⟩ := by rfl
theorem hs0 (R : List Bool) : run0 table 193 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: true :: true :: []),(false :: false :: false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: []),(R)⟩ := by rfl
theorem hs00 (R : List Bool) : run0 table 42 ⟨4,(false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: []),(false :: false :: false :: true :: false :: R)⟩ = some ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem hs01 (R : List Bool) : run0 table 42 ⟨4,(false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: []),(false :: true :: false :: R)⟩ = some ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: R)⟩ := by rfl
theorem hs1 (R : List Bool) : run0 table 69 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: true :: true :: []),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: true :: []),(R)⟩ := by rfl
theorem hs10 (R : List Bool) : run0 table 172 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: true :: []),(false :: false :: false :: true :: false :: R)⟩ = some ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: true :: false :: R)⟩ := by rfl
theorem hs11 (R : List Bool) : run0 table 137 ⟨4,(false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: true :: []),(false :: true :: false :: R)⟩ = some ⟨0,(false :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: []),(R)⟩ := by rfl
theorem hs110 (R : List Bool) : run0 table 32 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: []),(false :: false :: false :: true :: false :: R)⟩ = some ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl
theorem hs111 (R : List Bool) : run0 table 32 ⟨4,(true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: []),(false :: true :: false :: R)⟩ = some ⟨1,(false :: true :: []),(false :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: true :: false :: R)⟩ := by rfl

theorem boxEnd (L : List Bool) : run0 table 103 (boxIn [] L) = some (boxOut false [] L) := by rfl

theorem boxLen (n : Nat) (xs : List Block) (hx : xs.length = n) (L : List Bool) :
    ∃ c ys, ys.length = n ∧ Live (boxIn xs L) (boxOut c ys L) := by
  induction n generalizing xs L with
  | zero =>
    have he : xs = [] := List.length_eq_zero_iff.mp hx
    subst xs
    exact ⟨false,[],rfl,exactLive (boxEnd L) (by decide)⟩
  | succ n ih =>
    cases xs with
    | nil => simp at hx
    | cons b xs =>
      have hxs : xs.length = n := by simpa using hx
      cases b with
      | b0 =>
        have hb0s := exactLive (b0s L (enc xs)) (by decide)
        obtain ⟨cb0s,ysb0s,lenb0s,subb0s⟩ := ih xs hxs (true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: L)
        cases cb0s with
        | false =>
          have hb0s0 := exactLive (b0s0 L (enc ysb0s)) (by decide)
          refine ⟨true, Block.b7 :: ysb0s, by simp [lenb0s], ?_⟩
          exact joinLive hb0s (joinLive subb0s (hb0s0))
        | true =>
          have hb0s1 := exactLive (b0s1 L (enc ysb0s)) (by decide)
          refine ⟨true, Block.b1 :: ysb0s, by simp [lenb0s], ?_⟩
          exact joinLive hb0s (joinLive subb0s (hb0s1))
      | b1 =>
        have hb1s := exactLive (b1s L (enc xs)) (by decide)
        obtain ⟨cb1s,ysb1s,lenb1s,subb1s⟩ := ih xs hxs (false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: L)
        cases cb1s with
        | false =>
          have hb1s0 := exactLive (b1s0 L (enc ysb1s)) (by decide)
          refine ⟨true, Block.b5 :: ysb1s, by simp [lenb1s], ?_⟩
          exact joinLive hb1s (joinLive subb1s (hb1s0))
        | true =>
          have hb1s1 := exactLive (b1s1 L (enc ysb1s)) (by decide)
          refine ⟨true, Block.b0 :: ysb1s, by simp [lenb1s], ?_⟩
          exact joinLive hb1s (joinLive subb1s (hb1s1))
      | b2 =>
        have hb2s := exactLive (b2s L (enc xs)) (by decide)
        obtain ⟨cb2s,ysb2s,lenb2s,subb2s⟩ := ih xs hxs (false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: L)
        cases cb2s with
        | false =>
          have hb2s0 := exactLive (b2s0 L (enc ysb2s)) (by decide)
          refine ⟨true, Block.b11 :: ysb2s, by simp [lenb2s], ?_⟩
          exact joinLive hb2s (joinLive subb2s (hb2s0))
        | true =>
          have hb2s1 := exactLive (b2s1 L (enc ysb2s)) (by decide)
          refine ⟨true, Block.b3 :: ysb2s, by simp [lenb2s], ?_⟩
          exact joinLive hb2s (joinLive subb2s (hb2s1))
      | b3 =>
        have hb3s := exactLive (b3s L (enc xs)) (by decide)
        refine ⟨true, Block.b4 :: xs, by simp [hxs], ?_⟩
        exact hb3s
      | b4 =>
        have hb4s := exactLive (b4s L (enc xs)) (by decide)
        obtain ⟨cb4s,ysb4s,lenb4s,subb4s⟩ := ih xs hxs (true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: L)
        cases cb4s with
        | false =>
          have hb4s0 := exactLive (b4s0 L (enc ysb4s)) (by decide)
          refine ⟨false, Block.b2 :: ysb4s, by simp [lenb4s], ?_⟩
          exact joinLive hb4s (joinLive subb4s (hb4s0))
        | true =>
          have hb4s1 := exactLive (b4s1 L (enc ysb4s)) (by decide)
          obtain ⟨cb4s1,ysb4s1,lenb4s1,subb4s1⟩ := ih ysb4s lenb4s (false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L)
          cases cb4s1 with
          | false =>
            have hb4s10 := exactLive (b4s10 L (enc ysb4s1)) (by decide)
            refine ⟨false, Block.b5 :: ysb4s1, by simp [lenb4s1], ?_⟩
            exact joinLive hb4s (joinLive subb4s (joinLive hb4s1 (joinLive subb4s1 (hb4s10))))
          | true =>
            have hb4s11 := exactLive (b4s11 L (enc ysb4s1)) (by decide)
            refine ⟨false, Block.b0 :: ysb4s1, by simp [lenb4s1], ?_⟩
            exact joinLive hb4s (joinLive subb4s (joinLive hb4s1 (joinLive subb4s1 (hb4s11))))
      | b5 =>
        have hb5s := exactLive (b5s L (enc xs)) (by decide)
        refine ⟨true, Block.b8 :: xs, by simp [hxs], ?_⟩
        exact hb5s
      | b6 =>
        have hb6s := exactLive (b6s L (enc xs)) (by decide)
        refine ⟨true, Block.b9 :: xs, by simp [hxs], ?_⟩
        exact hb6s
      | b7 =>
        have hb7s := exactLive (b7s L (enc xs)) (by decide)
        refine ⟨true, Block.b2 :: xs, by simp [hxs], ?_⟩
        exact hb7s
      | b8 =>
        have hb8s := exactLive (b8s L (enc xs)) (by decide)
        obtain ⟨cb8s,ysb8s,lenb8s,subb8s⟩ := ih xs hxs (false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: L)
        cases cb8s with
        | false =>
          have hb8s0 := exactLive (b8s0 L (enc ysb8s)) (by decide)
          refine ⟨true, Block.b14 :: ysb8s, by simp [lenb8s], ?_⟩
          exact joinLive hb8s (joinLive subb8s (hb8s0))
        | true =>
          have hb8s1 := exactLive (b8s1 L (enc ysb8s)) (by decide)
          obtain ⟨cb8s1,ysb8s1,lenb8s1,subb8s1⟩ := ih ysb8s lenb8s (true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: L)
          cases cb8s1 with
          | false =>
            have hb8s10 := exactLive (b8s10 L (enc ysb8s1)) (by decide)
            refine ⟨true, Block.b12 :: ysb8s1, by simp [lenb8s1], ?_⟩
            exact joinLive hb8s (joinLive subb8s (joinLive hb8s1 (joinLive subb8s1 (hb8s10))))
          | true =>
            have hb8s11 := exactLive (b8s11 L (enc ysb8s1)) (by decide)
            refine ⟨true, Block.b6 :: ysb8s1, by simp [lenb8s1], ?_⟩
            exact joinLive hb8s (joinLive subb8s (joinLive hb8s1 (joinLive subb8s1 (hb8s11))))
      | b9 =>
        have hb9s := exactLive (b9s L (enc xs)) (by decide)
        obtain ⟨cb9s,ysb9s,lenb9s,subb9s⟩ := ih xs hxs (false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L)
        cases cb9s with
        | false =>
          have hb9s0 := exactLive (b9s0 L (enc ysb9s)) (by decide)
          refine ⟨false, Block.b8 :: ysb9s, by simp [lenb9s], ?_⟩
          exact joinLive hb9s (joinLive subb9s (hb9s0))
        | true =>
          have hb9s1 := exactLive (b9s1 L (enc ysb9s)) (by decide)
          obtain ⟨cb9s1,ysb9s1,lenb9s1,subb9s1⟩ := ih ysb9s lenb9s (true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: true :: true :: L)
          cases cb9s1 with
          | false =>
            have hb9s10 := exactLive (b9s10 L (enc ysb9s1)) (by decide)
            refine ⟨false, Block.b7 :: ysb9s1, by simp [lenb9s1], ?_⟩
            exact joinLive hb9s (joinLive subb9s (joinLive hb9s1 (joinLive subb9s1 (hb9s10))))
          | true =>
            have hb9s11 := exactLive (b9s11 L (enc ysb9s1)) (by decide)
            refine ⟨false, Block.b1 :: ysb9s1, by simp [lenb9s1], ?_⟩
            exact joinLive hb9s (joinLive subb9s (joinLive hb9s1 (joinLive subb9s1 (hb9s11))))
      | b10 =>
        have hb10s := exactLive (b10s L (enc xs)) (by decide)
        obtain ⟨cb10s,ysb10s,lenb10s,subb10s⟩ := ih xs hxs (false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: true :: L)
        cases cb10s with
        | false =>
          have hb10s0 := exactLive (b10s0 L (enc ysb10s)) (by decide)
          refine ⟨false, Block.b14 :: ysb10s, by simp [lenb10s], ?_⟩
          exact joinLive hb10s (joinLive subb10s (hb10s0))
        | true =>
          have hb10s1 := exactLive (b10s1 L (enc ysb10s)) (by decide)
          obtain ⟨cb10s1,ysb10s1,lenb10s1,subb10s1⟩ := ih ysb10s lenb10s (true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: L)
          cases cb10s1 with
          | false =>
            have hb10s10 := exactLive (b10s10 L (enc ysb10s1)) (by decide)
            refine ⟨false, Block.b12 :: ysb10s1, by simp [lenb10s1], ?_⟩
            exact joinLive hb10s (joinLive subb10s (joinLive hb10s1 (joinLive subb10s1 (hb10s10))))
          | true =>
            have hb10s11 := exactLive (b10s11 L (enc ysb10s1)) (by decide)
            refine ⟨false, Block.b6 :: ysb10s1, by simp [lenb10s1], ?_⟩
            exact joinLive hb10s (joinLive subb10s (joinLive hb10s1 (joinLive subb10s1 (hb10s11))))
      | b11 =>
        have hb11s := exactLive (b11s L (enc xs)) (by decide)
        refine ⟨true, Block.b10 :: xs, by simp [hxs], ?_⟩
        exact hb11s
      | b12 =>
        have hb12s := exactLive (b12s L (enc xs)) (by decide)
        refine ⟨true, Block.b13 :: xs, by simp [hxs], ?_⟩
        exact hb12s
      | b13 =>
        have hb13s := exactLive (b13s L (enc xs)) (by decide)
        obtain ⟨cb13s,ysb13s,lenb13s,subb13s⟩ := ih xs hxs (false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: true :: true :: L)
        cases cb13s with
        | false =>
          have hb13s0 := exactLive (b13s0 L (enc ysb13s)) (by decide)
          refine ⟨false, Block.b11 :: ysb13s, by simp [lenb13s], ?_⟩
          exact joinLive hb13s (joinLive subb13s (hb13s0))
        | true =>
          have hb13s1 := exactLive (b13s1 L (enc ysb13s)) (by decide)
          refine ⟨false, Block.b3 :: ysb13s, by simp [lenb13s], ?_⟩
          exact joinLive hb13s (joinLive subb13s (hb13s1))
      | b14 =>
        have hb14s := exactLive (b14s L (enc xs)) (by decide)
        refine ⟨true, Block.b15 :: xs, by simp [hxs], ?_⟩
        exact hb14s
      | b15 =>
        have hb15s := exactLive (b15s L (enc xs)) (by decide)
        obtain ⟨cb15s,ysb15s,lenb15s,subb15s⟩ := ih xs hxs (false :: true :: true :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: L)
        cases cb15s with
        | false =>
          have hb15s0 := exactLive (b15s0 L (enc ysb15s)) (by decide)
          refine ⟨false, Block.b15 :: ysb15s, by simp [lenb15s], ?_⟩
          exact joinLive hb15s (joinLive subb15s (hb15s0))
        | true =>
          have hb15s1 := exactLive (b15s1 L (enc ysb15s)) (by decide)
          obtain ⟨cb15s1,ysb15s1,lenb15s1,subb15s1⟩ := ih ysb15s lenb15s (true :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: false :: false :: L)
          cases cb15s1 with
          | false =>
            have hb15s10 := exactLive (b15s10 L (enc ysb15s1)) (by decide)
            refine ⟨false, Block.b13 :: ysb15s1, by simp [lenb15s1], ?_⟩
            exact joinLive hb15s (joinLive subb15s (joinLive hb15s1 (joinLive subb15s1 (hb15s10))))
          | true =>
            have hb15s11 := exactLive (b15s11 L (enc ysb15s1)) (by decide)
            refine ⟨false, Block.b9 :: ysb15s1, by simp [lenb15s1], ?_⟩
            exact joinLive hb15s (joinLive subb15s (joinLive hb15s1 (joinLive subb15s1 (hb15s11))))

theorem hubAdvance (xs : List Block) : ∃ ys, Live (hub xs) (hub ys) := by
  have hhs := exactLive (hs (enc xs)) (by decide)
  obtain ⟨chs,yshs,lenhs,subhs⟩ := boxLen xs.length xs rfl (true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: false :: true :: true :: [])
  cases chs with
  | false =>
    have hhs0 := exactLive (hs0 (enc yshs)) (by decide)
    obtain ⟨chs0,yshs0,lenhs0,subhs0⟩ := boxLen yshs.length yshs rfl (false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: [])
    cases chs0 with
    | false =>
      have hhs00 := exactLive (hs00 (enc yshs0)) (by decide)
      refine ⟨Block.b11 :: yshs0, ?_⟩
      exact joinLive hhs (joinLive subhs (joinLive hhs0 (joinLive subhs0 (hhs00))))
    | true =>
      have hhs01 := exactLive (hs01 (enc yshs0)) (by decide)
      refine ⟨Block.b3 :: yshs0, ?_⟩
      exact joinLive hhs (joinLive subhs (joinLive hhs0 (joinLive subhs0 (hhs01))))
  | true =>
    have hhs1 := exactLive (hs1 (enc yshs)) (by decide)
    obtain ⟨chs1,yshs1,lenhs1,subhs1⟩ := boxLen yshs.length yshs rfl (false :: true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: true :: [])
    cases chs1 with
    | false =>
      have hhs10 := exactLive (hs10 (enc yshs1)) (by decide)
      refine ⟨Block.b8 :: yshs1, ?_⟩
      exact joinLive hhs (joinLive subhs (joinLive hhs1 (joinLive subhs1 (hhs10))))
    | true =>
      have hhs11 := exactLive (hs11 (enc yshs1)) (by decide)
      obtain ⟨chs11,yshs11,lenhs11,subhs11⟩ := boxLen yshs1.length yshs1 rfl (true :: true :: true :: false :: true :: true :: true :: true :: true :: false :: true :: true :: false :: true :: true :: true :: true :: true :: false :: false :: true :: true :: [])
      cases chs11 with
      | false =>
        have hhs110 := exactLive (hs110 (enc yshs11)) (by decide)
        refine ⟨Block.b7 :: yshs11, ?_⟩
        exact joinLive hhs (joinLive subhs (joinLive hhs1 (joinLive subhs1 (joinLive hhs11 (joinLive subhs11 (hhs110))))))
      | true =>
        have hhs111 := exactLive (hs111 (enc yshs11)) (by decide)
        refine ⟨Block.b1 :: yshs11, ?_⟩
        exact joinLive hhs (joinLive subhs (joinLive hhs1 (joinLive subhs1 (joinLive hhs11 (joinLive subhs11 (hhs111))))))

theorem entry : run0 table 843 ⟨0,[],[]⟩ = some (hub [.b15]) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arb : ∀ k : Nat, ∃ t xs, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (hub xs) := by
    intro k
    induction k with
    | zero => exact ⟨843,[.b15],by decide,entry⟩
    | succ k ih =>
      obtain ⟨t,xs,ht,hr⟩ := ih
      obtain ⟨ys,n,hn,hs⟩ := hubAdvance xs
      exact ⟨t+n,ys,by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,xs,ht,hr⟩ := arb n
  have hp : (zrun table t start).map project = some (hub xs) := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hp
  | some u =>
    have H := zrun_sound table m hm t start u h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms boxLen
#print axioms hubAdvance
#print axioms never
end BB6.Agent11Raw39LE180
