import ClosedCertFast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CascadeEvenPre887Z1Z2

open CascadeResetInverse

def p887 : Nat := 2^885
def A887 : Nat := 40*p887 - 2059*887 - 3084
def T887 : Nat := 80*p887 - 4118*887 - 6123

/-- Agent 10's quotient coordinate for the n=887 z1 node. -/
def z1_887 : Nat := A887 / 9

/-- The unique t=1 parent predicted by the second-tier formula. -/
def z2_887 : Nat := 12*(T887/243) - (2*p887+887+1)

def a : Nat :=
  0x3cd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0f748f5

def b : Nat :=
  0x177bf62ad79dac6c28bc39975a3fe9867f1f40f73889a835609215c5b4d9b910813aa50c4a727ae878cd14b802cf301c17e118eecaf953edbd474964c8ddefd8ab5e76b1b0a2f0e65d68ffa619fc7d03dce226a0d582485716d366e44204ea943129c9eba1e33452e00b3cc06de59d

def c : Nat :=
  0x39add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161ee8e77

def d : Nat :=
  0x335ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3f35ba781948b0fcd6e9e06522c3dd197b

def e : Nat :=
  0x13452e00b3cc0705f8463bb2be54fb6f51d25932377bf62ad79dac6c28bc39975a3fe9867f1f40f73889a835609215c5b4d9b910813aa50c4a727ae878cd14b802cf301c17e118eecaf953edbd474964c8ddefd8ab5e76b1b0a2f0e65d68ffa619fc7d03dce226a0d58248570cecf5

def f : Nat :=
  0x26b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587e6b74f0329161f9add3c0ca4587ba2f83

def g : Nat :=
  0x139f140436c82a23d1a5663075fde49beaee172d4ce7c5010db20a88f469598c1d7f7926fabb85cb5339f140436c82a23d1a5663075fde49beaee172d4ce7c5010db20a88f469598c1d7f7926fabb85cb5339f140436c82a23d1a5663075fde49beaee172d4ce7c5010db20a4d913b

def h : Nat :=
  0xa2970059e60382fc231dd95f2a7db7a8e92c991bbdfb156bced636145e1ccbad1ff4c33f8fa07b9c44d41ab0490ae2da6cdc88409d528625393d743c668a5c0167980e0bf08c77657ca9f6dea3a4b2646ef7ec55af3b58d85178732eb47fd30cfe3e81ee7113506ac1242b86768dc

def i : Nat :=
  0x58c955cd32af59502ed277298dfcf4e136e6217a52a41c8fbe72f2c5d2d10f917ff10454bf80a4d05bc578eb0c0e83cde67b60562718b2dc4c51f05088b87aac8a2012ba96109f31fb8d4928da30eddb3e9fe5c7944f21206ca099939b551966a85357e896c46b3901858f5df3309

/-- The exact ten-state reverse subtree rooted at z2. -/
def z2Cone : List Nat := [z2_887,a,b,c,d,e,f,g,h,i]

/-- Add z1 itself; its unique source parent is z2. -/
def z1Cone : List Nat := z1_887 :: z2Cone

/-- Exact source ResetParent list for every node in the eleven-state tree. -/
def parentTable : List (Nat × List Nat) :=
  [ (z1_887,[z2_887]),
    (z2_887,[a,b]),
    (a,[c]),
    (b,[]),
    (c,[d,e]),
    (d,[f]),
    (e,[]),
    (f,[g]),
    (g,[h]),
    (h,[i]),
    (i,[]) ]

theorem parentTable_exact :
    parentTable.all (fun p => parentsFast p.1 = p.2) = true := by
  decide

theorem z1_unique_parent_887 :
    parentsFast z1_887 = [z2_887] := by
  decide

theorem z1_parent_source : ResetParent z2_887 z1_887 := by
  exact (parentsFast_iff z2_887 z1_887).mp (by decide)

theorem z2Cone_length : z2Cone.length = 10 := by decide
theorem z1Cone_length : z1Cone.length = 11 := by decide
theorem z1Cone_nodup : z1Cone.Nodup := by decide

/-- The complete n=887 z1/z2 reverse subtree is backward-closed. -/
theorem z1Cone_closed : closedCertFast z1Cone = true := by
  decide

/-- Neither z1 nor any of its ten source ancestors is reachable from blank. -/
theorem z1Cone_no_root (u : Nat) (hu : u ∈ z1Cone) :
    ¬ CascadeSweep.ReachC (2,0) (u,0) :=
  closedCertFast_excludes u z1Cone z1Cone_closed hu (by decide)

#print axioms parentTable_exact
#print axioms z1_unique_parent_887
#print axioms z1_parent_source
#print axioms z1Cone_closed
#print axioms z1Cone_no_root

end CascadeEvenPre887Z1Z2
