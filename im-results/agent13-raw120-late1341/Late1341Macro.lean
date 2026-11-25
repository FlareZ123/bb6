import Late1341Base
namespace BB6.Agent13Raw120Late1341
open BB6Coverage BB6Coverage.Agent13PackedZipper
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem step18_0 (L R : Nat) : stepP table ⟨0,8*L,16*R+13⟩ = some ⟨1,16*L+3,8*R+6⟩ := by
  have h0 : (8*L)%2=0 := by omega
  have h1 : (8*L)/2=4*L := by omega
  have h2 : (16*R+13)%2=1 := by omega
  have h3 : (16*R+13)/2=8*R+6 := by omega
  have hread : readP ⟨0,8*L,16*R+13⟩ = (0,false) := by simp [readP,h0]
  have htable : table (0,false) = some (some ⟨true,true,1⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_1 (L R : Nat) : stepP table ⟨1,16*L+3,8*R+6⟩ = some ⟨5,8*L+1,16*R+12⟩ := by
  have h0 : (16*L+3)%2=1 := by omega
  have h1 : (16*L+3)/2=8*L+1 := by omega
  have hread : readP ⟨1,16*L+3,8*R+6⟩ = (1,true) := by simp [readP,h0]
  have htable : table (1,true) = some (some ⟨false,false,5⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_2 (L R : Nat) : stepP table ⟨5,8*L+1,16*R+12⟩ = some ⟨4,4*L,32*R+24⟩ := by
  have h0 : (8*L+1)%2=1 := by omega
  have h1 : (8*L+1)/2=4*L := by omega
  have hread : readP ⟨5,8*L+1,16*R+12⟩ = (5,true) := by simp [readP,h0]
  have htable : table (5,true) = some (some ⟨false,false,4⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_3 (L R : Nat) : stepP table ⟨4,4*L,32*R+24⟩ = some ⟨1,2*L,64*R+49⟩ := by
  have h0 : (4*L)%2=0 := by omega
  have h1 : (4*L)/2=2*L := by omega
  have hread : readP ⟨4,4*L,32*R+24⟩ = (4,false) := by simp [readP,h0]
  have htable : table (4,false) = some (some ⟨true,false,1⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_4 (L R : Nat) : stepP table ⟨1,2*L,64*R+49⟩ = some ⟨2,4*L+3,32*R+24⟩ := by
  have h0 : (2*L)%2=0 := by omega
  have h1 : (2*L)/2=1*L := by omega
  have h2 : (64*R+49)%2=1 := by omega
  have h3 : (64*R+49)/2=32*R+24 := by omega
  have hread : readP ⟨1,2*L,64*R+49⟩ = (1,false) := by simp [readP,h0]
  have htable : table (1,false) = some (some ⟨true,true,2⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_5 (L R : Nat) : stepP table ⟨2,4*L+3,32*R+24⟩ = some ⟨5,8*L+4,16*R+12⟩ := by
  have h0 : (4*L+3)%2=1 := by omega
  have h1 : (4*L+3)/2=2*L+1 := by omega
  have h2 : (32*R+24)%2=0 := by omega
  have h3 : (32*R+24)/2=16*R+12 := by omega
  have hread : readP ⟨2,4*L+3,32*R+24⟩ = (2,true) := by simp [readP,h0]
  have htable : table (2,true) = some (some ⟨false,true,5⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_6 (L R : Nat) : stepP table ⟨5,8*L+4,16*R+12⟩ = some ⟨0,16*L+8,8*R+6⟩ := by
  have h0 : (8*L+4)%2=0 := by omega
  have h1 : (8*L+4)/2=4*L+2 := by omega
  have h2 : (16*R+12)%2=0 := by omega
  have h3 : (16*R+12)/2=8*R+6 := by omega
  have hread : readP ⟨5,8*L+4,16*R+12⟩ = (5,false) := by simp [readP,h0]
  have htable : table (5,false) = some (some ⟨false,true,0⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_7 (L R : Nat) : stepP table ⟨0,16*L+8,8*R+6⟩ = some ⟨1,32*L+18,4*R+3⟩ := by
  have h0 : (16*L+8)%2=0 := by omega
  have h1 : (16*L+8)/2=8*L+4 := by omega
  have h2 : (8*R+6)%2=0 := by omega
  have h3 : (8*R+6)/2=4*R+3 := by omega
  have hread : readP ⟨0,16*L+8,8*R+6⟩ = (0,false) := by simp [readP,h0]
  have htable : table (0,false) = some (some ⟨true,true,1⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_8 (L R : Nat) : stepP table ⟨1,32*L+18,4*R+3⟩ = some ⟨2,64*L+39,2*R+1⟩ := by
  have h0 : (32*L+18)%2=0 := by omega
  have h1 : (32*L+18)/2=16*L+9 := by omega
  have h2 : (4*R+3)%2=1 := by omega
  have h3 : (4*R+3)/2=2*R+1 := by omega
  have hread : readP ⟨1,32*L+18,4*R+3⟩ = (1,false) := by simp [readP,h0]
  have htable : table (1,false) = some (some ⟨true,true,2⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_9 (L R : Nat) : stepP table ⟨2,64*L+39,2*R+1⟩ = some ⟨5,128*L+77,1*R⟩ := by
  have h0 : (64*L+39)%2=1 := by omega
  have h1 : (64*L+39)/2=32*L+19 := by omega
  have h2 : (2*R+1)%2=1 := by omega
  have h3 : (2*R+1)/2=1*R := by omega
  have hread : readP ⟨2,64*L+39,2*R+1⟩ = (2,true) := by simp [readP,h0]
  have htable : table (2,true) = some (some ⟨false,true,5⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_10 (L R : Nat) : stepP table ⟨5,128*L+77,1*R⟩ = some ⟨4,64*L+38,2*R⟩ := by
  have h0 : (128*L+77)%2=1 := by omega
  have h1 : (128*L+77)/2=64*L+38 := by omega
  have hread : readP ⟨5,128*L+77,1*R⟩ = (5,true) := by simp [readP,h0]
  have htable : table (5,true) = some (some ⟨false,false,4⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_11 (L R : Nat) : stepP table ⟨4,64*L+38,2*R⟩ = some ⟨1,32*L+19,4*R+1⟩ := by
  have h0 : (64*L+38)%2=0 := by omega
  have h1 : (64*L+38)/2=32*L+19 := by omega
  have hread : readP ⟨4,64*L+38,2*R⟩ = (4,false) := by simp [readP,h0]
  have htable : table (4,false) = some (some ⟨true,false,1⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_12 (L R : Nat) : stepP table ⟨1,32*L+19,4*R+1⟩ = some ⟨5,16*L+9,8*R+2⟩ := by
  have h0 : (32*L+19)%2=1 := by omega
  have h1 : (32*L+19)/2=16*L+9 := by omega
  have hread : readP ⟨1,32*L+19,4*R+1⟩ = (1,true) := by simp [readP,h0]
  have htable : table (1,true) = some (some ⟨false,false,5⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_13 (L R : Nat) : stepP table ⟨5,16*L+9,8*R+2⟩ = some ⟨4,8*L+4,16*R+4⟩ := by
  have h0 : (16*L+9)%2=1 := by omega
  have h1 : (16*L+9)/2=8*L+4 := by omega
  have hread : readP ⟨5,16*L+9,8*R+2⟩ = (5,true) := by simp [readP,h0]
  have htable : table (5,true) = some (some ⟨false,false,4⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_14 (L R : Nat) : stepP table ⟨4,8*L+4,16*R+4⟩ = some ⟨1,4*L+2,32*R+9⟩ := by
  have h0 : (8*L+4)%2=0 := by omega
  have h1 : (8*L+4)/2=4*L+2 := by omega
  have hread : readP ⟨4,8*L+4,16*R+4⟩ = (4,false) := by simp [readP,h0]
  have htable : table (4,false) = some (some ⟨true,false,1⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1]
  <;> omega

private theorem step18_15 (L R : Nat) : stepP table ⟨1,4*L+2,32*R+9⟩ = some ⟨2,8*L+7,16*R+4⟩ := by
  have h0 : (4*L+2)%2=0 := by omega
  have h1 : (4*L+2)/2=2*L+1 := by omega
  have h2 : (32*R+9)%2=1 := by omega
  have h3 : (32*R+9)/2=16*R+4 := by omega
  have hread : readP ⟨1,4*L+2,32*R+9⟩ = (1,false) := by simp [readP,h0]
  have htable : table (1,false) = some (some ⟨true,true,2⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_16 (L R : Nat) : stepP table ⟨2,8*L+7,16*R+4⟩ = some ⟨5,16*L+12,8*R+2⟩ := by
  have h0 : (8*L+7)%2=1 := by omega
  have h1 : (8*L+7)/2=4*L+3 := by omega
  have h2 : (16*R+4)%2=0 := by omega
  have h3 : (16*R+4)/2=8*R+2 := by omega
  have hread : readP ⟨2,8*L+7,16*R+4⟩ = (2,true) := by simp [readP,h0]
  have htable : table (2,true) = some (some ⟨false,true,5⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem step18_17 (L R : Nat) : stepP table ⟨5,16*L+12,8*R+2⟩ = some ⟨0,32*L+24,4*R+1⟩ := by
  have h0 : (16*L+12)%2=0 := by omega
  have h1 : (16*L+12)/2=8*L+6 := by omega
  have h2 : (8*R+2)%2=0 := by omega
  have h3 : (8*R+2)/2=4*R+1 := by omega
  have hread : readP ⟨5,16*L+12,8*R+2⟩ = (5,false) := by simp [readP,h0]
  have htable : table (5,false) = some (some ⟨false,true,0⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP, h0,h1,h2,h3]
  <;> omega

private theorem one18_0 (L R : Nat) : runP table 1 ⟨0,8*L,16*R+13⟩ = some ⟨1,16*L+3,8*R+6⟩ := by
  change (stepP table ⟨0,8*L,16*R+13⟩).bind (runP table 0) = some ⟨1,16*L+3,8*R+6⟩
  rw [step18_0 L R]
  rfl

private theorem one18_1 (L R : Nat) : runP table 1 ⟨1,16*L+3,8*R+6⟩ = some ⟨5,8*L+1,16*R+12⟩ := by
  change (stepP table ⟨1,16*L+3,8*R+6⟩).bind (runP table 0) = some ⟨5,8*L+1,16*R+12⟩
  rw [step18_1 L R]
  rfl

private theorem one18_2 (L R : Nat) : runP table 1 ⟨5,8*L+1,16*R+12⟩ = some ⟨4,4*L,32*R+24⟩ := by
  change (stepP table ⟨5,8*L+1,16*R+12⟩).bind (runP table 0) = some ⟨4,4*L,32*R+24⟩
  rw [step18_2 L R]
  rfl

private theorem one18_3 (L R : Nat) : runP table 1 ⟨4,4*L,32*R+24⟩ = some ⟨1,2*L,64*R+49⟩ := by
  change (stepP table ⟨4,4*L,32*R+24⟩).bind (runP table 0) = some ⟨1,2*L,64*R+49⟩
  rw [step18_3 L R]
  rfl

private theorem one18_4 (L R : Nat) : runP table 1 ⟨1,2*L,64*R+49⟩ = some ⟨2,4*L+3,32*R+24⟩ := by
  change (stepP table ⟨1,2*L,64*R+49⟩).bind (runP table 0) = some ⟨2,4*L+3,32*R+24⟩
  rw [step18_4 L R]
  rfl

private theorem one18_5 (L R : Nat) : runP table 1 ⟨2,4*L+3,32*R+24⟩ = some ⟨5,8*L+4,16*R+12⟩ := by
  change (stepP table ⟨2,4*L+3,32*R+24⟩).bind (runP table 0) = some ⟨5,8*L+4,16*R+12⟩
  rw [step18_5 L R]
  rfl

private theorem one18_6 (L R : Nat) : runP table 1 ⟨5,8*L+4,16*R+12⟩ = some ⟨0,16*L+8,8*R+6⟩ := by
  change (stepP table ⟨5,8*L+4,16*R+12⟩).bind (runP table 0) = some ⟨0,16*L+8,8*R+6⟩
  rw [step18_6 L R]
  rfl

private theorem one18_7 (L R : Nat) : runP table 1 ⟨0,16*L+8,8*R+6⟩ = some ⟨1,32*L+18,4*R+3⟩ := by
  change (stepP table ⟨0,16*L+8,8*R+6⟩).bind (runP table 0) = some ⟨1,32*L+18,4*R+3⟩
  rw [step18_7 L R]
  rfl

private theorem one18_8 (L R : Nat) : runP table 1 ⟨1,32*L+18,4*R+3⟩ = some ⟨2,64*L+39,2*R+1⟩ := by
  change (stepP table ⟨1,32*L+18,4*R+3⟩).bind (runP table 0) = some ⟨2,64*L+39,2*R+1⟩
  rw [step18_8 L R]
  rfl

private theorem one18_9 (L R : Nat) : runP table 1 ⟨2,64*L+39,2*R+1⟩ = some ⟨5,128*L+77,1*R⟩ := by
  change (stepP table ⟨2,64*L+39,2*R+1⟩).bind (runP table 0) = some ⟨5,128*L+77,1*R⟩
  rw [step18_9 L R]
  rfl

private theorem one18_10 (L R : Nat) : runP table 1 ⟨5,128*L+77,1*R⟩ = some ⟨4,64*L+38,2*R⟩ := by
  change (stepP table ⟨5,128*L+77,1*R⟩).bind (runP table 0) = some ⟨4,64*L+38,2*R⟩
  rw [step18_10 L R]
  rfl

private theorem one18_11 (L R : Nat) : runP table 1 ⟨4,64*L+38,2*R⟩ = some ⟨1,32*L+19,4*R+1⟩ := by
  change (stepP table ⟨4,64*L+38,2*R⟩).bind (runP table 0) = some ⟨1,32*L+19,4*R+1⟩
  rw [step18_11 L R]
  rfl

private theorem one18_12 (L R : Nat) : runP table 1 ⟨1,32*L+19,4*R+1⟩ = some ⟨5,16*L+9,8*R+2⟩ := by
  change (stepP table ⟨1,32*L+19,4*R+1⟩).bind (runP table 0) = some ⟨5,16*L+9,8*R+2⟩
  rw [step18_12 L R]
  rfl

private theorem one18_13 (L R : Nat) : runP table 1 ⟨5,16*L+9,8*R+2⟩ = some ⟨4,8*L+4,16*R+4⟩ := by
  change (stepP table ⟨5,16*L+9,8*R+2⟩).bind (runP table 0) = some ⟨4,8*L+4,16*R+4⟩
  rw [step18_13 L R]
  rfl

private theorem one18_14 (L R : Nat) : runP table 1 ⟨4,8*L+4,16*R+4⟩ = some ⟨1,4*L+2,32*R+9⟩ := by
  change (stepP table ⟨4,8*L+4,16*R+4⟩).bind (runP table 0) = some ⟨1,4*L+2,32*R+9⟩
  rw [step18_14 L R]
  rfl

private theorem one18_15 (L R : Nat) : runP table 1 ⟨1,4*L+2,32*R+9⟩ = some ⟨2,8*L+7,16*R+4⟩ := by
  change (stepP table ⟨1,4*L+2,32*R+9⟩).bind (runP table 0) = some ⟨2,8*L+7,16*R+4⟩
  rw [step18_15 L R]
  rfl

private theorem one18_16 (L R : Nat) : runP table 1 ⟨2,8*L+7,16*R+4⟩ = some ⟨5,16*L+12,8*R+2⟩ := by
  change (stepP table ⟨2,8*L+7,16*R+4⟩).bind (runP table 0) = some ⟨5,16*L+12,8*R+2⟩
  rw [step18_16 L R]
  rfl

private theorem one18_17 (L R : Nat) : runP table 1 ⟨5,16*L+12,8*R+2⟩ = some ⟨0,32*L+24,4*R+1⟩ := by
  change (stepP table ⟨5,16*L+12,8*R+2⟩).bind (runP table 0) = some ⟨0,32*L+24,4*R+1⟩
  rw [step18_17 L R]
  rfl

theorem macro18 (L R : Nat) : runP table 18 ⟨0,8*L,16*R+13⟩ = some ⟨0,32*L+24,4*R+1⟩ := by
  have h0 : runP table 1 ⟨0,8*L,16*R+13⟩ = some ⟨1,16*L+3,8*R+6⟩ := one18_0 L R
  have h1 : runP table 2 ⟨0,8*L,16*R+13⟩ = some ⟨5,8*L+1,16*R+12⟩ := @joinP table 1 1 ⟨0,8*L,16*R+13⟩ ⟨1,16*L+3,8*R+6⟩ ⟨5,8*L+1,16*R+12⟩ h0 (one18_1 L R)
  have h2 : runP table 3 ⟨0,8*L,16*R+13⟩ = some ⟨4,4*L,32*R+24⟩ := @joinP table 2 1 ⟨0,8*L,16*R+13⟩ ⟨5,8*L+1,16*R+12⟩ ⟨4,4*L,32*R+24⟩ h1 (one18_2 L R)
  have h3 : runP table 4 ⟨0,8*L,16*R+13⟩ = some ⟨1,2*L,64*R+49⟩ := @joinP table 3 1 ⟨0,8*L,16*R+13⟩ ⟨4,4*L,32*R+24⟩ ⟨1,2*L,64*R+49⟩ h2 (one18_3 L R)
  have h4 : runP table 5 ⟨0,8*L,16*R+13⟩ = some ⟨2,4*L+3,32*R+24⟩ := @joinP table 4 1 ⟨0,8*L,16*R+13⟩ ⟨1,2*L,64*R+49⟩ ⟨2,4*L+3,32*R+24⟩ h3 (one18_4 L R)
  have h5 : runP table 6 ⟨0,8*L,16*R+13⟩ = some ⟨5,8*L+4,16*R+12⟩ := @joinP table 5 1 ⟨0,8*L,16*R+13⟩ ⟨2,4*L+3,32*R+24⟩ ⟨5,8*L+4,16*R+12⟩ h4 (one18_5 L R)
  have h6 : runP table 7 ⟨0,8*L,16*R+13⟩ = some ⟨0,16*L+8,8*R+6⟩ := @joinP table 6 1 ⟨0,8*L,16*R+13⟩ ⟨5,8*L+4,16*R+12⟩ ⟨0,16*L+8,8*R+6⟩ h5 (one18_6 L R)
  have h7 : runP table 8 ⟨0,8*L,16*R+13⟩ = some ⟨1,32*L+18,4*R+3⟩ := @joinP table 7 1 ⟨0,8*L,16*R+13⟩ ⟨0,16*L+8,8*R+6⟩ ⟨1,32*L+18,4*R+3⟩ h6 (one18_7 L R)
  have h8 : runP table 9 ⟨0,8*L,16*R+13⟩ = some ⟨2,64*L+39,2*R+1⟩ := @joinP table 8 1 ⟨0,8*L,16*R+13⟩ ⟨1,32*L+18,4*R+3⟩ ⟨2,64*L+39,2*R+1⟩ h7 (one18_8 L R)
  have h9 : runP table 10 ⟨0,8*L,16*R+13⟩ = some ⟨5,128*L+77,1*R⟩ := @joinP table 9 1 ⟨0,8*L,16*R+13⟩ ⟨2,64*L+39,2*R+1⟩ ⟨5,128*L+77,1*R⟩ h8 (one18_9 L R)
  have h10 : runP table 11 ⟨0,8*L,16*R+13⟩ = some ⟨4,64*L+38,2*R⟩ := @joinP table 10 1 ⟨0,8*L,16*R+13⟩ ⟨5,128*L+77,1*R⟩ ⟨4,64*L+38,2*R⟩ h9 (one18_10 L R)
  have h11 : runP table 12 ⟨0,8*L,16*R+13⟩ = some ⟨1,32*L+19,4*R+1⟩ := @joinP table 11 1 ⟨0,8*L,16*R+13⟩ ⟨4,64*L+38,2*R⟩ ⟨1,32*L+19,4*R+1⟩ h10 (one18_11 L R)
  have h12 : runP table 13 ⟨0,8*L,16*R+13⟩ = some ⟨5,16*L+9,8*R+2⟩ := @joinP table 12 1 ⟨0,8*L,16*R+13⟩ ⟨1,32*L+19,4*R+1⟩ ⟨5,16*L+9,8*R+2⟩ h11 (one18_12 L R)
  have h13 : runP table 14 ⟨0,8*L,16*R+13⟩ = some ⟨4,8*L+4,16*R+4⟩ := @joinP table 13 1 ⟨0,8*L,16*R+13⟩ ⟨5,16*L+9,8*R+2⟩ ⟨4,8*L+4,16*R+4⟩ h12 (one18_13 L R)
  have h14 : runP table 15 ⟨0,8*L,16*R+13⟩ = some ⟨1,4*L+2,32*R+9⟩ := @joinP table 14 1 ⟨0,8*L,16*R+13⟩ ⟨4,8*L+4,16*R+4⟩ ⟨1,4*L+2,32*R+9⟩ h13 (one18_14 L R)
  have h15 : runP table 16 ⟨0,8*L,16*R+13⟩ = some ⟨2,8*L+7,16*R+4⟩ := @joinP table 15 1 ⟨0,8*L,16*R+13⟩ ⟨1,4*L+2,32*R+9⟩ ⟨2,8*L+7,16*R+4⟩ h14 (one18_15 L R)
  have h16 : runP table 17 ⟨0,8*L,16*R+13⟩ = some ⟨5,16*L+12,8*R+2⟩ := @joinP table 16 1 ⟨0,8*L,16*R+13⟩ ⟨2,8*L+7,16*R+4⟩ ⟨5,16*L+12,8*R+2⟩ h15 (one18_16 L R)
  have h17 : runP table 18 ⟨0,8*L,16*R+13⟩ = some ⟨0,32*L+24,4*R+1⟩ := @joinP table 17 1 ⟨0,8*L,16*R+13⟩ ⟨5,16*L+12,8*R+2⟩ ⟨0,32*L+24,4*R+1⟩ h16 (one18_17 L R)
  exact h17

end BB6.Agent13Raw120Late1341
