import Late1341Macro
namespace BB6.Agent13Raw120Late1341
open BB6Coverage BB6Coverage.Agent13PackedZipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ones (base : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => base * ones base n x + (base-1)

theorem ones_succ_right (base n x : Nat) : ones base n (base*x+(base-1)) = ones base (n+1) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ones, ih]

theorem repeat18 (n L R : Nat) :
    runP table (18*n) ⟨0,8*L,4*ones 4 n R+1⟩ = some ⟨0,8*ones 4 n L,4*R+1⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : runP table 18 ⟨0,8*L,4*ones 4 (n+1) R+1⟩ = some ⟨0,8*(4*L+3),4*ones 4 n R+1⟩ := by
      have hleft : 32*L+24=8*(4*L+3) := by omega
      have hright : 4*ones 4 (n+1) R+1=16*ones 4 n R+13 := by simp only [ones]; omega
      rw [hright, ← hleft]
      exact macro18 L (ones 4 n R)
    have h2 := ih (4*L+3)
    have h3 : runP table (18+18*n) ⟨0,8*L,4*ones 4 (n+1) R+1⟩ = some ⟨0,8*ones 4 n (4*L+3),4*R+1⟩ := joinP h1 h2
    rw [show 18*(n+1)=18+18*n by omega]
    rw [← ones_succ_right 4 n L]
    exact h3

theorem stepE (L R : Nat) : stepP table ⟨4,2*L+1,R⟩ = some ⟨4,L,2*R+1⟩ := by
  have h0 : (2*L+1)%2=1 := by omega
  have h1 : (2*L+1)/2=L := by omega
  have hread : readP ⟨4,2*L+1,R⟩ = (4,true) := by simp [readP,h0]
  have htable : table (4,true) = some (some ⟨true,false,4⟩) := rfl
  unfold stepP
  rw [hread,htable]
  simp [moveP,h1]
  <;> omega

theorem repeatE (n L R : Nat) : runP table n ⟨4,ones 2 n L,R⟩ = some ⟨4,L,ones 2 n R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [runP]
    change (stepP table ⟨4,2*ones 2 n L+1,R⟩).bind (runP table n) = _
    rw [stepE]
    simp only [Option.bind_some]
    rw [← ones_succ_right 2 n R]
    exact ih (2*R+1)

#print axioms repeat18
#print axioms repeatE
end BB6.Agent13Raw120Late1341
