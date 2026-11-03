import Root119ShuttleSupport

namespace BB6Root119

/-- Exact D-to-F round trip: an odd number of consecutive ones followed by zero.
    All cells in the swept interval become one; exterior cells remain unchanged. -/
theorem shuttle (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*n+1 → t (h+(j:Int)) = true)
    (zero : t (h+(2*n+1:Int)) = false) :
    shuttleRun (4*n+3) ⟨.D,h,t⟩ =
    some ⟨.F,h-1, shuttleFill t h (2*n+2)⟩ := by
  induction n generalizing t h with
  | zero =>
    have h0 : t h = true := by simpa using ones 0 (by omega)
    have h1 : t (h+1) = false := by simpa using zero
    let t1 := setBit t h true
    let u := setBit t1 (h+1) true
    have fRead : t1 (h+1) = false := by
      have hne : h+1 ≠ h := by omega
      simp [t1,setBit,hne,h1]
    have hu : u h = true := by
      have hne : h ≠ h+1 := by omega
      simp [u,t1,setBit,hne,h0]
    have hs1 : next ⟨Q.D,h,t⟩ = some ⟨Q.F,h+1,t1⟩ := by
      simp [next,h0,t1]
    have hs2 : next ⟨Q.F,h+1,t1⟩ = some ⟨Q.B,h,u⟩ := by
      simp [next,fRead,u]
    have hs3 : next ⟨Q.B,h,u⟩ = some ⟨Q.F,h-1,u⟩ := by
      have hh := shuttleSetBit_same u h true hu
      simp [next,hu,hh]
    have full : u = shuttleFill t h 2 := shuttleFill_two t h
    have hr : shuttleRun 3 ⟨Q.D,h,t⟩ = some ⟨Q.F,h-1,u⟩ := by
      simp [shuttleRun,hs1,hs2,hs3]
    simpa only [full] using hr
  | succ n ih =>
    have h0 : t h = true := by
      simpa using ones 0 (by omega)
    have h1 : t (h+1) = true := by
      simpa using ones 1 (by omega)
    let t2 := setBit (setBit t h true) (h+1) false
    have hinner : ∀ j : Nat, j < 2*n+1 → t2 (h+2+(j:Int)) = true := by
      intro j hj
      have hi : 2+j < 2*(n+1)+1 := by omega
      have heq : h+2+(j:Int) = h+((2+j:Nat):Int) := by omega
      have hsrc := ones (2+j) hi
      have ne0 : h+2+(j:Int) ≠ h := by omega
      have ne1 : h+2+(j:Int) ≠ h+1 := by omega
      have ha : t2 (h+2+(j:Int)) = t (h+2+(j:Int)) := by
        simp [t2,setBit,ne0,ne1] <;> omega
      rw [ha,heq]
      exact hsrc
    have hz : t2 (h+2+(2*n+1:Int)) = false := by
      have heq : h+2+(2*n+1:Int) = h+(2*(n+1)+1:Int) := by omega
      have ne0 : h+2+(2*n+1:Int) ≠ h := by omega
      have ne1 : h+2+(2*n+1:Int) ≠ h+1 := by omega
      have ha : t2 (h+2+(2*n+1:Int)) = t (h+2+(2*n+1:Int)) := by
        simp [t2,setBit,ne0,ne1] <;> omega
      rw [ha,heq]
      exact zero
    have hF := ih t2 (h+2) hinner hz
    have hF0 : (shuttleFill t2 (h+2) (2*n+2)) (h+1) = false := by
      rw [shuttleFill_outside]
      · simp [t2,setBit]
      · left;omega
    have hB1 : (setBit (shuttleFill t2 (h+2) (2*n+2)) (h+1) true) h = true := by
      have ne : h ≠ h+1 := by omega
      have fl : (shuttleFill t2 (h+2) (2*n+2)) h = t2 h := by
        exact shuttleFill_outside t2 (h+2) h (2*n+2) (Or.inl (by omega))
      have hh : t2 h = true := by
        simp [t2,setBit,ne]
      simp [setBit,ne,fl,hh]
    have hstart2 : shuttleRun 2 ⟨Q.D,h,t⟩ = some ⟨Q.D,h+2,t2⟩ := by
      let t1 := setBit t h true
      have fRead : t1 (h+1) = true := by
        have hn : h+1 ≠ h := by omega
        simp [t1,setBit,hn,h1]
      have hs1 : next ⟨Q.D,h,t⟩ = some ⟨Q.F,h+1,t1⟩ := by
        simp [next,h0,t1]
      have hs2 : next ⟨Q.F,h+1,t1⟩ = some ⟨Q.D,h+2,t2⟩ := by
        simp [next,fRead,t2,t1]
        omega
      simpa [shuttleRun,hs1,hs2]
    have hlast2 : shuttleRun 2 ⟨Q.F,h+1,shuttleFill t2 (h+2) (2*n+2)⟩ =
      some ⟨Q.F,h-1,setBit (setBit (shuttleFill t2 (h+2) (2*n+2)) (h+1) true) h true⟩ := by
      let t3 := shuttleFill t2 (h+2) (2*n+2)
      let t4 := setBit t3 (h+1) true
      have hs1 : next ⟨Q.F,h+1,t3⟩ = some ⟨Q.B,h,t4⟩ := by
        simp [next,hF0,t3,t4]
      have hs2 : next ⟨Q.B,h,t4⟩ = some ⟨Q.F,h-1,setBit t4 h true⟩ := by
        have hb : t4 h = true := hB1
        simp [next,hb]
      simpa [shuttleRun,hs1,hs2,t3,t4]
    have hsimpl : 4*(n+1)+3 = 2 + ((4*n+3)+2) := by omega
    have hshift := shuttleFill_shift t h n
    calc
      shuttleRun (4*(n+1)+3) ⟨Q.D,h,t⟩ =
          (shuttleRun 2 ⟨Q.D,h,t⟩).bind (shuttleRun ((4*n+3)+2)) := by
        rw [hsimpl,shuttleRun_add]
      _ = (shuttleRun (4*n+3) ⟨Q.D,h+2,t2⟩).bind (shuttleRun 2) := by
        simp only [hstart2,Option.bind_some,shuttleRun_add]
      _ = shuttleRun 2 ⟨Q.F,h+1,shuttleFill t2 (h+2) (2*n+2)⟩ := by
        rw [hF]
        simp only [Option.bind_some]
        have hh : h+2-1 = h+1 := by omega
        rw [hh]
      _ = some ⟨Q.F,h-1,setBit (setBit (shuttleFill t2 (h+2) (2*n+2)) (h+1) true) h true⟩ :=
        hlast2
      _ = some ⟨Q.F,h-1,shuttleFill t h (2*(n+1)+2)⟩ := by rw [hshift]

#print axioms BB6Root119.shuttle
end BB6Root119
