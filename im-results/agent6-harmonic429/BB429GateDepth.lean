import Lean.Elab.Tactic.Omega
namespace GateDepth
private theorem two_pow_multiple (k d : Nat) (hd : d ≤ k) :
    2^k = 2^d * 2^(k-d) := by
  calc
    2^k = 2^(d+(k-d)) := by congr 1; omega
    _ = 2^d*2^(k-d) := Nat.pow_add 2 d (k-d)

private theorem modbound_637 (t u k : Nat)
    (h : (u+3)*2^k=1024*t+640) : k≤7 := by
  by_cases hk : k≤7
  · exact hk
  · have he := two_pow_multiple k 8 (by omega)
    have he2 : 2^k = 256*2^(k-8) := by simpa only [show (2:Nat)^8=256 by decide] using he
    rw [he2] at h
    have hh : (u+3)*(256*2^(k-8))=256*((u+3)*2^(k-8)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hh] at h
    omega

private theorem modbound_765 (t u k : Nat)
    (h : (u+3)*2^k=1024*t+768) : k≤8 := by
  by_cases hk : k≤8
  · exact hk
  · have he := two_pow_multiple k 9 (by omega)
    have he2 : 2^k = 512*2^(k-9) := by simpa only [show (2:Nat)^9=512 by decide] using he
    rw [he2] at h
    have hh : (u+3)*(512*2^(k-9))=512*((u+3)*2^(k-9)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hh] at h
    omega

private theorem modbound_893 (t u k : Nat)
    (h : (u+3)*2^k=1024*t+896) : k≤7 := by
  by_cases hk : k≤7
  · exact hk
  · have he := two_pow_multiple k 8 (by omega)
    have he2 : 2^k = 256*2^(k-8) := by simpa only [show (2:Nat)^8=256 by decide] using he
    rw [he2] at h
    have hh : (u+3)*(256*2^(k-8))=256*((u+3)*2^(k-8)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hh] at h
    omega

theorem only_765_depths (t u k : Nat)
    (h : (u+3)*2^k=1024*t+768)
    (hpar : (u%2=1 ∧ k%4=1) ∨ (u%2=0 ∧ k%4=3)) : k=1 ∨ k=5 := by
  have hk := modbound_765 t u k h
  have all : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases all with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 <;>
    subst k <;> simp only [show (2:Nat)^0=1 by decide,show (2:Nat)^1=2 by decide,
    show (2:Nat)^2=4 by decide,show (2:Nat)^3=8 by decide,
    show (2:Nat)^4=16 by decide,show (2:Nat)^5=32 by decide,
    show (2:Nat)^6=64 by decide,show (2:Nat)^7=128 by decide,
    show (2:Nat)^8=256 by decide] at h <;> omega

theorem only_893_depths (t u k : Nat)
    (h : (u+3)*2^k=1024*t+896)
    (hpar : (u%2=1 ∧ k%4=1) ∨ (u%2=0 ∧ k%4=3)) :
    k=1 ∨ k=5 ∨ k=7 := by
  have hk := modbound_893 t u k h
  have all : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases all with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;>
    subst k <;> simp only [show (2:Nat)^0=1 by decide,show (2:Nat)^1=2 by decide,
    show (2:Nat)^2=4 by decide,show (2:Nat)^3=8 by decide,
    show (2:Nat)^4=16 by decide,show (2:Nat)^5=32 by decide,
    show (2:Nat)^6=64 by decide,show (2:Nat)^7=128 by decide] at h <;> omega

theorem only_637_depths (t u k : Nat)
    (h : (u+3)*2^k=1024*t+640)
    (hpar : (u%2=1 ∧ k%4=1) ∨ (u%2=0 ∧ k%4=3)) :
    k=1 ∨ k=5 ∨ k=7 := by
  have hk := modbound_637 t u k h
  have all : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases all with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;>
    subst k <;> simp only [show (2:Nat)^0=1 by decide,show (2:Nat)^1=2 by decide,
    show (2:Nat)^2=4 by decide,show (2:Nat)^3=8 by decide,
    show (2:Nat)^4=16 by decide,show (2:Nat)^5=32 by decide,
    show (2:Nat)^6=64 by decide,show (2:Nat)^7=128 by decide] at h <;> omega

private theorem pow_le_of_le (k d : Nat) (h : k≤d) : 2^k≤2^d :=
  Nat.pow_le_pow_right (by omega) h

theorem nonfirst_765_depths (t u w k : Nat)
    (ha : (u+3)*2^k=1024*t+768)
    (hw : w%2=0)
    (hg : 2*u+w+3*k+13=4*((u+3)*2^k))
    (hpar : 0<u → (u%2=1 ∧ k%4=1) ∨ (u%2=0 ∧ k%4=3)) :
    0<u ∧ (k=1 ∨ k=5) := by
  have hb := modbound_765 t u k ha
  by_cases hz : u=0
  · subst u
    have hk8 : k=8 := by
      by_cases hk7 : k≤7
      · have hm : 2^k≤128 := by
          simpa only [show (2:Nat)^7=128 by decide] using pow_le_of_le k 7 hk7
        omega
      · omega
    subst k
    simp only [show (2:Nat)^8=256 by decide] at ha hg
    omega
  · have hu : 0<u := by omega
    exact ⟨hu, only_765_depths t u k ha (hpar hu)⟩

theorem nonfirst_637_depths (t u w k : Nat)
    (ha : (u+3)*2^k=1024*t+640)
    (hw : w%2=0)
    (hg : 2*u+w+3*k+13=4*((u+3)*2^k))
    (hpar : 0<u → (u%2=1 ∧ k%4=1) ∨ (u%2=0 ∧ k%4=3)) :
    0<u ∧ (k=1 ∨ k=5 ∨ k=7) := by
  have hb := modbound_637 t u k ha
  by_cases hz : u=0
  · subst u
    have hm : 2^k≤128 := by
      simpa only [show (2:Nat)^7=128 by decide] using pow_le_of_le k 7 hb
    omega
  · have hu : 0<u := by omega
    exact ⟨hu, only_637_depths t u k ha (hpar hu)⟩

theorem nonfirst_893_depths (t u w k : Nat)
    (ha : (u+3)*2^k=1024*t+896)
    (hw : w%2=0)
    (hg : 2*u+w+3*k+13=4*((u+3)*2^k))
    (hpar : 0<u → (u%2=1 ∧ k%4=1) ∨ (u%2=0 ∧ k%4=3)) :
    0<u ∧ (k=1 ∨ k=5 ∨ k=7) := by
  have hb := modbound_893 t u k ha
  by_cases hz : u=0
  · subst u
    have hm : 2^k≤128 := by
      simpa only [show (2:Nat)^7=128 by decide] using pow_le_of_le k 7 hb
    omega
  · have hu : 0<u := by omega
    exact ⟨hu, only_893_depths t u k ha (hpar hu)⟩

#print axioms nonfirst_765_depths
#print axioms nonfirst_637_depths
#print axioms nonfirst_893_depths
#print axioms only_765_depths
#print axioms only_893_depths
#print axioms only_637_depths
end GateDepth
