import CascadeOdd

namespace ReverseResidue

theorem pow3_even (k : Nat) : 2^(2*k)%3=1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have he : 2*(k+1)=2*k+2 := by omega
    rw [he,Nat.pow_add,Nat.mul_mod]
    have h4 : 2^2%3=1 := by decide
    rw [ih,h4]

theorem pow3_parity (n : Nat) :
    (n%2=0 → 2^n%3=1) ∧ (n%2=1 → 2^n%3=2) := by
  constructor
  · intro hn
    have he : n=2*(n/2) := by omega
    rw [he]
    exact pow3_even (n/2)
  · intro hn
    have he : n=2*(n/2)+1 := by omega
    rw [he,Nat.pow_succ,Nat.mul_mod]
    rw [pow3_even]

theorem mod3_ancestor (n i : Nat) (hn : 4≤n)
    (hc : n%6=0∨n%6=1∨n%6=2∨n%6=3)
    (hpos : CascadeOdd.ancestor (2^(n-1)) n i + (2*n+3)*2^i =
      8*2^(n-1)+n-1) :
    CascadeOdd.ancestor (2^(n-1)) n i %3 ≠ 2 := by
  let t:=CascadeOdd.ancestor (2^(n-1)) n i
  let p:=2^(n-1)
  change t%3 ≠ 2
  have hnsub : n-1+1=n := by omega
  have hnres : (n-1)%2=0∨(n-1)%2=1 := by omega
  have hp2 := pow3_parity (n-1)
  have hp : p%3=1∨p%3=2 := by
    rcases hnres with he|ho
    · left; exact hp2.1 he
    · right; exact hp2.2 ho
  have hi2:=pow3_parity i
  have hipar : i%2=0∨i%2=1 := by omega
  have hi : 2^i%3=1∨2^i%3=2 := by
    rcases hipar with he|ho
    · left; exact hi2.1 he
    · right; exact hi2.2 ho
  have hEq : (t%3+(2*n+3)%3*(2^i%3))%3 =
      (8*(p%3)+(n-1)%3)%3 := by
    have hbase : t+(2*n+3)*2^i=8*p+n-1 := hpos
    have hnprod : 8*p+n-1+n-(n-1)=8*p+n := by omega
    have hno : 8*p+n-1=8*p+(n-1) := by omega
    rw [hno] at hbase
    have heq:=congrArg (fun x : Nat => x%3) hbase
    simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_mod] using heq
  rcases hc with h0|h1|h2|h3
  · have hnp : (n-1)%2=1 := by omega
    have hpp : p%3=2 := hp2.2 hnp
    have hk : (2*n+3)%3=0 := by omega
    have hnp3 : (n-1)%3=2 := by omega
    rcases hi with hi|hi
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
  · have hnp : (n-1)%2=0 := by omega
    have hpp : p%3=1 := hp2.1 hnp
    have hk : (2*n+3)%3=2 := by omega
    have hnp3 : (n-1)%3=0 := by omega
    rcases hi with hi|hi
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
  · have hnp : (n-1)%2=1 := by omega
    have hpp : p%3=2 := hp2.2 hnp
    have hk : (2*n+3)%3=1 := by omega
    have hnp3 : (n-1)%3=1 := by omega
    rcases hi with hi|hi
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
  · have hnp : (n-1)%2=0 := by omega
    have hpp : p%3=1 := hp2.1 hnp
    have hk : (2*n+3)%3=0 := by omega
    have hnp3 : (n-1)%3=2 := by omega
    rcases hi with hi|hi
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega
    · simp only [hi,hk,hpp,hnp3] at hEq
      omega

#print axioms mod3_ancestor
end ReverseResidue
