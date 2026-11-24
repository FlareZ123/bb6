import P1CarryExact
import InverseIff
import OddConeMass

namespace BB6.P1CarryExact
open BB6.Agent1Quarter BB6.Agent47P1

def left (w : Nat) : Nat := 2*w-12
def right (v : Nat) : Nat := 2*v+1

theorem legal_mass (n m v w : Nat) (hn : 14≤n) (h : LegalGap n m v w) :
    v+w+n+m+1=total n := by
  cases h with
  | root => have := total_large n hn; omega
  | edge _ _ _ _ _ _ _ _ _ _ hMass _ => exact hMass

theorem legal_to_source (n m v w : Nat) (hn : 14≤n) (h : LegalGap n m v w) :
    OddCone (14*2^n-2*n-16) 3 (left w) (right v) m := by
  induction h with
  | root =>
    have hT := total_large n hn
    have hroot : left (total n-n-2)=14*2^n-2*n-16 := by
      simp [left,total] at *
      omega
    rw [hroot]
    exact OddCone.root
  | edge m v w e v' w' h he hstart hend hMass hrec ih =>
    have hpMass := legal_mass n m v w hn h
    let t := e-1
    let k := w'-4
    let c := 2*v'-3
    have hb : 8≤left w := by simp [left]; omega
    have hb4 : left w % 4=0 := by simp [left]; omega
    have hd : right v % 2=1 := by simp [right]
    have hk : 2≤k := by dsimp [k]; omega
    have hc : c%2=1 := by dsimp [c]; omega
    have hpow : 2^e = 2^t*2 := by
      have ht : t+1=e := by dsimp [t]; omega
      rw [←ht,Nat.pow_succ]
    have hlin : c+3=2*v' := by dsimp [c]; omega
    have hpre : right v+left w/2+3+(n+m+3)=v+total n := by
      simp [left,right]; omega
    have hpoweq : right v+left w/2+3=2^t*(c+3) := by
      have hrec' : v+total n=2^t*(c+3)+(n+m+3) := by
        rw [hrec,hpow,hlin,Nat.mul_assoc]
      omega
    have hmass : 2*k+c+2*t+1+c%2=left w+right v := by
      dsimp [k,c,t,left,right]; omega
    have hi := (inverseAt_iff_power_mass (left w) (right v) t k c (by omega) hb4 hd).mpr ⟨hpoweq,hmass⟩
    have hout := OddCone.parent (left w) (right v) m t k c ih hb hb4 hd hi hk hc
    have hleft : 2*k-4=left w' := by dsimp [k,left]; omega
    have hright : c+4=right v' := by dsimp [c,right]; omega
    have heq : m+t+1=m+e := by dsimp [t]; omega
    simpa [hleft,hright,heq] using hout

/-- A surviving prefix actually reaches an endpoint at cost exactly K in
    the original inverse relation. The root is the critical P1 inverse root. -/
theorem source_prefix_to_oddcone (n : Nat) (rest : List Bool)
    (hn : 14≤n) (hK : rest.length+1≤n)
    (hmod : ((n+3)+2*weightedTail n 1 rest)%2^(rest.length+1)=1) :
    ∃ b d, OddCone (14*2^n-2*n-16) 3 b d (rest.length+1) := by
  obtain ⟨v,w,h⟩ := prefix_to_legal n rest hn hK hmod
  exact ⟨left w,right v,legal_to_source n _ v w hn h⟩

#print axioms legal_to_source
#print axioms source_prefix_to_oddcone
end BB6.P1CarryExact
