import ReverseBlockCompose
import LagCore
namespace BB6.Agent45ReverseBlock
open BB6.Agent45.DelayedCarry (Trace target target_bound target_prefix trace_bounds)

/-- Delayed target digits in forward chronological order. -/
def targetWord (n s B : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => targetWord n s B k ++ [target n (s+k) B]

@[simp] theorem targetWord_length (n s B k : Nat) : (targetWord n s B k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [targetWord,ih]

theorem targetWord_bits (n s B k : Nat) : ∀ y∈targetWord n s B k,y≤1 := by
  induction k with
  | zero => simp [targetWord]
  | succ k ih =>
    intro y hy
    simp only [targetWord,List.mem_append,List.mem_singleton] at hy
    rcases hy with h|rfl
    · exact ih y h
    · exact target_bound _ _ _

/-- A genuine trace rewinds to its low prefix, using only that prefix's
    target digits, for every window of length at most n. -/
theorem trace_rewind {n m B a : Nat} (h : Trace n m B a) (s : Nat)
    (hs : 1≤s) (hm : s≤m) (hk : m-s≤n) :
    ∃ C c R, Trace n s C c ∧ B=C+2^s*R ∧
      Walk (n+m+3) a (targetWord n s C (m-s)) c := by
  induction h with
  | first =>
    have h1 : s=1 := by omega
    subst s
    exact ⟨1,(n+2)/2,0,Trace.first,by simp,Walk.nil (by omega)⟩
  | step i B a x d h hx he ih =>
    by_cases hsi : s≤i
    · obtain ⟨C,c,R,htr,hB,hw⟩ := ih hsi (by omega)
      have hi := (trace_bounds n i B a h).2.2.2
      have hy := target_bound n i B
      have hd : d<n+i+3 := by
        rcases (show x=0 ∨ x=1 by omega) with h0|h1 <;> subst x <;> simp at he <;> omega
      have htarget : target n i B=target n i C := by rw [hB]; exact target_prefix n s i C R (by omega)
      have hpre := prepend hw d (target n i B) x hd (by omega) hy hx (by simpa [Nat.mul_comm] using he)
      have hp : (2:Nat)^i=2^s*2^(i-s) := by rw [← Nat.pow_add]; congr 1 <;> omega
      refine ⟨C,c,R+2^(i-s)*x,htr,?_,?_⟩
      · rw [hB,hp,Nat.mul_add]; ac_rfl
      · rw [show i+1-s=(i-s)+1 by omega,targetWord,show s+(i-s)=i by omega,← htarget]
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hpre
    · have hsi' : s=i+1 := by omega
      subst s
      have hh := Trace.step i B a x d h hx he
      have hd := (trace_bounds n (i+1) _ d hh).2.2.2
      exact ⟨B+2^i*x,d,0,hh,by simp,by simpa [targetWord] using (Walk.nil (F:=n+(i+1)+3) (z:=d) (by omega))⟩

/-- Exact segmented reverse-live test for every genuine trace prefix.
    The caller chooses any fitted partition of the delayed target word. -/
theorem trace_block_live {n m B a : Nat} (h : Trace n m B a) (s : Nat)
    (hs : 1≤s) (hm : s≤m) (hk : m-s≤n) :
    ∃ C c R, Trace n s C c ∧ B=C+2^s*R ∧
    ∀ bs : List (List Nat), bs.flatten=targetWord n s C (m-s) →
       Fitted (n+s+3) bs →
       c∈blockFold (n+s+3) bs (List.range (n+m+3)) := by
  obtain ⟨C,c,R,htr,hB,hw⟩ := trace_rewind h s hs hm hk
  refine ⟨C,c,R,htr,hB,?_⟩
  intro bs hbs hf
  have hy : ∀ y∈bs.flatten,y≤1 := by rw [hbs]; exact targetWord_bits _ _ _ _
  apply (mem_blockFold _ _ _ _ hy hf).mpr
  refine ⟨a,List.mem_range.mpr (start_bound hw),?_⟩
  rw [hbs,targetWord_length,show n+s+3+(m-s)=n+m+3 by omega]
  exact hw

#print axioms trace_rewind
#print axioms trace_block_live
end BB6.Agent45ReverseBlock
