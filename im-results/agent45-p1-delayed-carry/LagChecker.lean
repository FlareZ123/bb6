import LagCore
import BitCarry
namespace BB6.Agent45.DelayedCarry
open BB6.Agent28BitCarry (packEven packEven_sound)

abbrev Prefix := Nat × Nat

inductive Extend (n s B a : Nat) : Nat → Nat → Nat → Prop
  | nil : Extend n s B a 0 B a
  | step (k C c x d : Nat) (h : Extend n s B a k C c) (hx : x≤1)
      (he : 2*d+target n (s+k) C = c+x*(n+(s+k)+3)) :
      Extend n s B a (k+1) (C+2^(s+k)*x) d

theorem extend_trace (n s B a k C c : Nat) (h : Trace n s B a)
    (he : Extend n s B a k C c) : Trace n (s+k) C c := by
  induction he with
  | nil => simpa using h
  | step k C c x d hE hx hh ih =>
    simpa [Nat.add_assoc] using Trace.step (s+k) C c x d ih hx hh

theorem extend_mod (n s B a k C c : Nat) (h : Extend n s B a k C c) :
    ∃ R, C=B+2^s*R := by
  induction h with
  | nil => exact ⟨0,by simp⟩
  | step k C c x d h hx he ih =>
    obtain ⟨R,hR⟩ := ih
    refine ⟨R+2^k*x,?_⟩
    rw [hR,Nat.pow_add,Nat.mul_add]; ac_rfl

theorem extend_prefix (n s B a k C c j : Nat) (h : Extend n s B a k C c)
    (hj : j≤k) : ∃ D d, Extend n s B a j D d := by
  induction h with
  | nil => have hj0 : j=0 := by omega
           subst j; exact ⟨B,a,Extend.nil⟩
  | step k C c x d h hx he ih =>
    by_cases hlt : j≤k
    · exact ih hlt
    · have hj' : j=k+1 := by omega
      subst j
      exact ⟨_,_,Extend.step k C c x d h hx he⟩

theorem extend_append (n s B a k C c j D d : Nat) (h : Extend n s B a k C c)
    (he : Extend n (s+k) C c j D d) : Extend n s B a (k+j) D d := by
  induction he with
  | nil => simpa using h
  | step j D d x e he hx hh ih =>
    simpa only [Nat.add_assoc] using
      Extend.step (k+j) D d x e ih hx (by simpa only [Nat.add_assoc] using hh)

theorem trace_split (n m B a s : Nat) (h : Trace n m B a)
    (hs : 1≤s) (hsm : s≤m) :
    ∃ C c, Trace n s C c ∧ Extend n s C c (m-s) B a := by
  induction h with
  | first =>
    have hs1 : s=1 := by omega
    subst s
    exact ⟨1,(n+2)/2,Trace.first,Extend.nil⟩
  | step i B a x c h hx he ih =>
    by_cases hsi : s≤i
    · obtain ⟨C,d,htr,hE⟩ := ih hsi
      have hidx : s+(i-s)=i := by omega
      have hk : i+1-s=(i-s)+1 := by omega
      refine ⟨C,d,htr,?_⟩
      rw [hk]
      have he' : 2*c+target n (s+(i-s)) B=a+x*(n+(s+(i-s))+3) := by simpa [hidx] using he
      have hstep := Extend.step (i-s) B a x c hE hx he'
      simpa only [hidx] using hstep
    · have hs' : s=i+1 := by omega
      subst s
      exact ⟨_,_,Trace.step i B a x c h hx he,by simpa using (Extend.nil : Extend n (i+1) (B+2^i*x) c 0 (B+2^i*x) c)⟩

def lowStep (n i : Nat) (p : Prefix) : List Prefix :=
  [0,1].filterMap fun x =>
    let t := p.2+x*(n+i+3)
    let y := target n i p.1
    if y≤t ∧ (t-y)%2=0 then some (p.1+2^i*x,(t-y)/2) else none

theorem lowStep_sound (n i B a x c : Nat) (hx : x≤1)
    (he : 2*c+target n i B=a+x*(n+i+3)) :
    (B+2^i*x,c) ∈ lowStep n i (B,a) := by
  unfold lowStep
  apply List.mem_filterMap.mpr
  refine ⟨x,?_,?_⟩
  · simp; omega
  · have hle : target n i B≤a+x*(n+i+3) := by omega
    have hsub : a+x*(n+i+3)-target n i B=2*c := by omega
    simp [hle,hsub]

def advance (n s : Nat) (ps : List Prefix) : Nat → List Prefix
  | 0 => ps
  | k+1 => (advance n s ps k).flatMap (lowStep n (s+k))

theorem extend_in_advance (n s B a k C c : Nat) (ps : List Prefix)
    (hp : (B,a)∈ps) (h : Extend n s B a k C c) : (C,c)∈advance n s ps k := by
  induction h with
  | nil => exact hp
  | step k C c x d h hx he ih =>
    apply List.mem_flatMap.mpr
    exact ⟨(C,c),ih,lowStep_sound n (s+k) C c x d hx he⟩

def lagStep (L weight y bits : Nat) : Nat := packEven L ((bits ||| (bits <<< weight)) >>> y)

theorem lagStep_sound (L weight y bits a x c : Nat) (hx : x≤1)
    (hc : c<2^L) (ha : bits.testBit a=true) (he : 2*c+y=a+x*weight) :
    (lagStep L weight y bits).testBit c=true := by
  unfold lagStep
  apply packEven_sound L _ c hc
  rw [Nat.testBit_shiftRight,Nat.testBit_or]
  have hx' : x=0 ∨ x=1 := by omega
  rcases hx' with h0|h1
  · subst x; simp at he
    have h : y+2*c=a := by omega
    simp [h,ha]
  · subst x; simp at he
    have hh : weight≤y+2*c := by omega
    have hh' : y+2*c-weight=a := by omega
    rw [Nat.testBit_shiftLeft]
    simp [hh,hh',ha]

def fixedRun (L n B i bits : Nat) : Nat → Nat
  | 0 => bits
  | k+1 => if bits=0 then 0 else
      fixedRun L n B (i+1) (lagStep L (n+i+3) (target n i B) bits) k

theorem fixedRun_zero (L n B i k : Nat) : fixedRun L n B i 0 k=0 := by
  cases k <;> simp [fixedRun]

theorem fixedRun_add (L n B i bits k j : Nat) :
    fixedRun L n B i bits (k+j) = fixedRun L n B (i+k) (fixedRun L n B i bits k) j := by
  induction k generalizing i bits with
  | zero => simp [fixedRun]
  | succ k ih =>
    by_cases hz : bits=0
    · subst bits
      simp [fixedRun_zero]
    · rw [Nat.succ_add,fixedRun,fixedRun,if_neg hz,if_neg hz,ih]
      congr 1
      omega

def lookahead (L n s B a k : Nat) : Nat := fixedRun L n B s (2^a) k

theorem lookahead_succ (L n s B a k : Nat) :
    lookahead L n s B a (k+1) =
      if lookahead L n s B a k=0 then 0 else
        lagStep L (n+s+k+3) (target n (s+k) B) (lookahead L n s B a k) := by
  unfold lookahead
  rw [fixedRun_add]
  simp [fixedRun,Nat.add_assoc]

theorem lookahead_sound (L n s B a k C c : Nat) (h : Trace n s B a)
    (he : Extend n s B a k C c) (hk : k≤n) (hbound : n+s+k+2<2^L) :
    (lookahead L n s B a k).testBit c=true := by
  induction he with
  | nil => exact Nat.testBit_two_pow_self
  | step k C c x d hE hx he ih =>
    have hbit := ih (by omega) (by omega)
    have hnon : lookahead L n s B a k ≠ 0 := by
      intro hz; rw [hz] at hbit; simp at hbit
    obtain ⟨R,hR⟩ := extend_mod n s B a k C c hE
    have htarget := target_prefix n s (s+k) B R (by omega)
    rw [← hR] at htarget
    rw [htarget] at he
    have htrace := extend_trace n s B a (k+1) (C+2^(s+k)*x) d h
      (Extend.step k C c x d hE hx (by rw [htarget]; exact he))
    have hd := (trace_bounds n (s+(k+1)) _ d htrace).2.2.2
    simp only [lookahead_succ, if_neg hnon]
    exact lagStep_sound L (n+s+k+3) (target n (s+k) B) _ c x d hx (by omega) hbit (by simpa [Nat.add_assoc] using he)

def Covered (n s : Nat) (ps : List Prefix) : Prop :=
  ∀ B a C c, Trace n s B a → Extend n s B a n C c → (B,a)∈ps

def nextBlock (L n s h : Nat) (ps : List Prefix) : List Prefix :=
  (advance n s ps h).filter fun p => lookahead L n (s+h) p.1 p.2 n != 0

theorem covered_first (n : Nat) : Covered n 1 [(1,(n+2)/2)] := by
  intro B a C c h he
  cases h with
  | first => simp
  | step i B a x c h hx he =>
    have hi := (trace_bounds n _ _ _ h).1
    omega

theorem covered_next (L n s h : Nat) (ps : List Prefix) (hS : 1≤s)
    (hb : 2*n+s+h+2<2^L) (hcover : Covered n s ps) :
    Covered n (s+h) (nextBlock L n s h ps) := by
  intro B a C c htr hE
  obtain ⟨D,d,hpre,hExt⟩ := trace_split n (s+h) B a s htr hS (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  have hfull := extend_append n s D d h B a n C c hExt' hE
  obtain ⟨F,f,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hm := hcover D d F f hpre hshort
  have hm' := extend_in_advance n s D d h B a ps hm hExt'
  have hbit := lookahead_sound L n (s+h) B a n C c htr hE (by omega) (by omega)
  have hz : lookahead L n (s+h) B a n ≠ 0 := by intro he; rw [he] at hbit; simp at hbit
  simp [nextBlock,hm',hz]

theorem no_trace_of_empty (n s : Nat) (hs : 1≤s) (h : Covered n s []) :
    ∀ m B a, n+s≤m → ¬ Trace n m B a := by
  intro m B a hm ht
  obtain ⟨C,c,hC,hE⟩ := trace_split n m B a s ht hs (by omega)
  obtain ⟨D,d,hExt⟩ := extend_prefix n s C c (m-s) B a n hE (by omega)
  have hh := h C c D d hC hExt
  simp at hh

#print axioms covered_next
#print axioms no_trace_of_empty
end BB6.Agent45.DelayedCarry
