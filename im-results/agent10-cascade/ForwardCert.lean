import ResetChain
import ResetParentStrict
import FastShield

namespace CascadeResetInverse
open CascadeFastShield CascadeManyShield CascadeSweep

/-- Determinism of genuine first-reset edges, inherited from the exact
    original source-C first-outcome semantics. -/
private theorem parent_unique (h u v:Nat)
    (hp:ResetParent h u) (hq:ResetParent h v):u=v := by
  have he := outcome_unique
    ((reset_parent_iff h u).mpr hp) ((reset_parent_iff h v).mpr hq)
  exact Option.some.inj he

private theorem chain_mono {start u:Nat} (hr:ResetChain start u):start≤u:=by
  induction hr with
  | root => omega
  | append hr hp ih =>
      have hs:=reset_parent_strict _ _ hp
      omega

private theorem chain_split {start u:Nat} (hr:ResetChain start u):
    u=start ∨ ∃v, ResetParent start v ∧ ResetChain v u := by
  induction hr with
  | root => exact Or.inl rfl
  | @append h w hr hp ih =>
    rcases ih with he | ⟨v,hfirst,hrest⟩
    · subst h
      exact Or.inr ⟨w,hp,ResetChain.root⟩
    · exact Or.inr ⟨v,hfirst,ResetChain.append hrest hp⟩

/-- Explicit source-indexed first-reset edge, with complete arithmetic
    witness. A claimed link is checked solely by Boolean arithmetic. -/
inductive Link where
  | even (u k:Nat) : Link
  | odd (u k t d:Nat) : Link

def Link.target : Link→Nat
  | .even u _ => u
  | .odd u _ _ _ => u

def Link.valid (h:Nat) : Link→Bool
  | .even u k =>
      decide (6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+h+k)
  | .odd u k t d =>
      decide (d%2=1 ∧ 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1 ∧
        2*u+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+h+k+5)

theorem Link.valid_sound (h:Nat) (l:Link)(hv:l.valid h=true):
    ResetParent h l.target := by
  cases l with
  | even u k =>
    have hh : 6*2^k-1≤u ∧ u≤8*2^k-3 ∧
        2*u=8*2^k+h+k := of_decide_eq_true hv
    exact Or.inl ⟨k,⟨hh.1,hh.2.1⟩,hh.2.2⟩
  | odd u k t d =>
    have hh : d%2=1 ∧ 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1 ∧
        2*u+5=3^(t+1)*d ∧ 2*(2^t*d)=8*2^k+h+k+5 := of_decide_eq_true hv
    exact Or.inr ⟨k,t,d,hh.1,⟨hh.2.1,hh.2.2.1⟩,hh.2.2.2.1,hh.2.2.2.2⟩

/-- A certified finite first-reset path from h to v which has visited no
    target of the bounded fatal family. -/
inductive SafeTail (N:Nat) : Nat→Nat→Prop where
  | stop (h:Nat) (hsafe:badFast N (h,0)=false):SafeTail N h h
  | step {h v u:Nat} (hp:ResetParent h v)
      (hsafe:badFast N (h,0)=false)
      (ht:SafeTail N v u):SafeTail N h u

def endHeight (h:Nat) : List Link→Nat
  | []=>h
  | x::xs=>endHeight x.target xs

def checkSeq (N h:Nat) : List Link→Bool
  | []=>!(badFast N (h,0))
  | x::xs=>x.valid h && !(badFast N (h,0)) && checkSeq N x.target xs

/-- The generator is entirely untrusted: even malformed link data cannot
    pass because every exact arithmetic edge and every fatal gate is
    rechecked in Lean's kernel. -/
theorem checkSeq_sound (N:Nat) (h:Nat) (xs:List Link)
    (hc:checkSeq N h xs=true):SafeTail N h (endHeight h xs) := by
  induction xs generalizing h with
  | nil =>
    have hs : badFast N (h,0)=false := by
      cases hv:badFast N (h,0) <;> simp [checkSeq,hv] at hc ⊢
    exact SafeTail.stop h hs
  | cons x xs ih =>
    have hh : (x.valid h=true ∧ !(badFast N (h,0))=true) ∧
        checkSeq N x.target xs=true := by
      simpa [checkSeq, Bool.and_eq_true] using hc
    have hs : badFast N (h,0)=false := by
      cases hv:badFast N (h,0) <;> simp [hv] at hh ⊢
    exact SafeTail.step (Link.valid_sound h x hh.1.1) hs
      (ih x.target hh.2)

theorem SafeTail.trans {N h v u:Nat}
    (hv:SafeTail N h v) (hu:SafeTail N v u) : SafeTail N h u := by
  induction hv with
  | stop h hs => exact hu
  | step hp hs ht ih => exact SafeTail.step hp hs (ih hu)

/-- Deterministic-forward shielding: any genuine reset chain from the same
    root either avoids the bounded fatal set or lies above the end height
    of the explicitly checked safe forward prefix. -/
theorem SafeTail.cover {N h v u:Nat}
    (hv:SafeTail N h v) (hu:ResetChain h u) :
    badFast N (u,0)=false ∨ v≤u := by
  induction hv generalizing u with
  | stop h hs =>
    right
    exact chain_mono hu
  | @step h w v hp hs ht ih =>
    rcases chain_split hu with he | ⟨z,hfirst,hrest⟩
    · left
      rwa [he]
    · have hz:w=z:=parent_unique h w z hp hfirst
      subst z
      exact ih hrest

/-- A single safe forward prefix, exceeding c_N, excludes every fatal
    reset of index <=N at every time of the genuine blank-root reset orbit. -/
theorem safePrefix_excludes {N h v:Nat} (hr:SafeTail N h v)
    (hlarge:fatal N<v) (n:Nat) (hn:4≤n) (ht:n≤N)
    (hc:n%6=4∨n%6=5) : ¬ResetChain h (fatal n) := by
  intro hh
  obtain hb | hbound := SafeTail.cover hr hh
  · have hyes := badFast_hits N n hn ht hc
    rw [hyes] at hb
    contradiction
  · have hle := fatal_mono n N ht
    omega

theorem safePrefix_excludes_root {N v:Nat}
    (hr:SafeTail N 2 v) (hlarge:fatal N<v)
    (n:Nat) (hn:4≤n) (ht:n≤N)
    (hc:n%6=4∨n%6=5) :
    ¬ReachC (2,0) (fatal n,0) := by
  intro hh
  exact safePrefix_excludes hr hlarge n hn ht hc
    ((root_reset_chain_iff (fatal n)).mp hh)

#print axioms parent_unique
#print axioms Link.valid_sound
#print axioms checkSeq_sound
#print axioms SafeTail.cover
#print axioms safePrefix_excludes_root
end CascadeResetInverse
