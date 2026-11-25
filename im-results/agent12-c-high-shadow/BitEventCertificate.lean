import BitEventSummary
namespace BB6.Agent12BitEventCertificate
open BB6.Agent12WordBlock BB6.Agent12StreakWord BB6.Agent12BitPlanes BB6.Agent12BitEventWord BB6.Agent12BitEventSummary

structure Witness where
  counts : List Nat
  indices : List Nat
  p : Nat
  deriving Repr

/-- A ripple-carry addition across value-bit planes. All position lanes are
    processed in parallel. Generation is untrusted; the check verifies the
    entire recurrence and does not depend on this implementation's correctness. -/
def addPairs : List (Nat×Nat) → Nat → List Nat
  | [],c => [c]
  | (x,y)::ps,c =>
    let v := x^^^y
    (v^^^c)::addPairs ps ((x&&&y)|||(v&&&c))

def prefixAux : Nat → Nat → List Nat → List Nat
  | 0,_,ps => ps
  | f+1,k,ps => prefixAux f (2*k) (addPairs (ps.zip (ps.map (fun v=>v/2^k))) 0)

def countPlanes (N q : Nat) : List Nat := prefixAux (N.log2+1) 1 [q]

/-- Alternating blocks of 2^i zero/one bits, clipped to the required width. -/
def indexPlane (N i : Nat) : Nat :=
  let h := 2^i
  let len := (N+2*h-1)/(2*h)*(2*h)
  (((2^len-1)/(2^h+1))*2^h)%2^N

def indexPlanes (N : Nat) : List Nat := (List.range (N.log2+1)).map (indexPlane N)

/-- Fill gaps below the most recent event. The sentinel at N carries the
    initial parity. Each doubling step extends the known prefix by k bits. -/
def fillKnown (full : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0,_,v,_ => v
  | f+1,k,v,known =>
    fillKnown full f (2*k) (v|||((v/2^k)&&&(full^^^known))) (known|||known/2^k)

def propose (s : State) (N q : Nat) : Witness :=
  let cs := countPlanes N q
  let is := indexPlanes N
  let mp := parityMask s.m N cs is
  let p := fillKnown (2^(N+1)-1) (N.log2+1) 1 ((mp&&&q)|||(if s.m%2=1 then 2^N else 0)) (q|||2^N)
  ⟨cs,is,p⟩

/-- Closed decision contains no evaluation of the expanded event word or
    intermediate machine states. The witness can be generated in any way. -/
def checked (s t : State) (N q R D E K : Nat) (v : Witness) : Prop :=
  0<N ∧ q<2^N ∧ q.testBit 0=true ∧ 1≤R ∧
  runMask ((2^N-1)^^^q) (R-1)=0 ∧ runMask q D=0 ∧ (runMask q E).testBit 0=false ∧
  countCheckB N q v.counts=true ∧ indexCheck N v.indices ∧ parityCheck s.m N q v.p v.counts v.indices ∧
  8*2^R≤s.m ∧ 40*2^D≤s.m ∧ consistent s ∧
  fastEndpoint s N q v.p v.counts v.indices=t ∧ 0≤t.a ∧ 20*(2:Int)^E≤gap t+4 ∧
  value v.counts 0=K

instance (s t : State) (N q R D E K : Nat) (v : Witness) : Decidable (checked s t N q R D E K v) := by
  unfold checked indexCheck parityCheck consistent
  infer_instance

theorem certificate (next : Nat × Nat → Option (Nat × Nat)) (law : EdgeLaw next)
    (s t : State) (N q R D E K : Nat) (v : Witness) (h : checked s t N q R D E K v) :
    runNext next K (some (decode s))=some (decode t) := by
  obtain ⟨hN,hq,hclose,hR,hz,ho,hE,hc,hi,hp,hm,hd,hcons,hend,hx,hgap,hcount⟩ := h
  have hcs:=countCheckB_sound N q v.counts hc
  have he:=fastEndpoint_sound s N q v.p v.counts v.indices hN hq hclose hcs hi hp
  rw [hend] at he
  have hword:=word_guard_top q N R D E hN hR hz ho hE hclose
  have hcnt:=word_count q N 0 v.counts N (by omega) hcs
  rw [count_top N q v.counts hcs,Nat.add_zero,hcount] at hcnt
  have hpow : (2:Int)^endStreak 0 (word q 0 N)≤(2:Int)^E := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) hword.2)
  have hmul:=Int.mul_le_mul_of_nonneg_left hpow (by decide : (0:Int)≤20)
  have hgap' : 20*(2:Int)^endStreak 0 (word q 0 N)≤gap (run (word q 0 N) s)+4 := by rw [he]; omega
  have hx' : 0≤(run (word q 0 N) s).a := by rwa [he]
  have hr:=(long_word_certificate next law R D 0 (word q 0 N) s hword.1 hm hd hcons hx' hgap').2.2
  rw [hcnt,he] at hr
  exact hr

#print axioms certificate
end BB6.Agent12BitEventCertificate
