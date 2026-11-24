import BB429AffinePump

namespace BB429AffinePump

/-- Untrusted branch selection; endpoint guards still independently checked. -/
def guess (u w : Int) : Tag :=
  let g := w-2*u
  if 3≤g then .F
  else if g=2 then .R2
  else if g=1 then .R1
  else if g=0 then .R0
  else if g= -2 then .E1
  else if g= -3 then .O2
  else if g%4=0 then .Eeven
  else if g%4=2 then .Eodd
  else if g%4=1 then if w=1 then .Oeven1 else .Oeven
  else .Oodd

def autoCheck (len : Nat) (l : Line) (N : Nat) : Option Line :=
  match len with
  | 0 => some l
  | k+1 =>
    let t := guess l.u l.w
    if guard t l.u l.w ∧ guard t (eu l N) (ew l N) then
      autoCheck k (move t l) N else none

theorem autoCheck_word (len : Nat) (l l' : Line) (N : Nat)
    (h : autoCheck len l N=some l') :
    ∃ word : List Tag, word.length=len ∧ checkWord word l N=some l' := by
  induction len generalizing l with
  | zero => exact ⟨[],rfl,h⟩
  | succ len ih =>
    simp only [autoCheck] at h
    split at h
    next hg =>
      obtain ⟨word,hlen,hword⟩ := ih _ h
      exact ⟨guess l.u l.w::word,by simp [hlen],by simp [checkWord,hg,hword]⟩
    next hg => simp at h

structure Block where
  len : Nat
  count : Nat
  quarter : Nat
  deriving Repr

def blockTime (b : Block) : Nat := b.count*b.len
def blockNext (b : Block) (s : BB429.State) : Option BB429.State :=
  if b.count=1 then BB429.run b.len s
  else if b.count=0 then none
  else
    let (u,w) := s
    let q := b.quarter
    if autoCheck b.len (sectionLine u w q) (b.count-1)=some (sectionLine u (w+4*q) q)
    then some (u,w+4*q*b.count) else none

theorem blockNext_sound (b : Block) (s t : BB429.State)
    (h : blockNext b s=some t) : BB429.run (blockTime b) s=some t := by
  rcases s with ⟨u,w⟩
  simp only [blockNext] at h
  split at h
  next he => simpa [blockTime,he] using h
  next hne =>
    split at h
    next hz => simp at h
    next hnz =>
      split at h
      next hc =>
        obtain ⟨word,hlen,hw⟩ := autoCheck_word _ _ _ _ hc
        have hr := repeated_pump word u w b.quarter (b.count-1) hw b.count (by omega)
        rw [hlen] at hr
        simpa [blockTime,← Option.some.inj h] using hr
      next hc => simp at h

def replay (bs : List Block) (s : BB429.State) : Option BB429.State :=
  match bs with
  | [] => some s
  | b::rest => (blockNext b s).bind (replay rest)

def total : List Block → Nat
  | [] => 0
  | b::rest => blockTime b+total rest

theorem replay_sound (bs : List Block) (s t : BB429.State)
    (h : replay bs s=some t) : BB429.run (total bs) s=some t := by
  induction bs generalizing s with
  | nil => exact h
  | cons b rest ih =>
    simp only [replay] at h
    cases hs : blockNext b s with
    | none => simp [hs] at h
    | some mid =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [total, BB429.run_add, blockNext_sound b s mid hs]
      exact ih mid h

#print axioms autoCheck_word
#print axioms blockNext_sound
#print axioms replay_sound
end BB429AffinePump
