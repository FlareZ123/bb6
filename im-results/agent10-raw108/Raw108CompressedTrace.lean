import Raw108CompressedTape
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108Long
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent10CompressedTape

def table (a1 : Option (Option Move)) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => a1
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,true,5⟩)
  | (4,true) => some (some ⟨true,false,1⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | (5,true) => some (some ⟨false,false,1⟩)
  | _ => none


abbrev P : Pat := ⟨false,true,true⟩
abbrev Q : Pat := ⟨true,false,true⟩
abbrev R : Pat := ⟨true,true,false⟩
abbrev Z : Pat := ⟨false,false,false⟩

theorem left1 (a1 : Option (Option Move)) (L S : List Bool) :
    run0 (table a1) 9 ⟨1,P.word++L,Z.word++S⟩ = some ⟨1,L,Z.word++R.word++S⟩ := by rfl
theorem right1 (a1 : Option (Option Move)) (L S : List Bool) :
    run0 (table a1) 5 ⟨2,false::L,Q.word++S⟩ = some ⟨2,false::(R.word++L),S⟩ := by rfl

def fallback (a1 : Option (Option Move)) (z : Cfg) : Option (Nat × Cfg) :=
  (BB6.Agent10CompressedTape.step (table a1) z).map fun x => (1,x)

def macroStep (a1 : Option (Option Move)) (z : Cfg) : Option (Nat × Cfg) :=
  if z.q = 1 then
    match pop3 z.r with
    | some (p,rs) =>
      if p=Z then
        let (n,l) := strip P 1024 z.l
        if n > 0 then some (9*n,⟨1,l,.run Z 3 (.run R (3*n) rs)⟩)
        else fallback a1 z
      else fallback a1 z
    | none => fallback a1 z
  else if z.q = 2 then
    match pop z.l with
    | some (false,ls) =>
      let (n,r) := strip Q 1024 z.r
      if n > 0 then some (5*n,⟨2,push false (.run R (3*n) ls),r⟩)
      else fallback a1 z
    | _ => fallback a1 z
  else fallback a1 z

abbrev pr := BB6.Agent10CompressedTape.project

theorem fallback_sound {a1 : Option (Option Move)} {z : Cfg} {k : Nat} {c : Cfg}
    (h : fallback a1 z = some (k,c)) : run0 (table a1) k (pr z) = some (pr c) := by
  unfold fallback at h
  cases hs : BB6.Agent10CompressedTape.step (table a1) z with
  | none => simp [hs] at h
  | some t =>
    simp [hs] at h
    obtain ⟨rfl,rfl⟩ := h
    have H := step_sound (table a1) z
    simp [hs] at H
    simp [run0,← H]

theorem macroStep_sound (a1 : Option (Option Move)) (z : Cfg) (k : Nat) (c : Cfg)
    (h : macroStep a1 z = some (k,c)) : run0 (table a1) k (pr z) = some (pr c) := by
  rcases z with ⟨q,l,r⟩
  unfold macroStep at h
  simp only at h
  split at h
  · rename_i hq
    subst q
    split at h
    · rename_i p rs hp
      split at h
      · rename_i hZ; subst p
        split at h
        · rename_i hn
          have H := sweepL (table a1) 1 [] Z.word P.word R.word 9 (left1 a1) (strip P 1024 l).1 (expand (strip P 1024 l).2) (expand rs)
          simp only [List.nil_append,strip_sound] at H
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          change run0 (table a1) (9*(strip P 1024 l).1) ⟨1,expand l,expand r⟩ = _
          rw [pop3_sound r Z rs hp]
          simpa only [pr,BB6.Agent10CompressedTape.project,expand,word_3,show word Z 3 = Z.word by rfl,List.append_assoc] using H
        · exact fallback_sound h
      · exact fallback_sound h
    · exact fallback_sound h
  · split at h
    · rename_i hq
      subst q
      split at h
      · rename_i ls hp
        split at h
        · rename_i hn
          have H := sweepR (table a1) 2 [false] [] Q.word R.word 5 (right1 a1) (strip Q 1024 r).1 (expand ls) (expand (strip Q 1024 r).2)
          simp only [List.nil_append,strip_sound] at H
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          change run0 (table a1) (5*(strip Q 1024 r).1) ⟨2,expand l,expand r⟩ = _
          rw [pop_some l false ls hp]
          simpa only [pr,BB6.Agent10CompressedTape.project,expand,push_sound,word_3,List.cons_append,List.nil_append] using H
        · exact fallback_sound h
      · exact fallback_sound h
    · exact fallback_sound h

def fastRun (a1 : Option (Option Move)) : Nat → Nat → Cfg → Option Cfg
  | _,0,z => some z
  | 0,_+1,_ => none
  | fuel+1,n+1,z =>
    match macroStep a1 z with
    | none => none
    | some (k,c) =>
      if k ≤ n+1 then fastRun a1 fuel (n+1-k) c
      else (BB6.Agent10CompressedTape.step (table a1) z).bind (fastRun a1 fuel n)

theorem fastRun_sound (a1 : Option (Option Move)) (fuel n : Nat) (z c : Cfg)
    (h : fastRun a1 fuel n z = some c) : run0 (table a1) n (pr z) = some (pr c) := by
  induction fuel generalizing n z with
  | zero => cases n <;> simp_all [fastRun,run0]
  | succ f ih =>
    cases n with
    | zero => simpa [fastRun,run0] using congrArg (Option.map pr) h
    | succ n =>
      simp only [fastRun] at h
      split at h
      · contradiction
      · rename_i k d hm
        split at h
        · rename_i hk
          have H := join0 (macroStep_sound a1 z k d hm) (ih _ _ h)
          rw [show k+(n+1-k)=n+1 by omega] at H
          exact H
        · cases hs : BB6.Agent10CompressedTape.step (table a1) z with
          | none => simp [hs] at h
          | some d =>
            simp [hs] at h
            have H := step_sound (table a1) z
            simp [hs] at H
            simpa [run0,← H] using ih n d h

theorem step_refine (a1 : Option (Option Move)) (z c : Z0)
    (h : step0 (table none) z = some c) : step0 (table a1) z = some c := by
  have htable : ∀ s mv, table none s = some (some mv) → table a1 s = some (some mv) := by
    intro s mv h
    rcases s with ⟨q,b⟩
    have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> simp_all [table]
  unfold step0 at h ⊢
  cases hval : table none (z.q,z.l.headD false) with
  | none => rw [hval] at h; contradiction
  | some v =>
    cases v with
    | none => rw [hval] at h; contradiction
    | some mv => rw [htable _ _ hval]; rw [hval] at h; exact h

theorem run_refine (a1 : Option (Option Move)) (n : Nat) (z c : Z0)
    (h : run0 (table none) n z = some c) : run0 (table a1) n z = some c := by
  induction n generalizing z with
  | zero => exact h
  | succ n ih =>
    simp only [run0] at h ⊢
    cases hs : step0 (table none) z with
    | none => simp [hs] at h
    | some d =>
      simp [hs] at h
      simpa [step_refine a1 z d hs] using ih d h

#print axioms fastRun_sound
#print axioms run_refine
end BB6.Agent10Raw108Long
