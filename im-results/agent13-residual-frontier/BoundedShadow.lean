import NegativeShadow
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
namespace BB6.Agent13BoundedShadow
open BB6.Agent13AffineCone BB6.Agent13NegativeShadow BB6.Agent46

/-- Once depth fuel reaches precision, it cannot truncate a certificate. -/
theorem check_saturated (b : Nat) : ∀ f, b≤f → ∀ s, check f b s=check b b s := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro f hfb s
    cases b with
    | zero =>
      cases f <;> simp [check,small]
    | succ b =>
      cases f with
      | zero => omega
      | succ f =>
        simp only [check]
        have hD : check f (b+1-1) (dir s)=check b (b+1-1) (dir s) := by
          rw [ih _ (by omega) f (by omega),ih _ (by omega) b (by omega)]
        rw [hD]
        congr 3
        congr 1
        funext n
        rw [ih _ (by omega : b+1-(n+2)<b+1) f (by omega),
              ih _ (by omega : b+1-(n+2)<b+1) b (by omega)]

abbrev CacheKey := Nat × Nat × Nat × Nat
abbrev Cache := Std.HashMap CacheKey Bool

def cacheKey (f b : Nat) (s : Pair) : CacheKey := (min f b,b,s.x,s.y)
def cacheSound (c : Cache) : Prop := ∀ f b s v, c[cacheKey f b s]?=some v → v=check f b s

def allState (eval : α → Cache → Bool × Cache) : List α → Cache → Bool × Cache
  | [],c => (true,c)
  | a::as,c => let (v,c'):=eval a c; if v then allState eval as c' else (false,c')

theorem allState_correct (eval : α → Cache → Bool × Cache) (pred : α → Bool)
    (he : ∀ a c, cacheSound c → (eval a c).1=pred a ∧ cacheSound (eval a c).2)
    (xs : List α) (c : Cache) (hc : cacheSound c) :
    (allState eval xs c).1=xs.all pred ∧ cacheSound (allState eval xs c).2 := by
  induction xs generalizing c with
  | nil => exact ⟨rfl,hc⟩
  | cons a as ih =>
    obtain ⟨hv,hs⟩:=he a c hc
    cases hh : eval a c with
    | mk v c' =>
      rw [hh] at hv hs
      cases v <;> simp [allState,hh,←hv,hs,ih c' hs]

def memo : Nat → Nat → Pair → Cache → Bool × Cache
  | f,b,s,c =>
    match c[cacheKey f b s]? with
    | some v => (v,c)
    | none =>
      let result := match f with
        | 0 => (small b s && bad s,c)
        | f+1 =>
          if !small b s then (false,c)
          else if bad s then (true,c)
          else if !validVal b s then (false,c)
          else
            let (v,c') := if s.y%2=0 then memo f (b-1) (dir s) c else (true,c)
            if !v then (false,c')
            else allState (fun n d =>
              if depthOK s n then
                if validHi s (hi s n) n then memo f (b-(n+2)) (hi s n) d else (false,d)
              else (true,d)) (List.range (val s+1)) c'
      (result.1,result.2.insert (cacheKey f b s) result.1)

private theorem cache_insert (c : Cache) (f b : Nat) (s : Pair) (v : Bool)
    (hc : cacheSound c) (hv : v=check f b s) : cacheSound (c.insert (cacheKey f b s) v) := by
  intro f' b' s' v' hh
  rw [Std.HashMap.getElem?_insert] at hh
  by_cases he : cacheKey f b s = cacheKey f' b' s'
  · simp [he] at hh
    have he' : min f b=min f' b' ∧ b=b' ∧ s.x=s'.x ∧ s.y=s'.y := by simpa [cacheKey] using he
    rcases he' with ⟨hf,rfl,hx,hy⟩
    have hss : s=s' := by cases s; cases s'; simp_all
    subst s'
    subst v'
    rw [hv]
    by_cases h : b≤f
    · have h' : b≤f' := by omega
      rw [check_saturated b f h s,check_saturated b f' h' s]
    · have h' : f=f' := by omega
      subst f'
      rfl
  · simp [he] at hh
    exact hc _ _ _ _ hh

theorem memo_correct (f b : Nat) (s : Pair) (c : Cache) (hc : cacheSound c) :
    (memo f b s c).1=check f b s ∧ cacheSound (memo f b s c).2 := by
  induction f generalizing b s c with
  | zero =>
    unfold memo
    split
    next v h => exact ⟨hc _ _ _ _ h,hc⟩
    next h =>
      simp only [check]
      exact ⟨True.intro,cache_insert _ _ _ _ _ hc rfl⟩
  | succ f ih =>
    unfold memo
    split
    next v h => exact ⟨hc _ _ _ _ h,hc⟩
    next h =>
      simp only [check]
      by_cases hs : small b s=true
      · by_cases hb : bad s=true
        · simp [hs,hb]
          exact cache_insert _ _ _ _ _ hc (by simp [check,hs,hb])
        · have hb' : bad s=false := Bool.eq_false_iff.mpr hb
          by_cases hv : validVal b s=true
          · have hD : ∀ d, cacheSound d →
                (if s.y%2=0 then memo f (b-1) (dir s) d else (true,d)).1=
                  (if s.y%2=0 then check f (b-1) (dir s) else true) ∧
                cacheSound (if s.y%2=0 then memo f (b-1) (dir s) d else (true,d)).2 := by
              intro d hd
              split <;> rename_i he
              · exact ih _ _ _ hd
              · simp [he,hd]
            obtain ⟨hdv,hds⟩:=hD c hc
            cases hdir : (if s.y%2=0 then memo f (b-1) (dir s) c else (true,c)) with
            | mk v c' =>
              rw [hdir] at hdv hds
              cases v
              · simp only [hs,hb',hv,Bool.not_true,Bool.not_false,if_false,if_true,hdir,Prod.fst,Prod.snd]
                have hfalse : check (f+1) b s=false := by simp [check,hs,hb',hv,←hdv]
                simp [←hdv]
                exact cache_insert _ _ _ _ _ hds hfalse.symm
              · let ev := fun n d => if depthOK s n then
                      if validHi s (hi s n) n then memo f (b-(n+2)) (hi s n) d else (false,d)
                    else (true,d)
                let pred := fun n => if depthOK s n then validHi s (hi s n) n && check f (b-(n+2)) (hi s n) else true
                have he : ∀ n d, cacheSound d → (ev n d).1=pred n ∧ cacheSound (ev n d).2 := by
                  intro n d hd
                  dsimp [ev,pred]
                  by_cases hn : depthOK s n=true
                  · by_cases hh : validHi s (hi s n) n=true
                    · simpa [hn,hh] using ih (b-(n+2)) (hi s n) d hd
                    · simp [hn,Bool.eq_false_iff.mpr hh,hd]
                  · simp [Bool.eq_false_iff.mpr hn,hd]
                obtain ⟨hav,has⟩:=allState_correct ev pred he (List.range (val s+1)) c' hds
                simp only [hs,hb',hv,Bool.not_true,Bool.not_false,if_false,if_true,hdir,Prod.fst,Prod.snd]
                have htarget : check (f+1) b s=(List.range (val s+1)).all pred := by simp [check,hs,hb',hv,←hdv,pred]
                change (allState ev (List.range (val s+1)) c').1 = _ ∧ _
                constructor
                · simpa [pred,←hdv] using hav
                · exact cache_insert _ _ _ _ _ has (hav.trans htarget.symm)
          · have hv' : validVal b s=false := Bool.eq_false_iff.mpr hv
            simp [hs,hb',hv']
            exact cache_insert _ _ _ _ _ hc (by simp [check,hs,hb',hv'])
      · have hs' : small b s=false := Bool.eq_false_iff.mpr hs
        simp [hs']
        exact cache_insert _ _ _ _ _ hc (by simp [check,hs'])

def bounded (b : Nat) (s : Pair) : Bool := (memo b b s {}).1

theorem bounded_eq_check (b : Nat) (s : Pair) : bounded b s=check b b s := by
  unfold bounded
  apply (memo_correct b b s {} ?_).1
  intro f b s v h
  simp at h

theorem bounded_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (b x y : Nat) (s : Pair) (h : bounded b s=true) (hc : congruent b x y s) : ¬reach x y := by
  rw [bounded_eq_check] at h
  exact check_sound reach parent forbid b b x y s h hc

#print axioms check_saturated
#print axioms memo_correct
#print axioms bounded_eq_check
#print axioms bounded_sound
end BB6.Agent13BoundedShadow
