import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8Scan
open BB6.Agent8Section
variable {α β : Type}

def finish (decode : α → Option β) : Option α → Option (Option β)
 | none => some none
 | some a => (decode a).map some

/-- Executable first section-or-halt scanner. On success returns both the
    elapsed calls and the section result; none means exhausted fuel. -/
def scan (f : α → Option α) (decode : α → Option β) :
    Nat → Option α → Option (Nat × Option β)
 | 0, s => (finish decode s).map (fun y => (0,y))
 | n+1, s =>
     match finish decode s with
     | some y => some (0,y)
     | none => (scan f decode n (s.bind f)).map (fun p => (p.1+1,p.2))

theorem finish_sound (decode : α → Option β) (embed : β → α)
    (hd : ∀ a y, decode a = some y → a = embed y)
    (s : Option α) (y : Option β) (h : finish decode s = some y) :
    s = y.map embed := by
  cases s with
  | none =>
      simp [finish] at h
      subst y
      rfl
  | some a =>
      cases hh : decode a with
      | none => simp [finish,hh] at h
      | some b =>
          simp only [finish,hh,Option.map_some,Option.some.injEq] at h
          subst y
          rw [hd a b hh]
          rfl

theorem scan_sound (f : α → Option α) (decode : α → Option β)
    (embed : β → α) (hd : ∀ a y, decode a = some y → a = embed y)
    (fuel : Nat) (s : Option α) (m : Nat) (y : Option β)
    (h : scan f decode fuel s = some (m,y)) :
    m ≤ fuel ∧ run f m s = y.map embed := by
  induction fuel generalizing s m y with
  | zero =>
      simp only [scan] at h
      cases hf : finish decode s with
      | none => simp [hf] at h
      | some z =>
          simp only [hf,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨hm,hy⟩
          subst m
          subst y
          exact ⟨by omega, finish_sound decode embed hd s z hf⟩
  | succ fuel ih =>
      change (match finish decode s with
        | some z => some (0,z)
        | none => (scan f decode fuel (s.bind f)).map
            (fun p => (p.1+1,p.2))) = some (m,y) at h
      cases hf : finish decode s with
      | some z =>
          simp only [hf,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨hm,hy⟩
          subst m
          subst y
          exact ⟨by omega, finish_sound decode embed hd s z hf⟩
      | none =>
          simp only [hf] at h
          cases hn : scan f decode fuel (s.bind f) with
          | none => simp [hn] at h
          | some p =>
              rcases p with ⟨q,z⟩
              simp only [hn,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨hm,hy⟩
              subst m
              subst y
              obtain ⟨hq,heq⟩ := ih (s.bind f) q z hn
              constructor
              · omega
              · simpa only [run_succ_head] using heq

/-- A terminal observation at any moment before the fuel limit guarantees
    that the scanner returns a properly witnessed section exit. -/
theorem scan_complete (f : α → Option α) (decode : α → Option β)
    (m fuel : Nat) (s : Option α) (hm : m ≤ fuel)
    (ht : ∃ y : Option β, finish decode (run f m s) = some y) :
    ∃ n y, scan f decode fuel s = some (n,y) := by
  induction m generalizing fuel s with
  | zero =>
      obtain ⟨y,hy⟩ := ht
      have hh : finish decode s = some y := by simpa only [run] using hy
      cases fuel with
      | zero => exact ⟨0,y, by simp [scan,hh]⟩
      | succ fuel => exact ⟨0,y, by simp [scan,hh]⟩
  | succ m ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases hf : finish decode s with
          | some y => exact ⟨0,y,by simp [scan,hf]⟩
          | none =>
              have he : ∃ y : Option β,
                  finish decode (run f m (s.bind f)) = some y := by
                simpa only [run_succ_head] using ht
              obtain ⟨n,y,hn⟩ := ih fuel (s.bind f) (by omega) he
              exact ⟨n+1,y,by simp [scan,hf,hn]⟩

/-- The scanner returns the first terminal section-or-halt event, not a later
    hit: every smaller elapsed time has no recognized return or stop. -/
theorem scan_first (f : α → Option α) (decode : α → Option β)
    (fuel : Nat) (s : Option α) (m : Nat) (y : Option β)
    (h : scan f decode fuel s = some (m,y)) :
    ∀ j : Nat, j < m → finish decode (run f j s) = none := by
  induction fuel generalizing s m y with
  | zero =>
      simp only [scan] at h
      cases hf : finish decode s with
      | none => simp [hf] at h
      | some z =>
          simp only [hf,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨hm,hy⟩
          subst m
          intro j hj
          omega
  | succ fuel ih =>
      change (match finish decode s with
        | some z => some (0,z)
        | none => (scan f decode fuel (s.bind f)).map
            (fun p => (p.1+1,p.2))) = some (m,y) at h
      cases hf : finish decode s with
      | some z =>
          simp only [hf,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨hm,hy⟩
          subst m
          intro j hj
          omega
      | none =>
          simp only [hf] at h
          cases hn : scan f decode fuel (s.bind f) with
          | none => simp [hn] at h
          | some p =>
              rcases p with ⟨q,z⟩
              simp only [hn,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨hm,hy⟩
              subst m
              subst y
              intro j hj
              cases j with
              | zero => simpa [run] using hf
              | succ j =>
                  have hlt : j < q := by omega
                  have hi := ih (s.bind f) q z hn j hlt
                  simpa only [run_succ_head] using hi

#print axioms scan_first

#print axioms scan_sound
#print axioms scan_complete
end BB6.Agent8Scan
