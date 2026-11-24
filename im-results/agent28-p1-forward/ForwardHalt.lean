import ForwardReset
namespace BB6.Agent28Forward
open BB6.Agent1 BB6P1Unit

theorem Wrap.clock {q v r w : Nat} (h : Wrap q v r w) : q<r := by
  obtain ⟨t,ht,he,_⟩ := h
  have := ht.1
  omega

theorem reset_clock {q r w : Nat} (hq : 5≤q) (h : resetRule (q-2) (some (r,w))) : q<r := by
  obtain ⟨j,hlo,hhi,hb⟩ := h
  let x:=q-2-drop j
  have hd := drop_identity j
  change (x=0 ∧ some (r,w)=some (A j-1,A j-6)) ∨
    (x=1 ∧ ∃ a b, Wrap (A j+j+1) (2*j+5) a b ∧ some (r,w)=some (a,b)) ∨
    (x=2 ∧ some (r,w)=none) ∨
    (3≤x ∧ ∃ a b, Wrap (A j+x-2) (2*x-1) a b ∧ some (r,w)=some (a,b)) at hb
  have hx : x+drop j=q-2 := by dsimp [x]; omega
  rcases hb with h0 | h1 | h2 | h3
  · have he : r=A j-1 := congrArg Prod.fst (Option.some.inj h0.2)
    omega
  · obtain ⟨he,a,b,hw,hab⟩ := h1
    have hq' : r=a := congrArg Prod.fst (Option.some.inj hab)
    have := hw.clock
    omega
  · cases h2.2
  · obtain ⟨he,a,b,hw,hab⟩ := h3
    have hq' : r=a := congrArg Prod.fst (Option.some.inj hab)
    have := hw.clock
    omega

theorem next_clock {q v r w : Nat} (hq : valid q v) (h : Next q v (some (r,w))) : q<r := by
  unfold valid at hq
  unfold Next at h
  split at h <;> rename_i hv0
  · have he : r=q+2 := congrArg Prod.fst (Option.some.inj h)
    omega
  · split at h <;> rename_i hv1
    · exact reset_clock (by omega) h
    · split at h <;> obtain ⟨a,b,hw,he⟩ := h <;>
        have hr : r=a := congrArg Prod.fst (Option.some.inj he) <;> rw [hr] <;> exact hw.clock

/-- Determinism forces any genuine halting path to extend every successful prefix. -/
theorem Walk.halt_suffix {p r : Nat × Nat} {n : Nat} (h : Walk p n r) {m : Nat} {s : Nat × Nat}
    (hh : Walk p m s) (hhalt : trans s=none) : n≤m ∧ Walk r (m-n) s := by
  induction h generalizing m s with
  | nil => exact ⟨by omega,by simpa using hh⟩
  | cons p t r n hp hw ih =>
    cases hh with
    | nil => rw [hp] at hhalt; cases hhalt
    | cons p u s m hu hw' =>
      have he : t=u := Option.some.inj (hp.symm.trans hu)
      subst u
      obtain ⟨hle,hs⟩ := ih hw' hhalt
      exact ⟨by omega,by simpa only [show m+1-(n+1)=m-n by omega] using hs⟩

def SourceHalt (p : Nat × Nat) : Prop := ∃ n s, Walk p n s ∧ trans s=none

inductive MacroHalt : Nat → Nat → Prop where
  | now (q v : Nat) : Next q v none → MacroHalt q v
  | later (q v r w : Nat) : Next q v (some (r,w)) → MacroHalt r w → MacroHalt q v

theorem macro_to_source {q v : Nat} (hv : valid q v) (h : MacroHalt q v) : SourceHalt (decode q v) := by
  induction h with
  | now q v hn => exact next_sound hv hn
  | later q v r w hn hm ih =>
    obtain ⟨hvalid,n,hnpos,hw⟩ := next_sound hv hn
    obtain ⟨m,s,hs,hh⟩ := ih hvalid
    exact ⟨n+m,s,hw.append hs,hh⟩

theorem source_to_macro (m : Nat) (q v : Nat) (hv : valid q v) (s : Nat × Nat)
    (hw : Walk (decode q v) m s) (hh : trans s=none) : MacroHalt q v := by
  induction m using Nat.strongRecOn generalizing q v s with
  | ind m ih =>
    obtain ⟨o,hn,hs⟩ := next_total q v hv
    cases o with
    | none => exact MacroHalt.now q v hn
    | some p =>
      obtain ⟨r,w⟩ := p
      obtain ⟨hvalid,n,hnpos,hwalk⟩ := hs
      obtain ⟨hle,hsuffix⟩ := hwalk.halt_suffix hw hh
      exact MacroHalt.later q v r w hn (ih (m-n) (by omega) r w hvalid s hsuffix hh)

theorem source_halt_iff (q v : Nat) (hv : valid q v) :
    SourceHalt (decode q v) ↔ MacroHalt q v := by
  constructor
  · rintro ⟨m,s,hw,hh⟩
    exact source_to_macro m q v hv s hw hh
  · exact macro_to_source hv

theorem blank_halt_iff : SourceHalt (2,1) ↔ MacroHalt 5 0 := by
  exact source_halt_iff 5 0 (by unfold valid; decide)

inductive MacroReach : Nat → Nat → Prop where
  | init : MacroReach 5 0
  | next (q v r w : Nat) : MacroReach q v → Next q v (some (r,w)) → MacroReach r w

theorem macro_reach_valid {q v : Nat} (h : MacroReach q v) : valid q v := by
  induction h with
  | init => unfold valid; decide
  | next q v r w hr hn ih => exact (next_sound ih hn).1

theorem macro_reach_source {q v : Nat} (h : MacroReach q v) :
    Reach (decode q v).1 (decode q v).2 := by
  induction h with
  | init => exact Reach.init
  | next q v r w hr hn ih =>
    obtain ⟨_,n,_,hw⟩ := next_sound (macro_reach_valid hr) hn
    exact hw.reach ih

theorem macro_halt_reaches {q v : Nat} (h : MacroHalt q v) (hr : MacroReach q v) :
    ∃ a b, MacroReach a b ∧ Next a b none := by
  induction h with
  | now q v hn => exact ⟨q,v,hr,hn⟩
  | later q v r w hn hm ih => exact ih (MacroReach.next q v r w hr hn)

theorem walk_of_reach {a c : Nat} (h : Reach a c) : ∃ n, Walk (2,1) n (a,c) := by
  induction h with
  | init => exact ⟨0,Walk.nil _⟩
  | next a c b d hr ht ih =>
    obtain ⟨n,hw⟩ := ih
    exact ⟨n+1,hw.append (Walk.single (a,c) (b,d) ht)⟩

/-- Exact blank halting criterion solely in the arithmetic forward orbit.
    This theorem does not assert that any critical clock is reached. -/
theorem blank_critical_clock_iff : SourceHalt (2,1) ↔ ∃ j, MacroReach (7*2^j-j-3) 1 := by
  constructor
  · intro h
    obtain ⟨q,v,hr,hn⟩ := macro_halt_reaches (blank_halt_iff.mp h) MacroReach.init
    obtain ⟨he,j,hq⟩ := (next_none_iff q v (macro_reach_valid hr)).mp hn
    subst q
    subst v
    exact ⟨j,hr⟩
  · rintro ⟨j,hr⟩
    let q:=7*2^j-j-3
    have hv : valid q 1 := macro_reach_valid hr
    have hn : Next q 1 none := (next_none_iff q 1 hv).mpr ⟨rfl,j,rfl⟩
    obtain ⟨n,s,hw,hh⟩ := next_sound hv hn
    obtain ⟨m,hrw⟩ := walk_of_reach (macro_reach_source hr)
    exact ⟨m+n,s,hrw.append hw,hh⟩

#print axioms next_clock
#print axioms blank_halt_iff
#print axioms blank_critical_clock_iff
end BB6.Agent28Forward
