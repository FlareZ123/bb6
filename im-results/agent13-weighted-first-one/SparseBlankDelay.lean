import BlankDelaySource

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Unknown zero rows can take any successor. Known halt and write-one
    rows have no zero-preserving outgoing edge. -/
def mayZero (p : PartialMachine) (s t : Fin 6) : Bool :=
  match p (s,false) with
  | none => true
  | some none => false
  | some (some mv) => !mv.write && mv.next == t

theorem actual_mayZero (p : PartialMachine) (m : Machine) (hc : compatible p m)
    (s t : Fin 6) (h : zeroNext m s=some t) : mayZero p s t=true := by
  obtain ⟨r,hr⟩ := zeroNext_some m s t h
  unfold mayZero
  cases hp : p (s,false) with
  | none => rfl
  | some v =>
    have he:=hc (s,false) v hp
    rw [hr] at he
    subst v
    simp

inductive SimplePath (p : PartialMachine) (t : Fin 6) : List (Fin 6) → Prop where
  | stop : SimplePath p t [t]
  | step {s u : Fin 6} {l : List (Fin 6)}
      (h : mayZero p s u=true) (hn : s∉u::l)
      (hp : SimplePath p t (u::l)) : SimplePath p t (s::u::l)

def prependPaths (p : PartialMachine) (l : List (Fin 6)) : List (List (Fin 6)) :=
  match l with
  | [] => []
  | u::_rest => ((List.finRange 6).filter fun s => !l.contains s && mayZero p s u).map (fun s => s::l)

def pathsTo (p : PartialMachine) (t : Fin 6) : Nat → List (List (Fin 6))
  | 0 => [[t]]
  | d+1 => (pathsTo p t d).flatMap (prependPaths p)

theorem mem_pathsTo (p : PartialMachine) (t : Fin 6) (d : Nat) (l : List (Fin 6))
    (h : l∈pathsTo p t d) : SimplePath p t l ∧ l.length=d+1 := by
  induction d generalizing l with
  | zero =>
    simp [pathsTo] at h
    subst l
    exact ⟨.stop,rfl⟩
  | succ d ih =>
    obtain ⟨ls,hm,hl⟩ := List.mem_flatMap.mp h
    obtain ⟨hp,hlen⟩ := ih ls hm
    cases ls with
    | nil => simp [prependPaths] at hl
    | cons u rest =>
      obtain ⟨s,hs,he⟩ := List.mem_map.mp hl
      subst l
      obtain ⟨_,hs⟩ := List.mem_filter.mp hs
      simp at hs
      exact ⟨.step hs.2 (by simpa using hs.1) hp,by simp [List.length_cons] at hlen ⊢; omega⟩

theorem path_mem_pathsTo {p : PartialMachine} {t : Fin 6} {l : List (Fin 6)}
    (h : SimplePath p t l) : l∈pathsTo p t (l.length-1) := by
  induction h with
  | stop => simp [pathsTo]
  | @step s u l h hn hp ih =>
    have he : (s::u::l : List (Fin 6)).length-1=((u::l : List (Fin 6)).length-1)+1 := by simp
    rw [he]
    apply List.mem_flatMap.mpr
    refine ⟨u::l,ih,?_⟩
    apply List.mem_map.mpr
    refine ⟨s,?_,rfl⟩
    apply List.mem_filter.mpr
    exact ⟨by simp,by simp [hn,h]⟩

/-- At most 326 distinct simple incoming paths are enumerated over all
    six possible delays when the target state is fixed. -/
def possibleDelays (p : PartialMachine) (t : Fin 6) : List Nat :=
  (List.range 6).filter fun d => !(pathsTo p t d).isEmpty

theorem terminal_has_simple_path (p : PartialMachine) (m : Machine) (hc : compatible p m)
    {s t : Fin 6} {d : Nat} (h : TerminalPath (zeroNext m) s d t) :
    ∃ l : List (Fin 6), l.head?=some s ∧ l.length=d+1 ∧ SimplePath p t l ∧
      ∀ q∈l, ∃ e≤d, TerminalPath (zeroNext m) q e t := by
  induction h with
  | stop s hs =>
    refine ⟨[s],rfl,rfl,.stop,?_⟩
    intro q hq
    have he : q=s := by simpa using hq
    subst q
    exact ⟨0,Nat.le_refl _,.stop _ hs⟩
  | @step s u t d hs ht ih =>
    obtain ⟨l,hhead,hlen,hpath,hmem⟩ := ih
    cases l with
    | nil => simp at hhead
    | cons v l =>
      simp at hhead
      subst v
      have hn : s∉u::l := by
        intro hm
        obtain ⟨e,he,ht'⟩ := hmem s hm
        have hh := (TerminalPath.step hs ht).unique ht'
        omega
      refine ⟨s::u::l,rfl,by simp [List.length_cons] at hlen ⊢; omega,
        .step (actual_mayZero p m hc s u hs) hn hpath,?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact ⟨d+1,Nat.le_refl _,.step hs ht⟩
      · obtain ⟨e,he,ht'⟩ := hmem q hq
        exact ⟨e,by omega,ht'⟩

/-- Every concrete total completion's possible delay is in the sparse list. -/
theorem delays_subset_possible (p : PartialMachine) (m : Machine) (hc : compatible p m)
    (t : Fin 6) (ht : zeroNext m t=none) (d : Nat) (hd : d∈delays (zeroNext m) t) :
    d∈possibleDelays p t := by
  obtain ⟨s,hp⟩ := (mem_delays_iff ht).mp hd
  obtain ⟨l,_,hlen,hpath,_⟩ := terminal_has_simple_path p m hc hp
  have hm := path_mem_pathsTo hpath
  rw [show l.length-1=d by omega] at hm
  simp [possibleDelays]
  exact ⟨by have := terminal_delay_le_five hp; omega, List.ne_nil_of_mem hm⟩

/-- Realize the chosen incoming path by assigning its unknown zero rows.
    The remaining unknown rows can all be halt. This changes no assigned row. -/
def fillPath (p : PartialMachine) : List (Fin 6) → Machine
  | [] => fun slot => (p slot).getD none
  | [_] => fun slot => (p slot).getD none
  | s::u::l => fun slot =>
      if slot=(s,false) ∧ p slot=none then some ⟨false,true,u⟩
      else fillPath p (u::l) slot

theorem fillPath_compatible (p : PartialMachine) (l : List (Fin 6)) : compatible p (fillPath p l) := by
  induction l with
  | nil => intro slot v hv; simp [fillPath,hv]
  | cons s l ih =>
    cases l with
    | nil => intro slot v hv; simp [fillPath,hv]
    | cons u l =>
      intro slot v hv
      have hn : p slot≠none := by rw [hv]; simp
      simp [fillPath,hn,ih slot v hv]

def realizes (next : Fin 6 → Option (Fin 6)) : List (Fin 6) → Prop
  | [] => True
  | [_] => True
  | s::u::l => next s=some u ∧ realizes next (u::l)

theorem realizes_congr (next next' : Fin 6 → Option (Fin 6)) (l : List (Fin 6))
    (h : realizes next l) (he : ∀ q∈l, next' q=next q) : realizes next' l := by
  induction l with
  | nil => trivial
  | cons s l ih =>
    cases l with
    | nil => trivial
    | cons u l =>
      refine ⟨?_,ih h.2 (fun q hq => he q (List.mem_cons_of_mem _ hq))⟩
      rw [he s (by simp)]
      exact h.1

theorem fillPath_realizes {p : PartialMachine} {t : Fin 6} {l : List (Fin 6)}
    (h : SimplePath p t l) : realizes (zeroNext (fillPath p l)) l := by
  induction h with
  | stop => trivial
  | @step s u l hmay hn hp ih =>
    constructor
    · cases he : p (s,false) with
      | none => simp [zeroNext,fillPath,he]
      | some v =>
        have hf := fillPath_compatible p (s::u::l) (s,false) v he
        unfold mayZero at hmay
        rw [he] at hmay
        cases v with
        | none => simp at hmay
        | some mv =>
          rcases mv with ⟨w,r,q⟩
          cases w <;> simp at hmay
          subst q
          simp [zeroNext,hf]
    · apply realizes_congr _ _ _ ih
      intro q hq
      have hneq : q≠s := by intro he; subst q; exact hn hq
      have he : (q,false)≠(s,false) := by simp [hneq]
      unfold zeroNext
      simp [fillPath,he]

theorem path_terminal_of_realizes {p : PartialMachine} {t : Fin 6} {l : List (Fin 6)}
    (h : SimplePath p t l) (next : Fin 6 → Option (Fin 6)) (ht : next t=none)
    (hr : realizes next l) (s : Fin 6) (hs : l.head?=some s) :
    TerminalPath next s (l.length-1) t := by
  induction h generalizing s with
  | stop =>
    simp at hs
    subst s
    exact .stop _ ht
  | @step v u l hmay hn hp ih =>
    simp at hs
    subst s
    have hd : (v::u::l : List (Fin 6)).length-1=((u::l : List (Fin 6)).length-1)+1 := by simp
    rw [hd]
    exact .step hr.1 (ih hr.2 u rfl)

/-- Exact sparse lifting: every accepted delay is realized by a concrete
    compatible completion, provided the target row is fixed non-zero-writing. -/
theorem possible_delay_realized (p : PartialMachine) (t : Fin 6) (d : Nat)
    (hterm : ∀ m, compatible p m → zeroNext m t=none)
    (hd : d∈possibleDelays p t) :
    ∃ m, compatible p m ∧ d∈delays (zeroNext m) t := by
  have hmem : (pathsTo p t d)≠[] := by
    have h := (List.mem_filter.mp hd).2
    simpa using h
  cases he : pathsTo p t d with
  | nil => contradiction
  | cons l ls =>
    have hl : l∈pathsTo p t d := by rw [he]; simp
    obtain ⟨hp,hlen⟩:=mem_pathsTo p t d l hl
    let m := fillPath p l
    have hc : compatible p m := fillPath_compatible p l
    have ht := hterm m hc
    cases l with
    | nil => simp at hlen
    | cons s rest =>
      have h := path_terminal_of_realizes hp (zeroNext m) ht (fillPath_realizes hp) s rfl
      rw [show (s::rest : List (Fin 6)).length-1=d by omega] at h
      exact ⟨m,hc,(mem_delays_iff ht).mpr ⟨s,h⟩⟩

theorem possible_delay_iff (p : PartialMachine) (t : Fin 6) (d : Nat)
    (hterm : ∀ m, compatible p m → zeroNext m t=none) :
    d∈possibleDelays p t ↔ ∃ m, compatible p m ∧ d∈delays (zeroNext m) t := by
  constructor
  · exact possible_delay_realized p t d hterm
  · rintro ⟨m,hc,hd⟩
    exact delays_subset_possible p m hc t (hterm m hc) d hd

def WeightedBound (B : Nat) (m : Machine) : Prop :=
  ∀ k d, HaltsAfter m k → d∈delays (zeroNext m) 0 → d+k+1≤B

theorem firstOne_terminal (p : PartialMachine)
    (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (m : Machine) (hc : compatible p m) : zeroNext m 0=none := by
  have h := hc initialSlot _ hf
  change (match m initialSlot with | some t => if t.write then none else some t.next | none => none)=none
  rw [h]
  rfl

private theorem halt_unique (m : Machine) (k n : Nat) (hk : HaltsAfter m k) (hn : HaltsAfter m n) : k=n := by
  by_cases h : k=n
  · exact h
  rcases Nat.lt_or_gt_of_ne h with hlt|hgt
  · have he : n=(k+1)+(n-(k+1)) := by omega
    have hz : run m n blank=none := by
      rw [he,run_append,hk.2]
      rfl
    simp [HaltsAfter,hz] at hn
  · have he : k=(n+1)+(k-(n+1)) := by omega
    have hz : run m k blank=none := by
      rw [he,run_append,hn.2]
      rfl
    simp [HaltsAfter,hz] at hk

/-- Exact weight criterion for every completion of a uniform halting cylinder.
    In particular, unvisited zero-symbol rows cannot be arbitrarily filled
    before computing the maximum runtime. -/
theorem uniform_halter_weight_iff (p : PartialMachine) (B n : Nat)
    (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (hh : ∀ m, compatible p m → HaltsAfter m n) :
    (∀ m, compatible p m → WeightedBound B m) ↔
    ∀ d∈possibleDelays p 0, d+n+1≤B := by
  constructor
  · intro h d hd
    obtain ⟨m,hc,hm⟩ := possible_delay_realized p 0 d (firstOne_terminal p hf) hd
    exact h m hc n d (hh m hc) hm
  · intro h m hc k d hk hd
    have he := halt_unique m k n hk (hh m hc)
    subst k
    exact h d (delays_subset_possible p m hc 0 (firstOne_terminal p hf m hc) d hd)

def shortCylinder : PartialMachine := fun slot =>
  if slot=initialSlot then some (some ⟨true,true,1⟩)
  else if slot=(1,false) then some none else none

example : possibleDelays shortCylinder 0 = [0,1,2,3,4] := by decide

#print axioms possible_delay_iff
#print axioms uniform_halter_weight_iff
end BB6.Agent13BlankDelay
