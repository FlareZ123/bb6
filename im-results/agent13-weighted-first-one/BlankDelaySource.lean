import BlankDelayKernel
import RootShift
import FirstStep
import WriteOneDrift

namespace BB6.Agent13BlankDelay
open BB6Coverage

def zeroNext (m : Machine) (s : Fin 6) : Option (Fin 6) :=
  match m (s,false) with
  | some t => if t.write then none else some t.next
  | none => none

theorem zeroNext_some (m : Machine) (s u : Fin 6) (h : zeroNext m s=some u) :
    ∃ r : Bool, m (s,false)=some ⟨false,r,u⟩ := by
  unfold zeroNext at h
  cases he : m (s,false) with
  | none => simp [he] at h
  | some t =>
    rcases t with ⟨w,r,q⟩
    cases w <;> simp [he] at h
    subst q
    exact ⟨r,rfl⟩

theorem zero_step (m : Machine) (s u : Fin 6) (r : Bool)
    (h : m (s,false)=some ⟨false,r,u⟩) :
    run m 1 (blankAt s)=some (shiftConfig (if r then 1 else -1) (blankAt u)) := by
  simp only [run,Option.bind_some,rawStep,show readSlot (blankAt s)=(s,false) from rfl,h,Option.map_some]
  apply congrArg some
  simp [applyMove,shiftConfig,blankAt]
  funext x
  by_cases hx : x=0 <;> simp [hx]

theorem zero_suffix (m : Machine) (s u : Fin 6) (r : Bool)
    (h : m (s,false)=some ⟨false,r,u⟩) (k : Nat) :
    HaltsAfterAt m s (k+1) ↔ HaltsAfterAt m u k := by
  have hrun (j : Nat) : run m (j+1) (blankAt s) =
      (run m j (blankAt u)).map (shiftConfig (if r then 1 else -1)) := by
    rw [show j+1=1+j by omega,run_append,zero_step m s u r h]
    exact shift_run _ _ _ _
  unfold HaltsAfterAt
  rw [hrun k,hrun (k+1)]
  cases run m k (blankAt u) <;> cases run m (k+1) (blankAt u) <;> simp

theorem zero_path_halts_iff (m : Machine) (s t : Fin 6) (d k : Nat)
    (h : TerminalPath (zeroNext m) s d t) :
    HaltsAfterAt m s (d+k) ↔ HaltsAfterAt m t k := by
  induction h with
  | stop => simp
  | @step s u t d hs ht ih =>
    obtain ⟨r,hr⟩:=zeroNext_some m s u hs
    rw [show d+1+k=(d+k)+1 by omega,zero_suffix m s u r hr,ih]

/-- Every halting root decomposes into a terminal zero-prefix and its exact suffix. -/
theorem halting_decomposes (m : Machine) (s : Fin 6) (n : Nat)
    (h : HaltsAfterAt m s n) :
    ∃ d k t, n=d+k ∧ TerminalPath (zeroNext m) s d t ∧ HaltsAfterAt m t k := by
  induction n generalizing s with
  | zero =>
    cases hn : zeroNext m s with
    | none => exact ⟨0,0,s,rfl,.stop s hn,h⟩
    | some u =>
      obtain ⟨r,hr⟩:=zeroNext_some m s u hn
      have hh := h.2
      rw [zero_step m s u r hr] at hh
      contradiction
  | succ n ih =>
    cases hn : zeroNext m s with
    | none => exact ⟨0,n+1,s,by omega,.stop s hn,h⟩
    | some u =>
      obtain ⟨r,hr⟩:=zeroNext_some m s u hn
      obtain ⟨d,k,t,he,hp,hk⟩ := ih u ((zero_suffix m s u r hr n).mp h)
      exact ⟨d+1,k,t,by omega,.step hn hp,hk⟩

theorem terminal_zero_next {next : α → Option α} {s t : α} {d : Nat}
    (h : TerminalPath next s d t) : next t=none :=
  (terminalPath_iff_follow.mp h).2

theorem halt_blank_immediate (m : Machine) (s : Fin 6) (k : Nat)
    (h : m (s,false)=none) (hh : HaltsAfterAt m s k) : k=0 := by
  cases k with
  | zero => rfl
  | succ k =>
    have hr : run m 1 (blankAt s)=none := by simp [run,rawStep,show readSlot (blankAt s)=(s,false) from rfl,h]
    have hf : run m (k+1) (blankAt s)=none := by rw [show k+1=1+k by omega,run_append,hr]; rfl
    simp [HaltsAfterAt,hf] at hh

def swapToZero (s : Fin 6) : StatePerm where
  forward := fun q => if q=s then 0 else if q=0 then s else q
  backward := fun q => if q=s then 0 else if q=0 then s else q
  leftInverse := by intro q; revert q; revert s; decide
  rightInverse := by intro q; revert q; revert s; decide

@[simp] theorem swapToZero_maps (s : Fin 6) : (swapToZero s).forward s=0 := by simp [swapToZero]
@[simp] theorem swapToZero_back (s : Fin 6) : (swapToZero s).backward 0=s := by revert s; decide

theorem renamed_zeroNext (e : StatePerm) (m : Machine) (s : Fin 6) :
    zeroNext (renameTable e m) (e.forward s)=(zeroNext m s).map e.forward := by
  unfold zeroNext renameTable
  simp only [e.leftInverse]
  cases he : m (s,false) with
  | none => rfl
  | some t => rcases t with ⟨w,r,q⟩; cases w <;> rfl

theorem renamed_path (e : StatePerm) (m : Machine) {s t : Fin 6} {d : Nat}
    (h : TerminalPath (zeroNext m) s d t) :
    TerminalPath (zeroNext (renameTable e m)) (e.forward s) d (e.forward t) := by
  induction h with
  | stop s hs => exact .stop _ (by rw [renamed_zeroNext,hs]; rfl)
  | step hs _ ih => exact .step (by rw [renamed_zeroNext,hs]; rfl) ih

theorem reflected_zeroNext (m : Machine) (s : Fin 6) :
    zeroNext (reflectTable m) s=zeroNext m s := by
  unfold zeroNext reflectTable
  cases he : m (s,false) with
  | none => rfl
  | some t => rcases t with ⟨w,r,q⟩; cases w <;> rfl

theorem reflected_path (m : Machine) {s t : Fin 6} {d : Nat}
    (h : TerminalPath (zeroNext m) s d t) :
    TerminalPath (zeroNext (reflectTable m)) s d t := by
  have he : zeroNext (reflectTable m)=zeroNext m := funext (reflected_zeroNext m)
  rw [he]; exact h

theorem root_rename (m : Machine) (s : Fin 6) (k : Nat) :
    HaltsAfter (renameTable (swapToZero s) m) k ↔ HaltsAfterAt m s k := by
  have h:=rename_haltsAt_iff (swapToZero s) m s k
  rw [swapToZero_maps] at h
  exact h

/-- Starting in a write-one state, all exact halting times and all incoming
    blank delays survive the first-one canonicalization together. -/
theorem normalize_write_root (m : Machine) (s t : Fin 6) (d k : Nat)
    (p : TerminalPath (zeroNext m) s d t) (h : HaltsAfterAt m t k)
    (r : Bool) (q : Fin 6) (hw : m (t,false)=some ⟨true,r,q⟩) :
    ∃ m', m' initialSlot=some ⟨true,true,1⟩ ∧ HaltsAfter m' k ∧
      d∈delays (zeroNext m') 0 := by
  let e := swapToZero t
  let m0 := renameTable e m
  let q0 := e.forward q
  have hp : TerminalPath (zeroNext m0) (e.forward s) d 0 := by
    have H:=renamed_path e m p
    simpa [e,m0] using H
  have hh : HaltsAfter m0 k := (root_rename m t k).mpr h
  have h0 : m0 initialSlot=some ⟨true,r,q0⟩ := by
    change (m (e.backward 0,false)).map (renameMove e)=_
    rw [show e.backward 0=t from swapToZero_back t,hw]
    rfl
  let m1 := if r then m0 else reflectTable m0
  have h1 : m1 initialSlot=some ⟨true,true,q0⟩ := by
    cases r <;> simp [m1,reflectTable,reflectMove,h0]
  have hp1 : TerminalPath (zeroNext m1) (e.forward s) d 0 := by
    cases r with
    | false => exact reflected_path m0 hp
    | true => exact hp
  have hh1 : HaltsAfter m1 k := by
    cases r with
    | false => exact (reflect_halts_iff m0 k).mpr hh
    | true => exact hh
  have hq : q0≠0 := by
    intro hq
    rw [hq] at h1
    have hn:=writeOneRight_never m1 (by simpa [writeOneRight] using h1) (k+1)
    rw [hh1.2] at hn
    contradiction
  let f := swapToOne q0
  let m' := renameTable f m1
  have hroot : f.forward 0=0 := swapToOne_root q0 hq
  have hback : f.backward 0=0 := by
    have H:=f.leftInverse 0
    rwa [hroot] at H
  have htarget : f.forward q0=1 := swapToOne_target q0
  have hfirst : m' initialSlot=some ⟨true,true,1⟩ := by
    change (m1 (f.backward 0,false)).map (renameMove f)=_
    rw [hback,show (0,false)=initialSlot from rfl,h1]
    simp [renameMove,htarget]
  have hh' : HaltsAfter m' k := by
    have H:=rename_haltsAt_iff f m1 0 k
    rw [hroot] at H
    exact H.mpr hh1
  have hp' : TerminalPath (zeroNext m') (f.forward (e.forward s)) d 0 := by
    have H:=renamed_path f m1 hp1
    rwa [hroot] at H
  exact ⟨m',hfirst,hh', (mem_delays_iff (terminal_zero_next hp')).mpr ⟨_,hp'⟩⟩

/-- Exact score-preserving normal form with a finite offset, except for
    short blank-only halters (at most six attempts including halt). -/
theorem weighted_first_one_normal_form (m : Machine) (n : Nat) (h : HaltsAfter m n) :
    n+1≤6 ∨ ∃ m' d k, m' initialSlot=some ⟨true,true,1⟩ ∧
      HaltsAfter m' k ∧ d∈delays (zeroNext m') 0 ∧ n=d+k := by
  obtain ⟨d,k,t,he,hp,hk⟩:=halting_decomposes m 0 n h
  have hd:=terminal_delay_le_five hp
  have ht:=terminal_zero_next hp
  cases h0 : m (t,false) with
  | none =>
    have hzero:=halt_blank_immediate m t k h0 hk
    exact Or.inl (by omega)
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    cases w with
    | false => simp [zeroNext,h0] at ht
    | true =>
      obtain ⟨m',hf,hh,hm⟩:=normalize_write_root m 0 t d k hp hk r q h0
      exact Or.inr ⟨m',d,k,hf,hh,hm,he⟩

/-- Every listed offset really is attained by some six-state machine, via
    re-rooting; thus this is not merely a conservative +5 bound. -/
theorem weighted_first_one_realized (m : Machine) (d k : Nat)
    (hf : m initialSlot=some ⟨true,true,1⟩) (hh : HaltsAfter m k)
    (hd : d∈delays (zeroNext m) 0) : ∃ m', HaltsAfter m' (d+k) := by
  have hzero : zeroNext m 0=none := by change (match m initialSlot with | some t => if t.write then none else some t.next | none => none)=none; rw [hf]; rfl
  obtain ⟨s,hp⟩ := (mem_delays_iff hzero).mp hd
  exact ⟨renameTable (swapToZero s) m,(root_rename m s (d+k)).mpr ((zero_path_halts_iff m s 0 d k hp).mpr hh)⟩

/-- Exact global upper-bound equivalence, eliminating the separate 0RB
    cylinder when every 1RB halter carries its exact possible offsets. -/
theorem upper_iff_weighted_first_one (B : Nat) (hB : 6≤B) :
    (∀ m n, HaltsAfter m n → n+1≤B) ↔
    (∀ m, m initialSlot=some ⟨true,true,1⟩ → ∀ k d,
      HaltsAfter m k → d∈delays (zeroNext m) 0 → d+k+1≤B) := by
  constructor
  · intro h m hf k d hh hd
    obtain ⟨m',hm'⟩:=weighted_first_one_realized m d k hf hh hd
    exact h m' _ hm'
  · intro h m n hh
    rcases weighted_first_one_normal_form m n hh with hshort|⟨m',d,k,hf,hk,hd,he⟩
    · omega
    · rw [he]
      exact h m' hf k d hk hd

#print axioms weighted_first_one_normal_form
#print axioms weighted_first_one_realized
#print axioms upper_iff_weighted_first_one
end BB6.Agent13BlankDelay
