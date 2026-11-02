import Symmetry
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

/-- Agreement of translated control, head, and every tape cell to the right
    of a fixed origin; no constraints on the tape to the left. -/
def RayAgree (origin : Int) (q r : Config) : Prop :=
  q.state = r.state ∧ q.head = origin+r.head ∧
    ∀ x, origin ≤ x → q.tape x = r.tape (x-origin)

def FreshRay (q : Config) : Prop :=
  q.state = 0 ∧ ∀ x, q.head ≤ x → q.tape x = false

private theorem ray_step (origin : Int) (q r : Config) (mv : Move)
    (h : RayAgree origin q r) :
    RayAgree origin (applyMove q mv) (applyMove r mv) := by
  obtain ⟨hs,hh,ht⟩ := h
  constructor
  · rfl
  constructor
  · simp [applyMove,hh,Int.add_assoc]
  · intro x hx
    have hiff : (x=q.head) ↔ (x-origin=r.head) := by
      rw [hh]
      omega
    by_cases he : x=q.head
    · have hread := hiff.mp he
      subst x
      simp [applyMove,hread]
    · have hre : x-origin≠r.head := by
        intro he'
        exact he (hiff.mpr he')
      simp [applyMove,he,hre,ht x hx]

private theorem ray_read (origin : Int) (q r : Config)
    (h : RayAgree origin q r) (hpos : 0≤r.head) :
    readSlot q = readSlot r := by
  obtain ⟨hs,hh,ht⟩ := h
  have hge : origin≤q.head := by rw [hh]; omega
  have hteq := ht q.head hge
  have hhead : q.head-origin=r.head := by omega
  simp [readSlot,hs,hteq,hhead]

private theorem ray_raw (m : Machine) (origin : Int) (q r r' : Config)
    (h : RayAgree origin q r) (hpos : 0≤r.head)
    (hr : rawStep m r=some r') :
    ∃ q', rawStep m q=some q' ∧ RayAgree origin q' r' := by
  have hread := ray_read origin q r h hpos
  cases hm : m (readSlot r) with
  | none => simp [rawStep,hm] at hr
  | some mv =>
    have heq : r'=applyMove r mv := by
      simpa [rawStep,hm] using hr.symm
    subst r'
    refine ⟨applyMove q mv, ?_, ray_step origin q r mv h⟩
    simp [rawStep,hread,hm]

private theorem ray_transfer (m : Machine) (origin : Int) (q r : Config)
    (h : RayAgree origin q r) :
    ∀ n, (∀ k, k<n → ∀ d, run m k r=some d → 0≤d.head) →
      ∀ r', run m n r=some r' →
        ∃ q', run m n q=some q' ∧ RayAgree origin q' r' := by
  intro n
  induction n with
  | zero =>
    intro _ r' hr
    have hre : r'=r := by simpa [run] using hr.symm
    subst r'
    exact ⟨q,rfl,h⟩
  | succ n ih =>
    intro hp r' hr
    cases hmid : run m n r with
    | none => simp [run,hmid] at hr
    | some d =>
      have hpref : ∀ k, k<n → ∀ t, run m k r=some t → 0≤t.head := by
        intro k hk t ht
        exact hp k (by omega) t ht
      obtain ⟨qmid,hqmid,hagree⟩ := ih hpref d hmid
      have hdpos : 0≤d.head := hp n (by omega) d hmid
      have hrstep : rawStep m d=some r' := by
        simpa [run,hmid] using hr
      obtain ⟨q',hstep,hagree'⟩ := ray_raw m origin qmid d r' hagree hdpos hrstep
      refine ⟨q', ?_, hagree'⟩
      simp [run,hqmid,hstep]

private theorem still_blank_above (c : Config) (mv : Move) (bar : Int)
    (hb : ∀ x, bar≤x → c.tape x=false) (hhead : c.head<bar) :
    ∀ x, bar≤x → (applyMove c mv).tape x=false := by
  intro x hx
  have hneq : x≠c.head := by omega
  simp [applyMove,hneq,hb x hx]

private theorem untouched_prefix (m : Machine) (r : Config) (bar : Int)
    (hb : ∀ x, bar≤x → r.tape x=false) :
    ∀ n, (∀ k, k<n → ∀ d, run m k r=some d → d.head<bar) →
      ∀ r', run m n r=some r' →
        ∀ x, bar≤x → r'.tape x=false := by
  intro n
  induction n with
  | zero =>
    intro _ r' hr
    have hre : r'=r := by simpa [run] using hr.symm
    subst r'
    exact hb
  | succ n ih =>
    intro hp r' hr
    cases hmid : run m n r with
    | none => simp [run,hmid] at hr
    | some d =>
      have hprev : ∀ k, k<n → ∀ t, run m k r=some t → t.head<bar := by
        intro k hk t ht
        exact hp k (by omega) t ht
      have hdb := ih hprev d hmid
      have hdhead : d.head<bar := hp n (by omega) d hmid
      have hrstep : rawStep m d=some r' := by simpa [run,hmid] using hr
      cases hm : m (readSlot d) with
      | none => simp [rawStep,hm] at hrstep
      | some mv =>
        have heq : r'=applyMove d mv := by simpa [rawStep,hm] using hrstep.symm
        subst r'
        exact still_blank_above d mv bar hdb hdhead

private theorem run_add_macro (m : Machine) (q : Config) (n k : Nat) :
    run m (n+k) q = (run m n q).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.add_succ,run,ih]
    cases h : run m n q with
    | none => simp
    | some d => rfl

private theorem run_prefix_macro (m : Machine) (q : Config) (N n : Nat)
    (hn : n≤N) (hN : (run m N q).isSome=true) :
    (run m n q).isSome=true := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k,hk⟩
  cases h : run m n q with
  | some d => simp
  | none =>
    have hm : run m N q=none := by
      rw [hk,run_add_macro,h]
      rfl
    simp [hm] at hN

/-- A single finite blank macro with final blank right ray can be replayed
    from every virgin-right boundary, without assuming periodic old output. -/
theorem fresh_ray_macro (m : Machine) (n delta : Nat)
    (hdelta : 0<delta)
    (htrace : ∃ r, run m n blank=some r ∧ r.state=0 ∧ r.head=(delta:Int) ∧
      ∀ x, (delta:Int)≤x → r.tape x=false)
    (hwindow : ∀ k, k<n → ∀ d, run m k blank=some d → 0≤d.head) :
    ∀ q, FreshRay q → ∃ q', run m n q=some q' ∧ FreshRay q' ∧
      q'.head = q.head + delta := by
  intro q hq
  obtain ⟨rs,hrs,hstate,hhead,hb⟩ := htrace
  let origin := q.head
  have hstart : RayAgree origin q blank := by
    constructor
    · exact hq.1
    constructor
    · simp [origin,blank]
    · intro x hx
      simp [blank,hq.2 x (by simpa [origin] using hx)]
  obtain ⟨qs,hqs,hagree⟩ := ray_transfer m origin q blank hstart n hwindow rs hrs
  refine ⟨qs,hqs,?_,?_⟩
  · constructor
    · exact hagree.1.trans hstate
    · intro x hx
      have horigin : origin≤x := by
        rw [hagree.2.1,hhead] at hx
        dsimp [origin]
        omega
      have ht := hagree.2.2 x horigin
      rw [ht]
      apply hb (x-origin)
      rw [hagree.2.1,hhead] at hx
      omega
  · dsimp [origin] at hagree
    rw [hagree.2.1,hhead]

/-- Finite ray-pumping lemma certifies all-time blank-start nonhalting. -/
theorem fresh_ray_macro_never (m : Machine) (n delta : Nat)
    (hn : 0<n) (hdelta : 0<delta)
    (htrace : ∃ r, run m n blank=some r ∧ r.state=0 ∧ r.head=(delta:Int) ∧
      ∀ x, (delta:Int)≤x → r.tape x=false)
    (hwindow : ∀ k, k<n → ∀ d, run m k blank=some d → 0≤d.head) : NeverHalts m := by
  have hm := fresh_ray_macro m n delta hdelta htrace hwindow
  have hall : ∀ t, ∃ q, run m (n*t) blank=some q ∧ FreshRay q := by
    intro t
    induction t with
    | zero =>
      exact ⟨blank,rfl,by constructor <;> simp [blank]⟩
    | succ t ih =>
      obtain ⟨q,hq,hfresh⟩ := ih
      obtain ⟨q',hmacro,hfresh',_⟩ := hm q hfresh
      refine ⟨q',?_,hfresh'⟩
      have htime : n*(t+1)=n*t+n := by simp [Nat.mul_add]
      rw [htime,run_add_macro,hq]
      exact hmacro
  intro t
  obtain ⟨q,hq,_⟩ := hall (t+1)
  have hle : 1*(t+1) ≤ n*(t+1) :=
    Nat.mul_le_mul_right (t+1) (Nat.succ_le_of_lt hn)
  apply run_prefix_macro m blank (n*(t+1)) t (by omega)
  simp [hq]

/-- Faster sufficient condition when no step reads beyond the fresh endpoint. -/
theorem fresh_ray_macro_never_window (m : Machine) (n delta : Nat)
    (hn : 0<n) (hdelta : 0<delta)
    (htrace : ∃ r, run m n blank=some r ∧ r.state=0 ∧ r.head=(delta:Int))
    (hwindow : ∀ k, k<n → ∀ d, run m k blank=some d →
      0≤d.head ∧ d.head<(delta:Int)) : NeverHalts m := by
  obtain ⟨r,hr,hs,hh⟩ := htrace
  have hb : ∀ x, (delta:Int)≤x → r.tape x=false := by
    apply untouched_prefix m blank (delta:Int)
    · intro x hx
      rfl
    · intro k hk d hd
      exact (hwindow k hk d hd).2
    · exact hr
  apply fresh_ray_macro_never m n delta hn hdelta ⟨r,hr,hs,hh,hb⟩
  intro k hk d hd
  exact (hwindow k hk d hd).1

/-- Reflected finite-macro lemma for leftward pristine-ray advancement. -/
theorem fresh_left_macro_never (m : Machine) (n delta : Nat)
    (hn : 0<n) (hdelta : 0<delta)
    (htrace : ∃ r, run m n blank=some r ∧ r.state=0 ∧
      r.head=-(delta:Int) ∧
      ∀ x, x≤-(delta:Int) → r.tape x=false)
    (hwindow : ∀ k, k<n → ∀ d, run m k blank=some d → d.head≤0) :
    NeverHalts m := by
  obtain ⟨r,hr,hs,hh,hb⟩ := htrace
  have hmir : run (reflectTable m) n blank=some (mirrorConfig r) := by
    have h := mirror_run m blank n
    simpa only [mirror_blank,hr,Option.map_some] using h
  have hmr : (mirrorConfig r).head = (delta:Int) := by
    simp [mirrorConfig,hh]
  have hmb : ∀ x, (delta:Int)≤x → (mirrorConfig r).tape x=false := by
    intro x hx
    have hneg : -x≤-(delta:Int) := by omega
    simpa [mirrorConfig] using hb (-x) hneg
  have hp : ∀ k, k<n → ∀ d, run (reflectTable m) k blank=some d → 0≤d.head := by
    intro k hk d hd
    have hkRun := mirror_run m blank k
    simp only [mirror_blank] at hkRun
    cases hpRun : run m k blank with
    | none =>
      simp only [hpRun,Option.map_none] at hkRun
      rw [hkRun] at hd
      contradiction
    | some c =>
      have hdm : d=mirrorConfig c := by
        have hsm : some d=some (mirrorConfig c) := by
          rw [← hd,hkRun,hpRun]
          rfl
        exact Option.some.inj hsm
      subst d
      have hneg := hwindow k hk c hpRun
      simpa [mirrorConfig] using hneg
  have hnon := fresh_ray_macro_never (reflectTable m) n delta hn hdelta
    ⟨mirrorConfig r,hmir,by simpa [mirrorConfig] using hs,hmr,hmb⟩ hp
  intro t
  have htrans := mirror_run m blank t
  simp only [mirror_blank] at htrans
  cases hm : run m t blank with
  | none =>
    simp only [hm,Option.map_none] at htrans
    have hn' := hnon t
    rw [htrans] at hn'
    simp at hn'
  | some q => simp

#print axioms fresh_ray_macro
#print axioms fresh_ray_macro_never
#print axioms fresh_ray_macro_never_window
#print axioms fresh_left_macro_never
/-- Configuration with arbitrary initial state on a globally blank tape. -/
def stateBlank (s : Fin 6) : Config :=
  { state := s, head := 0, tape := fun _ => false }

/-- A state-specific ray frontier, allowing a distinct initial preamble. -/
def FreshState (s : Fin 6) (q : Config) : Prop :=
  q.state = s ∧ ∀ x, q.head ≤ x → q.tape x = false

/-- A ray-pumping step from any control state, even if this state was
    reached after an arbitrary finite blank-start entry. -/
theorem fresh_ray_state_step (m : Machine) (s : Fin 6) (n delta : Nat)
    (hdelta : 0 < delta)
    (htrace : ∃ r, run m n (stateBlank s) = some r ∧
      r.state = s ∧ r.head = (delta : Int) ∧
      ∀ x, (delta : Int) ≤ x → r.tape x = false)
    (hwindow : ∀ k, k < n → ∀ d,
      run m k (stateBlank s) = some d → 0 ≤ d.head) :
    ∀ q, FreshState s q →
      ∃ q', run m n q = some q' ∧
        FreshState s q' ∧ q'.head = q.head + delta := by
  intro q hq
  obtain ⟨rs, hrs, hstate, hhead, hb⟩ := htrace
  let origin := q.head
  have hstart : RayAgree origin q (stateBlank s) := by
    constructor
    · exact hq.1
    constructor
    · simp [origin, stateBlank]
    · intro x hx
      simp [stateBlank, hq.2 x (by simpa [origin] using hx)]
  obtain ⟨qs, hqs, hagree⟩ :=
    ray_transfer m origin q (stateBlank s) hstart n hwindow rs hrs
  refine ⟨qs, hqs, ?_, ?_⟩
  · constructor
    · exact hagree.1.trans hstate
    · intro x hx
      have horigin : origin ≤ x := by
        rw [hagree.2.1, hhead] at hx
        dsimp [origin]
        omega
      have ht := hagree.2.2 x horigin
      rw [ht]
      apply hb (x-origin)
      rw [hagree.2.1, hhead] at hx
      omega
  · dsimp [origin] at hagree
    rw [hagree.2.1, hhead]

/-- The positive-shift state-specific macro runs forever when initiated
    from any configuration carrying a fresh ray of the correct state. -/
theorem fresh_ray_state_never_from (m : Machine) (s : Fin 6)
    (n delta : Nat) (hn : 0 < n) (hdelta : 0 < delta)
    (htrace : ∃ r, run m n (stateBlank s) = some r ∧
      r.state = s ∧ r.head = (delta : Int) ∧
      ∀ x, (delta : Int) ≤ x → r.tape x = false)
    (hwindow : ∀ k, k < n → ∀ d,
      run m k (stateBlank s) = some d → 0 ≤ d.head)
    (q : Config) (hq : FreshState s q) :
    ∀ t, (run m t q).isSome = true := by
  have hm := fresh_ray_state_step m s n delta hdelta htrace hwindow
  have hall : ∀ z, ∃ r, run m (n*z) q = some r ∧ FreshState s r := by
    intro z
    induction z with
    | zero =>
        exact ⟨q, rfl, hq⟩
    | succ z ih =>
        obtain ⟨r, hr, hfresh⟩ := ih
        obtain ⟨r', hnstep, hfresh', _⟩ := hm r hfresh
        refine ⟨r', ?_, hfresh'⟩
        have ht : n*(z+1) = n*z+n := by simp [Nat.mul_add]
        rw [ht, run_add_macro, hr]
        exact hnstep
  intro t
  obtain ⟨r, hr, _⟩ := hall (t+1)
  have hmul : 1*(t+1) ≤ n*(t+1) :=
    Nat.mul_le_mul_right (t+1) (Nat.succ_le_of_lt hn)
  exact run_prefix_macro m q (n*(t+1)) t (by omega) (by simp [hr])

/-- A finite genuine blank-start entry into a fresh state-specific
    frontier, followed by a repeatable macro, proves all-time nonhalting. -/
theorem entry_fresh_state_never (m : Machine) (s : Fin 6)
    (entrySteps n delta : Nat) (hn : 0 < n) (hdelta : 0 < delta)
    (hentry : ∃ q, run m entrySteps blank = some q ∧ FreshState s q)
    (htrace : ∃ r, run m n (stateBlank s) = some r ∧
      r.state = s ∧ r.head = (delta : Int) ∧
      ∀ x, (delta : Int) ≤ x → r.tape x = false)
    (hwindow : ∀ k, k < n → ∀ d,
      run m k (stateBlank s) = some d → 0 ≤ d.head) :
    NeverHalts m := by
  obtain ⟨q, hq, hfresh⟩ := hentry
  have htail := fresh_ray_state_never_from m s n delta
    hn hdelta htrace hwindow q hfresh
  intro t
  have htotal : (run m (entrySteps+t) blank).isSome = true := by
    rw [run_add_macro, hq]
    exact htail t
  exact run_prefix_macro m blank (entrySteps+t) t (by omega) htotal

#print axioms fresh_ray_state_step
#print axioms fresh_ray_state_never_from
#print axioms entry_fresh_state_never

/-- Reflection fixes a blank tape with arbitrary control state. -/
@[simp] theorem mirror_stateBlank (s : Fin 6) :
    mirrorConfig (stateBlank s) = stateBlank s := rfl

/-- The arbitrary-state genuine-entry macro theorem also holds for a
    pristine left ray, by physical-tape reflection of the entire run. -/
theorem entry_fresh_state_never_left (m : Machine) (s : Fin 6)
    (entrySteps n delta : Nat) (hn : 0 < n) (hdelta : 0 < delta)
    (hentry : ∃ q, run m entrySteps blank = some q ∧
      q.state = s ∧ ∀ x, x ≤ q.head → q.tape x = false)
    (htrace : ∃ r, run m n (stateBlank s) = some r ∧
      r.state = s ∧ r.head = -(delta : Int) ∧
      ∀ x, x ≤ -(delta : Int) → r.tape x = false)
    (hwindow : ∀ k, k < n → ∀ d,
      run m k (stateBlank s) = some d → d.head ≤ 0) :
    NeverHalts m := by
  obtain ⟨q, hq, hstate, hblank⟩ := hentry
  obtain ⟨r, hr, hrs, hhead, hrblank⟩ := htrace
  have hentryMirror :
      ∃ q', run (reflectTable m) entrySteps blank = some q' ∧
        FreshState s q' := by
    refine ⟨mirrorConfig q, ?_, ?_⟩
    · have h := mirror_run m blank entrySteps
      simpa only [mirror_blank, hq, Option.map_some] using h
    · constructor
      · simpa [mirrorConfig] using hstate
      · intro x hx
        have hle : -x ≤ q.head := by
          simp only [mirrorConfig] at hx
          omega
        simpa [mirrorConfig] using hblank (-x) hle
  have htraceMirror :
      ∃ r', run (reflectTable m) n (stateBlank s) = some r' ∧
        r'.state = s ∧ r'.head = (delta : Int) ∧
        ∀ x, (delta : Int) ≤ x → r'.tape x = false := by
    refine ⟨mirrorConfig r, ?_, ?_, ?_, ?_⟩
    · have h := mirror_run m (stateBlank s) n
      simpa only [mirror_stateBlank, hr, Option.map_some] using h
    · simpa [mirrorConfig] using hrs
    · simp [mirrorConfig, hhead]
    · intro x hx
      have hle : -x ≤ -(delta : Int) := by omega
      simpa [mirrorConfig] using hrblank (-x) hle
  have hwindowMirror : ∀ k, k < n → ∀ d,
      run (reflectTable m) k (stateBlank s) = some d → 0 ≤ d.head := by
    intro k hk d hd
    have h := mirror_run m (stateBlank s) k
    simp only [mirror_stateBlank] at h
    cases hactual : run m k (stateBlank s) with
    | none =>
        simp only [hactual, Option.map_none] at h
        rw [h] at hd
        contradiction
    | some c =>
        have heq : d = mirrorConfig c := by
          have hc : some d = some (mirrorConfig c) := by
            rw [← hd, h, hactual]
            rfl
          exact Option.some.inj hc
        subst d
        have hle := hwindow k hk c hactual
        simpa [mirrorConfig] using hle
  have hnever := entry_fresh_state_never (reflectTable m) s
    entrySteps n delta hn hdelta hentryMirror htraceMirror hwindowMirror
  intro t
  have h := mirror_run m blank t
  simp only [mirror_blank] at h
  cases ht : run m t blank with
  | none =>
      simp only [ht, Option.map_none] at h
      have hbad := hnever t
      rw [h] at hbad
      simp at hbad
  | some q => simp

#print axioms entry_fresh_state_never_left

end BB6Coverage
