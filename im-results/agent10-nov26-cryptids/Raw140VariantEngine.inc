structure CState where
  q : Fin 6
  right : Bool
  L : List SymLTok
  R : List SymRTok
  deriving DecidableEq, Repr

def ceval (v : Fin 5 → ℕ) (s : CState) : Cfg (Fin 2) (Fin 6) :=
  if s.right then Cfg.headRight s.q (encSL v s.L) (encSR v s.R)
  else Cfg.headLeft s.q (encSL v s.L) (encSR v s.R)

def cpushL (b : Fin 2) (L : List SymLTok) :=
  if b = 0 then symPushZerosL 1 L else symPushOnesL 1 L

def cpushR (b : Fin 2) (R : List SymRTok) :=
  if b = 0 then symPushZerosR 1 R else symPushOnesR 1 R

theorem cpushL_spec (v : Fin 5 → ℕ) {b : Fin 2} {L T : List SymLTok}
    (h : cpushL b L = some T) : encSL v T = b >> encSL v L := by
  fin_cases b
  · exact encSL_pushZerosL (v := v) (by simpa [cpushL] using h)
  · exact encSL_pushOnesL (v := v) (by simpa [cpushL] using h)

theorem cpushR_spec (v : Fin 5 → ℕ) {b : Fin 2} {R T : List SymRTok}
    (h : cpushR b R = some T) : encSR v T = b >> encSR v R := by
  fin_cases b
  · exact encSR_pushZerosR (v := v) (by simpa [cpushR] using h)
  · exact encSR_pushOnesR (v := v) (by simpa [cpushR] using h)

def cflip (s : CState) : Option CState := do
  if s.right then
    let (b,R) ← symPopBitR s.R
    let L ← cpushL b s.L
    return ⟨s.q,false,L,R⟩
  else
    let (b,L) ← symPopBitL s.L
    let R ← cpushR b s.R
    return ⟨s.q,true,L,R⟩

theorem cflip_spec (v : Fin 5 → ℕ) {s t : CState} (h : cflip s = some t) : ceval v s = ceval v t := by
  rcases s with ⟨q,d,L,R⟩
  cases d
  · cases hp : symPopBitL L with
    | none => simp [cflip,hp] at h
    | some p =>
      rcases p with ⟨b,L'⟩
      cases hw : cpushR b R with
      | none => simp [cflip,hp,hw] at h
      | some R' =>
        simp [cflip,hp,hw] at h
        subst t
        simp only [ceval, Bool.false_eq_true, if_false, if_true, Cfg.headLeft, Cfg.headRight,
          encSL_popBitL (v := v) hp, cpushR_spec v hw, ListBlank.head_cons, ListBlank.tail_cons]
  · cases hp : symPopBitR R with
    | none => simp [cflip,hp] at h
    | some p =>
      rcases p with ⟨b,R'⟩
      cases hw : cpushL b L with
      | none => simp [cflip,hp,hw] at h
      | some L' =>
        simp [cflip,hp,hw] at h
        subst t
        simp only [ceval, Bool.false_eq_true, if_false, if_true, Cfg.headLeft, Cfg.headRight,
          encSR_popBitR (v := v) hp, cpushL_spec v hw, ListBlank.head_cons, ListBlank.tail_cons]

def cstep (M : Machine (Fin 2) (Fin 6)) (s : CState) : Option CState := do
  if s.right then
    let (b,R) ← symPopBitR s.R
    match M s.q b with
    | some (some q, .write w .right) =>
      let L ← cpushL w s.L
      return ⟨q,true,L,R⟩
    | some (some q, .write w .left) =>
      let R' ← cpushR w R
      return ⟨q,false,s.L,R'⟩
    | _ => none
  else
    let (b,L) ← symPopBitL s.L
    match M s.q b with
    | some (some q, .write w .right) =>
      let L' ← cpushL w L
      return ⟨q,true,L',s.R⟩
    | some (some q, .write w .left) =>
      let R ← cpushR w s.R
      return ⟨q,false,L,R⟩
    | _ => none

theorem cstep_spec (v : Fin 5 → ℕ) {M : Machine (Fin 2) (Fin 6)} {s t : CState}
    (h : cstep M s = some t) : step M (ceval v s) = some (ceval v t) := by
  rcases s with ⟨q,d,L,R⟩
  cases d
  · cases hp : symPopBitL L with
    | none => simp [cstep,hp] at h
    | some p =>
      rcases p with ⟨b,L'⟩
      cases hm : M q b with
      | none => simp [cstep,hp,hm] at h
      | some tr =>
        rcases tr with ⟨qn,stmt⟩
        cases qn with
        | none => cases stmt <;> simp [cstep,hp,hm] at h
        | some q' =>
          rcases stmt with ⟨w,dir⟩
          cases dir
          · cases hw : cpushR w R with
            | none => simp [cstep,hp,hm,hw] at h
            | some R' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSL_popBitL (v := v) hp,
                cpushR_spec v hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]
          · cases hw : cpushL w L' with
            | none => simp [cstep,hp,hm,hw] at h
            | some L'' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSL_popBitL (v := v) hp,
                cpushL_spec v hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]
  · cases hp : symPopBitR R with
    | none => simp [cstep,hp] at h
    | some p =>
      rcases p with ⟨b,R'⟩
      cases hm : M q b with
      | none => simp [cstep,hp,hm] at h
      | some tr =>
        rcases tr with ⟨qn,stmt⟩
        cases qn with
        | none => cases stmt <;> simp [cstep,hp,hm] at h
        | some q' =>
          rcases stmt with ⟨w,dir⟩
          cases dir
          · cases hw : cpushR w R' with
            | none => simp [cstep,hp,hm,hw] at h
            | some R'' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSR_popBitR (v := v) hp,
                cpushR_spec v hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]
          · cases hw : cpushL w L with
            | none => simp [cstep,hp,hm,hw] at h
            | some L' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSR_popBitR (v := v) hp,
                cpushL_spec v hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]

def csym (s : CState) : Option SymState :=
  if s.q = 0 ∧ s.right = true then some (.mA,s.L,s.R)
  else if s.q = 3 ∧ s.right = false then some (.mD,s.L,s.R)
  else if s.q = 4 ∧ s.right = false then some (.mE,s.L,s.R)
  else none

theorem csym_spec (v : Fin 5 → ℕ) {s : CState} {u : SymState} (h : csym s = some u) :
    ceval v s = evalSym v u := by
  rcases s with ⟨q,d,L,R⟩
  simp only [csym] at h
  split at h
  · rename_i hq
    rcases hq with ⟨rfl,rfl⟩
    cases h
    rfl
  · split at h
    · rename_i hq
      rcases hq with ⟨rfl,rfl⟩
      cases h
      rfl
    · split at h
      · rename_i hq
        rcases hq with ⟨rfl,rfl⟩
        cases h
        rfl
      · contradiction

def cofSym : SymState → Option CState
  | (.mA,L,R) => some ⟨0,true,L,R⟩
  | (.mD,L,R) => some ⟨3,false,L,R⟩
  | (.mE,L,R) => some ⟨4,false,L,R⟩
  | (.mHalt,_,_) => none

theorem cofSym_spec (v : Fin 5 → ℕ) {u : SymState} {t : CState} (h : cofSym u = some t) :
    evalSym v u = ceval v t := by
  rcases u with ⟨m,L,R⟩
  cases m <;> cases h <;> rfl

def cmacro (s : CState) : Option CState := do
  let u ← csym s
  let v ← symStep u
  cofSym v

theorem cmacro_spec (v : Fin 5 → ℕ) {s t : CState} (h : cmacro s = some t) :
    ReachesPlus target_tm (ceval v s) (ceval v t) := by
  cases hu : csym s with
  | none => simp [cmacro,hu] at h
  | some u =>
    cases hv : symStep u with
    | none => simp [cmacro,hu,hv] at h
    | some v =>
      have ht : cofSym v = some t := by simpa [cmacro,hu,hv] using h
      rw [csym_spec v hu,← cofSym_spec v ht]
      exact symStep_sound v hv

def cnorm (s : CState) : Option CState :=
  if (s.q = 0 ∧ s.right = false) ∨ ((s.q = 3 ∨ s.q = 4) ∧ s.right = true)
  then cflip s else some s

theorem cnorm_spec (v : Fin 5 → ℕ) {s t : CState} (h : cnorm s = some t) : ceval v s = ceval v t := by
  unfold cnorm at h
  split at h
  · exact cflip_spec v h
  · cases h
    rfl

def cadvance (M : Machine (Fin 2) (Fin 6)) (s : CState) : Option CState := do
  let u ← cnorm s
  match cmacro u with
  | some v => some v
  | none => cstep M u

theorem cadvance_spec (v : Fin 5 → ℕ) (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    {s t : CState} (h : cadvance M s = some t) :
    ReachesPlus M (ceval v s) (ceval v t) := by
  cases hu : cnorm s with
  | none => simp [cadvance,hu] at h
  | some u =>
    rw [cnorm_spec v hu]
    cases hv : cmacro u with
    | none =>
      exact ReachesPlus.single (cstep_spec v (by simpa [cadvance,hu,hv] using h))
    | some v =>
      have ht : v = t := by simpa [cadvance,hu,hv] using h
      subst t
      exact reachesPlus_ext M he (cmacro_spec v hv)

def crun (M : Machine (Fin 2) (Fin 6)) : Nat → CState → Option CState
  | 0,s => some s
  | n+1,s => (cadvance M s).bind (crun M n)

theorem crun_spec (v : Fin 5 → ℕ) (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    (n : Nat) {s t : CState} (h : crun M n s = some t) :
    ReachesStar M (ceval v s) (ceval v t) := by
  induction n generalizing s with
  | zero =>
    simp [crun] at h
    subst t
    exact ReachesStar.refl _ _
  | succ n ih =>
    cases hu : cadvance M s with
    | none => simp [crun,hu] at h
    | some u =>
      have hv : crun M n u = some t := by simpa [crun,hu] using h
      exact (cadvance_spec v M he hu).to_star.trans (ih hv)

#print axioms crun_spec

def permAD (q : Fin 6) : Fin 6 := if q = 0 then 3 else if q = 3 then 0 else q
theorem permAD_inv (q : Fin 6) : permAD (permAD q) = q := by fin_cases q <;> rfl

def flipDir : Dir → Dir
  | .left => .right
  | .right => .left

def decodeMirrored (c : Nat) : Option (Option (Fin 6) × Stmt (Fin 2)) :=
  if c < 24 then
    some (some (permAD ⟨(c/4)%6, Nat.mod_lt _ (by decide)⟩),
      .write ⟨(c/2)%2, Nat.mod_lt _ (by decide)⟩ (if c%2 = 1 then .left else .right))
  else none

def cvariant (a f : Nat) : Machine (Fin 2) (Fin 6) :=
  fun q b => match target_tm q b with
  | some v => some v
  | none => if q = 3 ∧ b = 1 then decodeMirrored a
            else if q = 5 ∧ b = 0 then decodeMirrored f
            else none

theorem cvariant_ext (a f : Nat) : ExtendsRestricted (cvariant a f) := by
  intro q b v h
  simp [cvariant,h]

def cstart : CState := ⟨3,false,[],[]⟩


def Mstate (m z c k : Nat) : CState :=
  ⟨0,true,[.pair 1 0 symZero,.mid (symConst (m-1)),.pair 1 1 symZero,.pair 1 0 symZero],
    if z = 1 then
      [.pair 0 0 symZero,.pair 1 1 (symConst (6*k+4)),.mid symZero,
       .pair 1 1 (symConst (3*k)),.pair 1 2 symZero,
       .pair 1 1 (symConst (c-1)),.pair 1 0 symZero]
    else
      [.pair 0 0 symZero,.pair 1 1 (symConst (6*k+6)),.pair 2 0 (symConst (z-1)),
       .pair 1 1 (symConst (3*k)),.pair 1 2 symZero,
       .pair 1 1 (symConst (c-1)),.pair 1 0 symZero]⟩

def entryParams (s : CState) : Option (Nat × Nat × Nat × Nat) :=
  match s.q.val, s.right, s.L, s.R with
  | 0,true,[.pair 1 0 _,.mid m,.pair 1 1 _,.pair 1 0 _],
    [.pair 0 0 _,.pair 1 1 _,.mid _,.pair 1 1 k,.pair 1 2 _,.pair 1 1 c,.pair 1 0 _] =>
      let p := (m.k+1,1,c.k+1,k.k/3)
      if s = Mstate p.1 p.2.1 p.2.2.1 p.2.2.2 then some p else none
  | 0,true,[.pair 1 0 _,.mid m,.pair 1 1 _,.pair 1 0 _],
    [.pair 0 0 _,.pair 1 1 _,.pair 2 0 z,.pair 1 1 k,.pair 1 2 _,.pair 1 1 c,.pair 1 0 _] =>
      let p := (m.k+1,z.k+1,c.k+1,k.k/3)
      if s = Mstate p.1 p.2.1 p.2.2.1 p.2.2.2 then some p else none
  | _,_,_,_ => none

def searchM (M : Machine (Fin 2) (Fin 6)) (fuel : Nat) (start : CState) :
    Nat × Option (Nat × Nat × Nat × Nat) × CState := Id.run do
  let mut s := start
  for j in [:fuel] do
    if j > 0 then
      if let some p := entryParams s then
        if p.1 ≥ 33 && p.2.1 ≥ 1 && p.2.2.1 ≥ 2100 && p.2.2.1 ≥ 9*p.1 && p.2.2.2 ≤ 5 then
          return (j,some p,s)
    match cadvance M s with
    | none => return (j,none,s)
    | some t => s := t
  return (fuel,none,s)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
#eval ([(21,0),(21,3),(21,9),(23,19),(21,13)] : List (Nat × Nat)).map fun (a,f) =>
  (a,f,searchM (cvariant a f) 50000 (Mstate 33 1 2100 0))
