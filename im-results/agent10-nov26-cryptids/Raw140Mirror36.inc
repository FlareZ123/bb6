
/- New theorem for the reflected, A/D-renamed machine starting in original state D.
   The pinned upstream invariant is not changed. Its original blank theorem starts
   in state A, so a fresh entry witness is essential. -/
@[expose] public section
namespace Mirror36
abbrev V := v5 0 0 0 0 0
structure Entry where
  m : Nat
  z : Nat
  c : Nat
  k : Nat
  deriving DecidableEq, Repr

def valid (e : Entry) : Prop := InvM e.m e.z e.c e.k
instance (e : Entry) : Decidable (valid e) := by
  unfold valid InvM
  infer_instance

def canonical (e : Entry) : SymState :=
  (.mA, [.pair 1 0 symZero, .mid (symConst (e.m-1)), .pair 1 1 symZero, .pair 1 0 symZero],
    if e.z = 1 then
      [.pair 0 0 symZero, .pair 1 1 (symConst (6*e.k+4)), .mid symZero,
       .pair 1 1 (symConst (3*e.k)), .pair 1 2 symZero,
       .pair 1 1 (symConst (e.c-1)), .pair 1 0 symZero]
    else
      [.pair 0 0 symZero, .pair 1 1 (symConst (6*e.k+6)), .pair 2 0 (symConst (e.z-1)),
       .pair 1 1 (symConst (3*e.k)), .pair 1 2 symZero,
       .pair 1 1 (symConst (e.c-1)), .pair 1 0 symZero])

theorem canonical_eval (e : Entry) (he : valid e) :
    evalSym V (canonical e) = mCfg e.m e.z e.c e.k := by
  have hv : InvM e.m e.z e.c e.k := he
  rcases hv with ⟨hk,hz,hm,h9m,hc⟩
  by_cases h1 : e.z = 1
  · simp only [canonical,h1,if_true]
    have h := eval_mCfg_z1 V (symConst (e.m-1)) (symConst (6*e.k+4))
      (symConst (3*e.k)) (symConst (e.c-1)) e.m e.c e.k
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)
    simpa only [h1] using h
  · simp only [canonical,h1,if_false]
    exact eval_mCfg_z2 V (symConst (e.m-1)) (symConst (6*e.k+6))
      (symConst (e.z-1)) (symConst (3*e.k)) (symConst (e.c-1)) e.m e.z e.c e.k
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)
      (by dsimp [V,evalSymN,v5,symConst]; omega)

def propose : SymState → Option Entry
  | (.mA, [.pair 1 0 _, .mid cm, .pair 1 1 _, .pair 1 0 _],
      [.pair 0 0 _, .pair 1 1 _, .mid _, .pair 1 1 cb, .pair 1 2 _, .pair 1 1 cc, .pair 1 0 _]) =>
    some ⟨cm.k+1,1,cc.k+1,cb.k/3⟩
  | (.mA, [.pair 1 0 _, .mid cm, .pair 1 1 _, .pair 1 0 _],
      [.pair 0 0 _, .pair 1 1 _, .pair 2 0 cz, .pair 1 1 cb, .pair 1 2 _, .pair 1 1 cc, .pair 1 0 _]) =>
    some ⟨cm.k+1,cz.k+1,cc.k+1,cb.k/3⟩
  | _ => none

def checked (s : SymState) : Option Entry :=
  match propose s with
  | none => none
  | some e => if s = canonical e ∧ valid e then some e else none

theorem checked_sound {s : SymState} {e : Entry} (h : checked s = some e) :
    InAttractor (evalSym V s) := by
  unfold checked at h
  cases hp : propose s with
  | none => simp [hp] at h
  | some x =>
    simp only [hp] at h
    split at h
    · rename_i hx
      have hxe : x = e := Option.some.inj h
      subst x
      exact ⟨e.m,e.z,e.c,e.k,hx.2,hx.1 ▸ canonical_eval e hx.2⟩
    · contradiction

def search : Nat → SymState → Option (SymState × Entry)
  | 0,s => (checked s).map fun e => (s,e)
  | n+1,s => match checked s with
    | some e => some (s,e)
    | none => (symStep s).bind (search n)

theorem search_sound (n : Nat) {s t : SymState} {e : Entry}
    (h : search n s = some (t,e)) :
    ReachesStar target_tm (evalSym V s) (evalSym V t) ∧
      InAttractor (evalSym V t) := by
  induction n generalizing s with
  | zero =>
    cases hc : checked s with
    | none => simp [search,hc] at h
    | some x =>
      simp [search,hc] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨ReachesStar.refl _ _,checked_sound hc⟩
  | succ n ih =>
    cases hc : checked s with
    | some x =>
      simp [search,hc] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨ReachesStar.refl _ _,checked_sound hc⟩
    | none =>
      cases hs : symStep s with
      | none => simp [search,hc,hs] at h
      | some u =>
        have hu : search n u = some (t,e) := by simpa [search,hc,hs] using h
        obtain ⟨hr,hi⟩ := ih hu
        exact ⟨(symStep_sound V hs).to_star.trans hr,hi⟩

def start : SymState := (.mD,[],[])

-- Discovery is untrusted. A separate kernel check must certify any entry.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
#eval search 200000 start

end Mirror36
end
