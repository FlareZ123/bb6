import CanonicalSearch
import TranslatedFiniteOracle
namespace BB6Coverage.Canonical

/-- Produce the actual observed trace once; every proposed terminal
    witness is then rechecked by the already-proved source checkers. -/
def collectTrace (p : PartialMachine) : Nat → Nat → FinRayCfg → List (Nat × FinRayCfg)
  | 0,n,c => [(n,c)]
  | fuel+1,n,c =>
    (n,c) :: (match finitePartialStep p c with
      | none => []
      | some d => collectTrace p fuel (n+1) d)

def zeroOrbitMask (p : PartialMachine) : Nat → Fin 6 → Nat → Nat
  | 0,_,mask => mask
  | fuel+1,q,mask =>
    if mask.testBit q.val then mask
    else
      let mask' := mask ||| (1 <<< q.val)
      match p (q,false) with
      | some (some mv) => zeroOrbitMask p fuel mv.next mask'
      | _ => mask'

abbrev Leaf (p : PartialMachine) (bound : Nat) := PLift (Cover (DecidedBelow bound) p)

def traceLeaf (p : PartialMachine) (bound rayLimit : Nat) (item : Nat × FinRayCfg) :
    Option (Leaf p bound) := Id.run do
  let (n,c) := item
  if c.state.val < 6 && p (c.state,finiteTape c c.head) == some none then
    if h : n+1≤bound ∧ finiteHaltCheck p n = true then
      return some ⟨finiteHaltCheck_sound p n bound h.1 h.2⟩
  if n≤rayLimit then
    let mask := zeroOrbitMask p 6 c.state 0
    for dir in [true,false] do
      if (if dir then finiteFreshRight c else finiteFreshLeft c) &&
          rayTailCheck p dir (fun q => mask.testBit q.val) then
        if h : finiteRayCheck p n dir (fun q => mask.testBit q.val) = true then
          return some ⟨finiteRayCheck_sound p n dir (fun q => mask.testBit q.val) bound h⟩
  return none

def translatedLeaf (p : PartialMachine) (bound maxSteps : Nat)
    (trace : List (Nat × FinRayCfg)) : Option (Leaf p bound) :=
  trace.findSome? fun (n,c) =>
    if n > maxSteps then none else
    trace.findSome? fun (k,d) =>
      if k < n && shiftedFiniteEq d c then
        if h : 0<n-k ∧ finiteTranslatedCheck p k (n-k)=true then
          some ⟨finiteTranslatedCheck_sound p k (n-k) bound h.1 h.2⟩
        else none
      else none

/-- Candidate search is untrusted: every successful return includes the
    original source theorem. No proof of generator completeness is needed. -/
def fastLeaf (p : PartialMachine) (bound rayLimit lassoLimit entryLimit macroLimit farLimit : Nat) :
    Option (Leaf p bound) :=
  let mask := zeroOrbitMask p 6 0 0
  if h : zeroMaskCheck p (fun q => mask.testBit q.val)=true then
    some ⟨zeroMaskCheck_sound p (fun q => mask.testBit q.val) bound h⟩
  else
    let trace := collectTrace p (max bound (max rayLimit lassoLimit)) 0 finiteBlank
    match trace.findSome? (traceLeaf p bound rayLimit) with
    | some cert => some cert
    | none =>
      match translatedLeaf p bound lassoLimit trace with
      | some cert => some cert
      | none =>
        if h : finiteEntryMacroBiOracle p entryLimit macroLimit=true then
          some ⟨finiteEntryMacroBiOracle_sound p entryLimit macroLimit bound h⟩
        else if h : FAR.oracle p farLimit=true then
          some ⟨.leaf p (fun m hm => Or.inl (FAR.oracle_sound p farLimit h m hm))⟩
        else none

/-- Split first when an actual unknown row is reached. In that case there
    exists a compatible completion taking that row as a halt, so searching
    for a sparse all-completion nonhalt certificate is wasted work. At
    other leaves search only checked candidates, including translated cycles. -/
def fastSearch (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit : Nat) :
    (depth k : Nat) → (p : PartialMachine) → Scoped k p → (0<k ∧ k≤6) → Audit bound p k
  | depth,k,p,hp,hk =>
    match hs : firstUnknownPhysical p scanLimit finiteBlank with
    | some s =>
      match depth with
      | 0 => .unresolved p k
      | n+1 =>
        have hs' : s.1.val < k := firstUnknown_scoped p k scanLimit finiteBlank hp hk.1 s hs
        .branch p k s (firstUnknownPhysical_sound p scanLimit finiteBlank s hs) hp hs' hk
          (fun t _ => fastSearch bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit
            n (nextK k t) (refine p s t) (scoped_refine k p s t hp hs') (nextK_bounds k t hk))
    | none =>
      match fastLeaf p bound rayLimit lassoLimit entryLimit macroLimit farLimit with
      | some cert => .certified p k cert.down
      | none => .unresolved p k
termination_by depth k p hp hk => depth

def fastGlobal (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat) :
    Audit bound emptyTable 1 :=
  fastSearch bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth 1 emptyTable
    (by intro s t h; simp [emptyTable] at h) (by decide)

theorem fastGlobal_exhaustive (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat)
    (m : Machine) : DecidedBelow bound m ∨
      (fastGlobal bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth).open m :=
  (fastGlobal bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth).exhaustive m (empty_compatible m)

theorem fastGlobal_conserves (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat) :
    let a := fastGlobal bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth
    a.report.1+a.report.2 = 25^12 := by
  intro a
  calc
    _ = cylinderMass emptyTable := a.conserves
    _ = 25^12 := by decide

#print axioms fastGlobal_exhaustive
#print axioms fastGlobal_conserves
end BB6Coverage.Canonical
