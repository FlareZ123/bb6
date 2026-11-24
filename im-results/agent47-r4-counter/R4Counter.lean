import SparseZipper

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47R4Counter
open BB6Coverage Agent50Zipper

def table (action : Move) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,false,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some action)
  | _,_ => none

abbrev P : List Bool := [false,true,false,false]
abbrev J : List Bool := [false,true]

def enc : List Bool → List Bool
  | [] => [true]
  | b::bs => b::false::enc bs

def inc : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::inc bs

def M (a : Move) (k : Nat) (q q' : Fin 6) (l r l' r' : List Bool) : Prop :=
  ∀ h : Int, ∃ n h', k ≤ n ∧ zrun (table a) n ⟨q,h,l,r⟩ = some ⟨q',h',l',r'⟩

variable {a : Move}

theorem atom {k : Nat} {q q' : Fin 6} {l r l' r' : List Bool} (n : Nat) (d : Int)
    (hk : k ≤ n) (H : zrun (table a) n ⟨q,0,l,r⟩ = some ⟨q',d,l',r'⟩) : M a k q q' l r l' r' := by
  intro h
  refine ⟨n,d+h,hk,?_⟩
  have hh := zrun_shift (table a) h n ⟨q,0,l,r⟩
  rw [H] at hh
  simpa [shift] using hh

theorem M.then {k : Nat} {q u v : Fin 6} {l r s t l' r' : List Bool}
    (H : M a k q u l r s t) (G : M a 0 u v s t l' r') : M a k q v l r l' r' := by
  intro h
  obtain ⟨n,h',hn,hr⟩ := H h
  obtain ⟨m,h'',_,hs⟩ := G h'
  exact ⟨n+m,h'',by omega,join hr hs⟩

theorem M.thenPos {q u v : Fin 6} {l r s t l' r' : List Bool}
    (H : M a 0 q u l r s t) (G : M a 1 u v s t l' r') : M a 1 q v l r l' r' := by
  intro h
  obtain ⟨n,h',_,hr⟩ := H h
  obtain ⟨m,h'',hm,hs⟩ := G h'
  exact ⟨n+m,h'',by omega,join hr hs⟩

theorem M.weaken {q u : Fin 6} {l r s t : List Bool} (H : M a 1 q u l r s t) : M a 0 q u l r s t := by
  intro h; obtain ⟨n,h',_,hr⟩ := H h; exact ⟨n,h',by omega,hr⟩

theorem M.refl (q : Fin 6) (l r : List Bool) : M a 0 q q l r l r := by
  intro h; exact ⟨0,h,Nat.le_refl _,rfl⟩

-- D/E carry travels left across ones; A returns right, clearing them.
theorem carry : ∀ bs R : List Bool,
    M a 0 3 0 (enc bs) (true::R) (true::enc (inc bs)) R := by
  intro bs
  induction bs with
  | nil => intro R; exact atom 5 1 (by decide) rfl
  | cons b bs ih =>
    intro R
    cases b with
    | false => exact atom 1 1 (by decide) rfl
    | true =>
      have h1 : M a 0 3 3 (true::false::enc bs) (true::R) (enc bs) (true::true::true::R) := atom 2 (-2) (by decide) rfl
      have h2 := ih (true::true::R)
      have h3 : M a 0 0 0 (true::enc (inc bs)) (true::true::R) (true::false::false::enc (inc bs)) R := atom 2 2 (by decide) rfl
      exact (h1.then h2).then h3

abbrev zeroLE : Move := ⟨false,false,4⟩
abbrev oneLE : Move := ⟨true,false,4⟩
abbrev oneRC : Move := ⟨true,true,2⟩
abbrev oneRE : Move := ⟨true,true,4⟩
abbrev zeroRA : Move := ⟨false,true,0⟩

theorem finish (L R : List Bool) : M a 0 0 5 (true::L) ([true,false,true]++R) (P++L) R :=
  atom 5 3 (by decide) rfl

theorem le0Start (L : List Bool) : M zeroLE 1 5 3 (P++L) [false] L [true,true,false,false,false] := atom 6 (-4) (by decide) rfl

theorem le0Middle (L : List Bool) : M zeroLE 0 0 3 (true::L) [true,false,false,false] L [true,true,false,true,false] := atom 11 (-1) (by decide) rfl

theorem le0Step (bs : List Bool) : M zeroLE 1 5 5 (P++enc bs) [false] (P++enc (inc (inc bs))) [false] :=
  ((((le0Start (enc bs)).then (carry bs [true,false,false,false])).then (le0Middle _)).then (carry (inc bs) [true,false,true,false])).then (finish _ [false])

theorem le1Start (L : List Bool) : M oneLE 1 5 3 (P++L) [false] L [true,true,false,true,false] := atom 6 (-4) (by decide) rfl

theorem rc1Start (L : List Bool) : M oneRC 1 5 3 (P++L) [false] L [true,true,false,true,false] := atom 8 (-4) (by decide) rfl

theorem re1Start (L : List Bool) : M oneRE 1 5 3 (P++L) [false] L [true,true,false,true,true] := atom 8 (-4) (by decide) rfl

theorem re1Restore (L : List Bool) : M oneRE 0 5 5 (P++L) [true] (P++L) [false] := atom 4 0 (by decide) rfl

theorem le1Step (bs : List Bool) : M oneLE 1 5 5 (P++enc bs) [false] (P++enc (inc bs)) [false] :=
  ((le1Start _).then (carry bs [true,false,true,false])).then (finish _ [false])

theorem rc1Step (bs : List Bool) : M oneRC 1 5 5 (P++enc bs) [false] (P++enc (inc bs)) [false] :=
  ((rc1Start _).then (carry bs [true,false,true,false])).then (finish _ [false])

theorem re1Step (bs : List Bool) : M oneRE 1 5 5 (P++enc bs) [false] (P++enc (inc bs)) [false] :=
  (((re1Start _).then (carry bs [true,false,true,true])).then (finish _ [true])).then (re1Restore _)

-- A growing right shuttle for 0RA. Both shuttles use the same counter carry.
def repJ : Nat → List Bool
  | 0 => []
  | n+1 => J++repJ n

def buf (n : Nat) : List Bool := repJ n++[false]

theorem repJ_snoc (n : Nat) : repJ n++J = repJ (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [repJ,List.append_assoc,ih]

theorem buf_succ (n : Nat) : buf (n+1) = J++buf n := by simp [buf,repJ]

theorem raForward (L R : List Bool) : M zeroRA 0 5 5 (J++L) (J++R) (J++J++L) R := atom 4 2 (by decide) rfl

theorem raRight (k : Nat) (L : List Bool) : M zeroRA 0 5 5 (J++L) (buf k) (repJ (k+1)++L) [false] := by
  induction k generalizing L with
  | zero => exact M.refl _ _ _
  | succ k ih =>
    rw [buf_succ]
    have h := (raForward L (buf k)).then (ih (J++L))
    simpa only [← List.append_assoc,repJ_snoc] using h

theorem raTurn (L : List Bool) : M zeroRA 1 5 1 (false::L) [false] (false::L) (buf 1) := atom 6 0 (by decide) rfl

theorem raTurnJ (k : Nat) (L : List Bool) : M zeroRA 1 5 1 (repJ (k+1)++L) [false] (repJ (k+1)++L) (buf 1) := by
  exact raTurn _

theorem raBackward (L R : List Bool) : M zeroRA 0 1 1 (J++L) (false::R) L (J++false::R) := atom 4 (-2) (by decide) rfl

theorem raBack (k m : Nat) (L : List Bool) : M zeroRA 0 1 1 (repJ k++L) (buf m) L (buf (k+m)) := by
  induction k generalizing m with
  | zero => simpa [repJ] using (M.refl (a:=zeroRA) 1 L (buf m))
  | succ k ih =>
    have h1 : M zeroRA 0 1 1 (J++repJ k++L) (buf m) (repJ k++L) (buf (m+1)) := by
      cases m with
      | zero => exact raBackward _ _
      | succ m => exact raBackward _ _
    have h2 := ih (m+1)
    have hh := h1.then h2
    rw [show k+1+m = k+(m+1) by omega]
    simpa only [repJ,List.append_assoc] using hh

theorem raBase (L R : List Bool) : M zeroRA 0 1 3 (P++L) (false::R) L (true::true::J++false::R) := atom 8 (-4) (by decide) rfl

theorem raStep (bs : List Bool) (k : Nat) : M zeroRA 1 5 5 (P++enc bs) (buf k) (P++enc (inc bs)) (buf (k+1)) := by
  have h1 := raRight k (false::false::enc bs)
  have h2 := raTurnJ k (false::false::enc bs)
  have h12 := h1.thenPos h2
  have h12' : M zeroRA 1 5 1 (P++enc bs) (buf k) (repJ k++P++enc bs) (buf 1) := by
    simp only [List.append_assoc]
    change M zeroRA 1 5 1 (J++false::false::enc bs) (buf k) (repJ k++(J++false::false::enc bs)) (buf 1)
    simpa only [← repJ_snoc,List.append_assoc] using h12
  have h3 := raBack k 1 (P++enc bs)
  have h4 : M zeroRA 0 1 3 (P++enc bs) (buf (k+1)) (enc bs) (true::true::buf (k+2)) := by
    rw [buf_succ (k+1),buf_succ k]
    exact raBase _ _
  have h5 := carry (a:=zeroRA) bs (true::buf (k+2))
  have h6 : M zeroRA 0 0 5 (true::enc (inc bs)) (true::buf (k+2)) (P++enc (inc bs)) (buf (k+1)) := by
    rw [buf_succ (k+1)]
    exact finish _ _
  simp only [List.append_assoc] at h12'
  exact ((((h12'.then h3).then h4).then h5).then h6)

def start : Z := ⟨0,0,[],[]⟩

theorem forever (a : Move) (G : List Bool → List Bool → Prop)
    (initial : ∃ l r, G l r ∧ zrun (table a) 15 start = some ⟨5,1,l,r⟩)
    (stepG : ∀ l r, G l r → ∃ l' r', G l' r' ∧ M a 1 5 5 l r l' r')
    (n : Nat) : ∃ z, zrun (table a) n start = some z := by
  have hlong (k : Nat) : ∃ n h l r, k ≤ n ∧ G l r ∧ zrun (table a) n start = some ⟨5,h,l,r⟩ := by
    induction k with
    | zero =>
      obtain ⟨l,r,hg,hr⟩ := initial
      exact ⟨15,1,l,r,by omega,hg,hr⟩
    | succ k ih =>
      obtain ⟨n,h,l,r,hn,hg,hr⟩ := ih
      obtain ⟨l',r',hg',hs⟩ := stepG l r hg
      obtain ⟨m,h',hm,hs'⟩ := hs h
      exact ⟨n+m,h',l',r',by omega,hg',join hr hs'⟩
  obtain ⟨t,h,l,r,ht,_,hr⟩ := hlong n
  rw [show t = n+(t-n) by omega,zrun_add] at hr
  cases hn : zrun (table a) n start with
  | none => simp [hn] at hr
  | some z => exact ⟨z,rfl⟩

theorem counter_forever (a : Move) (f : List Bool → List Bool)
    (hstep : ∀ bs, M a 1 5 5 (P++enc bs) [false] (P++enc (f bs)) [false])
    (n : Nat) : ∃ z, zrun (table a) n start = some z := by
  apply forever a (fun l r => ∃ bs, l = P++enc bs ∧ r = [false]) _ _ n
  · exact ⟨_,_,⟨[],rfl,rfl⟩,rfl⟩
  · rintro l r ⟨bs,rfl,rfl⟩
    exact ⟨_,_,⟨f bs,rfl,rfl⟩,hstep bs⟩

theorem all_defined_LE0 : ∀ n, ∃ z, zrun (table zeroLE) n start = some z := counter_forever zeroLE (fun bs => inc (inc bs)) le0Step
theorem all_defined_LE1 : ∀ n, ∃ z, zrun (table oneLE) n start = some z := counter_forever oneLE inc le1Step
theorem all_defined_RC1 : ∀ n, ∃ z, zrun (table oneRC) n start = some z := counter_forever oneRC inc rc1Step
theorem all_defined_RE1 : ∀ n, ∃ z, zrun (table oneRE) n start = some z := counter_forever oneRE inc re1Step

theorem all_defined_RA0 (n : Nat) : ∃ z, zrun (table zeroRA) n start = some z := by
  apply forever zeroRA (fun l r => ∃ bs k, l = P++enc bs ∧ r = buf k) _ _ n
  · exact ⟨_,_,⟨[],0,rfl,rfl⟩,rfl⟩
  · rintro l r ⟨bs,k,rfl,rfl⟩
    exact ⟨_,_,⟨inc bs,k+1,rfl,rfl⟩,raStep bs k⟩

#print axioms all_defined_LE0
#print axioms all_defined_LE1
#print axioms all_defined_RC1
#print axioms all_defined_RE1
#print axioms all_defined_RA0
end BB6Coverage.Agent47R4Counter
