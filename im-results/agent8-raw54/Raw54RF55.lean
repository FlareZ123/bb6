import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF55
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def Zs (n : Nat) := rep [false] n
def Os (n : Nat) := rep [true] n

inductive Stack : List Bool → Prop
  | nil : Stack []
  | z (L : List Bool) : Stack L → Stack (false::false::false::L)
  | o (L : List Bool) : Stack L → Stack (true::true::L)

theorem stack_zeros (k : Nat) (L : List Bool) (h : Stack L) :
    Stack (Zs (3*k) ++ L) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 3*(k+1)=3*k+3 by omega]
    exact Stack.z _ ih

theorem stack_split (L : List Bool) (h : Stack L) :
    ∃ p V, L = Os (2*p) ++ V ∧
      (V=[] ∨ ∃ T, V=false::false::false::T ∧ Stack T) := by
  induction h with
  | nil => exact ⟨0,[],rfl,Or.inl rfl⟩
  | z L h ih => exact ⟨0,false::false::false::L,rfl,Or.inr ⟨L,rfl,h⟩⟩
  | o L h ih =>
    obtain ⟨p,V,he,hV⟩ := ih
    refine ⟨p+1,V,?_,hV⟩
    rw [show 2*(p+1)=2*p+2 by omega]
    exact congrArg (fun x => true::true::x) he

/-- Finite gaps have odd length; each nonterminal one-run is 1 mod 3. -/
inductive Runs where
  | last (n : Nat)
  | cons (k g : Nat) (tail : Runs)

def encode : Runs → List Bool
  | .last n => Os (n+1)
  | .cons k g u => Os (3*k+1) ++ Zs (2*g+1) ++ encode u

def cfg (L : List Bool) (u : Runs) : Z0 :=
  ⟨0,L,true::true::encode u⟩

/-- The A/B/C entry sweeps a nonempty one-run of length n+3. -/
theorem scan (L : List Bool) (n : Nat) (T : List Bool)
    (hL : L.headD false = false) (hT : T.headD false = false) :
    run0 table (n+4) ⟨0,L,Os (n+3) ++ T⟩ =
      some ⟨2,Zs (n+3) ++ true::true::L.tail,T.tail⟩ := by
  have a : run0 table 2 ⟨0,L,Os (n+3) ++ T⟩ =
      some ⟨2,true::true::true::L.tail,Os (n+1) ++ T⟩ := by
    cases L with
    | nil => rfl
    | cons b L =>
      cases b
      · rfl
      · simp at hL
  have b := sweepR table 2 [true] [] [true] [false] 1
    (by intro X Y; rfl) (n+1) (true::true::L.tail) T
  simp only [List.nil_append,List.cons_append,List.append_assoc,Nat.one_mul] at b
  have c : run0 table 1 ⟨2,true::(Zs (n+1) ++ true::true::L.tail),T⟩ =
      some ⟨2,Zs (n+3) ++ true::true::L.tail,T.tail⟩ := by
    cases T with
    | nil => rfl
    | cons b T =>
      cases b
      · rfl
      · simp at hT
  have H := join0 (join0 a b) c
  simpa only [show 2+(n+1)+1=n+4 by omega] using H

/-- Single-zero gap: the left tail acquires n zeros and one 11 block. -/
theorem carry (n : Nat) (L : List Bool) (u : Runs) :
    run0 table 6 ⟨2,Zs (n+3) ++ true::true::L,encode u⟩ =
      some (cfg (false::(Zs n ++ true::true::L)) u) := by
  cases u <;> rfl

theorem z_snoc (n : Nat) (T : List Bool) :
    Zs n ++ false::T = Zs (n+1) ++ T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false::(Zs n ++ false::T) = false::(Zs (n+1) ++ T)
    rw [ih]

/-- A longer gap (or blank extension) triggers a full D/E reset. -/
theorem reset (n p : Nat) (V R : List Bool)
    (hR : R.headD false = false) :
    ∃ t, 0<t ∧ run0 table t
      ⟨2,Zs (n+3) ++ true::true::(Os p ++ V),R⟩ =
      some ⟨4,V,Zs (p+2) ++ (Os (n+4) ++ R.tail)⟩ := by
  have a : run0 table 1 ⟨2,Zs (n+3) ++ true::true::(Os p ++ V),R⟩ =
      some ⟨3,Zs (n+4) ++ true::true::(Os p ++ V),R.tail⟩ := by
    cases R with
    | nil => rfl
    | cons b R =>
      cases b
      · rfl
      · simp at hR
  have b := sweepL table 3 [] [] [false] [true] 1
    (by intro X Y; rfl) (n+4) (true::true::(Os p ++ V)) R.tail
  simp only [List.nil_append,Nat.one_mul] at b
  have c : run0 table 1 ⟨3,true::true::(Os p ++ V),Os (n+4) ++ R.tail⟩ =
      some ⟨4,Os (p+1) ++ V,false::(Os (n+4) ++ R.tail)⟩ := by rfl
  have d := sweepL table 4 [] [] [true] [false] 1
    (by intro X Y; rfl) (p+1) V (false::(Os (n+4) ++ R.tail))
  simp only [List.nil_append,Nat.one_mul] at d
  have H := join0 (join0 (join0 a b) c) d
  change run0 table (1+(n+4)+1+(p+1)) _ =
    some ⟨4,V,Zs (p+1) ++ false::(Os (n+4) ++ R.tail)⟩ at H
  rw [z_snoc] at H
  exact ⟨_,by omega,H⟩

theorem resume (p : Nat) (V : List Bool) (v : Runs)
    (hV : V=[] ∨ ∃ T,V=false::false::false::T ∧ Stack T) :
    ∃ L, L.headD false=false ∧ Stack L.tail ∧
      run0 table 4 ⟨4,V,Zs (2*p+2) ++ encode v⟩ =
        some (cfg L (.cons 0 p v)) := by
  rcases hV with rfl|⟨T,rfl,hT⟩
  · exact ⟨[],rfl,Stack.nil,rfl⟩
  · exact ⟨false::T,rfl,hT,rfl⟩

theorem reset_resume (n : Nat) (L R : List Bool) (hL : Stack L)
    (hR : R.headD false=false) (v : Runs)
    (he : Os (n+4) ++ R.tail = encode v) :
    ∃ t L' u', 0<t ∧ L'.headD false=false ∧ Stack L'.tail ∧
      run0 table t ⟨2,Zs (n+3) ++ true::true::L,R⟩ =
        some (cfg L' u') := by
  obtain ⟨p,V,h,hV⟩ := stack_split L hL
  subst L
  obtain ⟨t,ht,a⟩ := reset n (2*p) V R hR
  rw [he] at a
  obtain ⟨L',h0,hS,b⟩ := resume p V v hV
  exact ⟨t+4,L',.cons 0 p v,by omega,h0,hS,join0 a b⟩

theorem next (L : List Bool) (u : Runs)
    (h0 : L.headD false=false) (hS : Stack L.tail) :
    ∃ t L' u', 0<t ∧ L'.headD false=false ∧ Stack L'.tail ∧
      run0 table t (cfg L u) = some (cfg L' u') := by
  cases u with
  | last n =>
    have a := scan L n [] h0 rfl
    change run0 table (n+4) (cfg L (.last n)) =
      some ⟨2,Zs (n+3) ++ true::true::L.tail,[]⟩ at a
    obtain ⟨t,L',u',ht,h0',hS',b⟩ :=
      reset_resume n L.tail [] hS rfl (.last (n+3)) (by simp [List.tail])
    exact ⟨n+4+t,L',u',by omega,h0',hS',join0 a b⟩
  | cons k g u =>
    cases g with
    | zero =>
      have a := scan L (3*k) (false::encode u) h0 rfl
      change run0 table (3*k+4) (cfg L (.cons k 0 u)) =
        some ⟨2,Zs (3*k+3) ++ true::true::L.tail,encode u⟩ at a
      have b := carry (3*k) L.tail u
      exact ⟨3*k+4+6,false::(Zs (3*k) ++ true::true::L.tail),u,
        by omega,rfl,stack_zeros k _ (Stack.o _ hS),join0 a b⟩
    | succ g =>
      have a := scan L (3*k) (Zs (2*g+3) ++ encode u) h0 rfl
      change run0 table (3*k+4) (cfg L (.cons k (g+1) u)) =
        some ⟨2,Zs (3*k+3) ++ true::true::L.tail,Zs (2*g+2) ++ encode u⟩ at a
      obtain ⟨t,L',u',ht,h0',hS',b⟩ :=
        reset_resume (3*k) L.tail (Zs (2*g+2) ++ encode u) hS rfl
          (.cons (k+1) g u) rfl
      exact ⟨3*k+4+t,L',u',by omega,h0',hS',join0 a b⟩

theorem first : run0 table 11 ⟨0,[],[]⟩ =
    some (cfg [] (.cons 0 0 (.last 1))) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t L u, k≤t ∧ L.headD false=false ∧ Stack L.tail ∧
      run0 table t ⟨0,[],[]⟩ = some (cfg L u) := by
    intro k
    induction k with
    | zero => exact ⟨11,[],.cons 0 0 (.last 1),by omega,rfl,Stack.nil,first⟩
    | succ k ih =>
      obtain ⟨t,L,u,ht,h0,hS,a⟩ := ih
      obtain ⟨s,L',u',hs,h0',hS',b⟩ := next L u h0 hS
      exact ⟨t+s,L',u',by omega,h0',hS',join0 a b⟩
  intro n
  obtain ⟨t,L,u,ht,h0,hS,hr⟩ := arbitrary n
  have hz : (zrun table t start).map project = some (cfg L u) :=
    (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms never
end BB6.Agent8Raw54.RF55
