import SweepPumping
namespace BB6Coverage.Agent3Raw120LACarry
open BB6Coverage Agent31Pump
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Pinned LA open leaf 855; the only undefined row is F0. -/
def table : PartialMachine
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,5⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,0⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,false,0⟩)
  | (4,true) => some (some ⟨true,false,4⟩)
  | (5,false) => none
  | (5,true) => some (some ⟨true,false,3⟩)

abbrev O (n : Nat) := rep [true] n
theorem ones_succ (n : Nat) : O (n+1) = true :: O n := rfl
theorem ones_add (n k : Nat) : O (n+k) = O n ++ O k := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega,ones_succ,ih,ones_succ]
    rfl

theorem rightPass (n : Nat) (L R : List Bool) (h : L.headD false = false) :
    run0 table (3*(n+2)) ⟨0,L,false::O (n+2)++R⟩ =
      some ⟨0,R.headD false::false::O (n+3)++L.tail,R.tail⟩ := by
  have a : run0 table 3 ⟨0,L,false::O (n+2)++R⟩ =
      some ⟨0,true::false::true::true::L.tail,O n++R⟩ := by
    cases L with
    | nil => rfl
    | cons b L =>
      cases b with
      | false => rfl
      | true => simp at h
  have b := sweepR table 0 [true,false] [] [true] [true] 3
    (by intro L R; rfl) n (true::true::L.tail) R
  have b' : run0 table (3*n) ⟨0,true::false::true::true::L.tail,O n++R⟩ =
      some ⟨0,true::false::(O n++true::true::L.tail),R⟩ := by
    simpa using b
  have c : run0 table 3 ⟨0,true::false::(O n++true::true::L.tail),R⟩ =
      some ⟨0,R.headD false::false::true::(O n++true::true::L.tail),R.tail⟩ := rfl
  have h' := join0 (join0 a b') c
  rw [show 3*(n+2)=3+3*n+3 by omega, h',show n+3=1+(n+2) by omega,ones_add 1,
      ones_add n 2]
  congr 2
  simp [List.append_assoc,rep]

theorem sweepE (n : Nat) (L R : List Bool) :
    run0 table n ⟨4,O n++L,R⟩ = some ⟨4,L,O n++R⟩ := by
  simpa using sweepL table 4 [] [] [true] [true] 1 (by intro L R; rfl) n L R

theorem exitE (L R : List Bool) (h : L.headD false = false) :
    run0 table 1 ⟨4,L,R⟩ = some ⟨0,L.tail,false::R⟩ := by
  cases L with
  | nil => rfl
  | cons b L =>
    cases b with
    | false => rfl
    | true => simp at h

theorem leftSplit (n : Nat) (L R : List Bool) (h : L.headD false = false) :
    run0 table (n+7) ⟨0,O (n+4)++L,R⟩ =
      some ⟨0,L.tail,false::O (n+2)++false::true::R⟩ := by
  have a : run0 table 4 ⟨0,O (n+4)++L,R⟩ =
      some ⟨4,O (n+2)++L,false::true::R⟩ := rfl
  have b := sweepE (n+2) L (false::true::R)
  have c := exitE L (O (n+2)++false::true::R) h
  rw [show n+7=4+(n+2)+1 by omega]
  exact join0 (join0 a b) c

theorem markBounce (n : Nat) (L R : List Bool) (h : L.headD false = false) :
    run0 table (n+8) ⟨0,false::false::O (n+1)++L,true::R⟩ =
      some ⟨0,L.tail,false::O (n+3)++false::R⟩ := by
  have a : run0 table 5 ⟨0,false::false::O (n+1)++L,true::R⟩ =
      some ⟨4,O (n+2)++L,true::false::R⟩ := rfl
  have b := sweepE (n+2) L (true::false::R)
  have c := exitE L (O (n+2)++true::false::R) h
  have h' := join0 (join0 a b) c
  rw [show n+8=5+(n+2)+1 by omega,h']
  rw [show n+3=(n+2)+1 by omega, ones_add (n+2) 1]
  congr 2
  simp [List.append_assoc,rep]

theorem extendRight (L : List Bool) :
    run0 table 10 ⟨0,false::false::L,[]⟩ = some ⟨0,L,false::O 4⟩ := rfl

abbrev Block := Nat × Bool

/-- A marked gap is 010, an unmarked gap 00; the terminal run has length four. -/
def enc : List Block → List Bool
  | [] => false::O 4
  | (n,b)::bs => false::O n++(if b then [false,true] else [false])++enc bs

def stack : List Nat → List Bool
  | [] => []
  | n::ns => false::O n++stack ns

def scanLeft : List Nat → List Bool
  | [] => []
  | n::ns => false::stack (n::ns)

theorem stackHead (xs : List Nat) : (stack xs).headD false = false := by
  cases xs <;> rfl
theorem scanHead (xs : List Nat) : (scanLeft xs).headD false = false := by
  cases xs <;> rfl
theorem scanTail (xs : List Nat) : (scanLeft xs).tail = stack xs := by
  cases xs <;> rfl

def Valid (bs : List Block) : Prop :=
  ∀ b ∈ bs, if b.2 then 3 ≤ b.1 else 4 ≤ b.1

def reset : List Nat → List Block → List Block
  | [], bs => bs
  | n::ns, bs => reset ns ((n-2,true)::bs)

theorem resetValid (xs : List Nat) (bs : List Block)
    (hx : ∀ n ∈ xs, 5 ≤ n) (hb : Valid bs) : Valid (reset xs bs) := by
  induction xs generalizing bs with
  | nil => exact hb
  | cons n ns ih =>
    apply ih
    · intro k hk
      exact hx k (by simp [hk])
    · intro b hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · have hn := hx n (by simp)
        simp
        omega
      · exact hb b hm

theorem leftSweep (xs : List Nat) (bs : List Block)
    (hx : ∀ n ∈ xs, 5 ≤ n) :
    ∃ t, run0 table t ⟨0,(stack xs).tail,enc bs⟩ =
      some ⟨0,[],enc (reset xs bs)⟩ := by
  induction xs generalizing bs with
  | nil => exact ⟨0,rfl⟩
  | cons n ns ih =>
    have hn := hx n (by simp)
    obtain ⟨k,hk⟩ := ih ((n-2,true)::bs) (by
      intro j hj
      exact hx j (by simp [hj]))
    have h := leftSplit (n-4) (stack ns) (enc bs) (stackHead ns)
    rw [show n-4+4=n by omega,show n-4+2=n-2 by omega] at h
    have h' : run0 table (n-4+7) ⟨0,(stack (n::ns)).tail,enc bs⟩ =
        some ⟨0,(stack ns).tail,enc ((n-2,true)::bs)⟩ := by
      simpa [stack,enc,List.append_assoc] using h
    exact ⟨_,join0 h' hk⟩

/-- Every legal configuration admits another positive-length phase.
    The proof recurses on the remaining blocks, not a bounded trace. -/
theorem advanceFrom (xs : List Nat) (bs : List Block)
    (hx : ∀ n ∈ xs, 5 ≤ n) (hb : Valid bs) :
    ∃ t out, 0 < t ∧ Valid out ∧
      run0 table t ⟨0,scanLeft xs,enc bs⟩ = some ⟨0,[],enc out⟩ := by
  induction bs generalizing xs with
  | nil =>
    have h := rightPass 2 (scanLeft xs) [] (scanHead xs)
    have h' : run0 table 12 ⟨0,scanLeft xs,enc []⟩ =
        some ⟨0,false::false::O 5++stack xs,[]⟩ := by
      simpa [enc,scanTail] using h
    have he := extendRight (O 5++stack xs)
    have he' : run0 table 10 ⟨0,false::false::O 5++stack xs,[]⟩ =
        some ⟨0,(stack (5::xs)).tail,enc []⟩ := he
    have hx' : ∀ n ∈ 5::xs, 5 ≤ n := by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · omega
      · exact hx n hn
    obtain ⟨k,hk⟩ := leftSweep (5::xs) [] hx'
    exact ⟨12+10+k,reset (5::xs) [],by omega,resetValid _ _ hx' hb,join0 (join0 h' he') hk⟩
  | cons b bs ih =>
    obtain ⟨n,mark⟩ := b
    have hn := hb (n,mark) (by simp)
    have hb' : Valid bs := by
      intro b hm
      exact hb b (by simp [hm])
    cases mark with
    | false =>
      simp at hn
      have h := rightPass (n-2) (scanLeft xs) (false::enc bs) (scanHead xs)
      rw [show n-2+2=n by omega,show n-2+3=n+1 by omega] at h
      have h' : run0 table (3*n) ⟨0,scanLeft xs,enc ((n,false)::bs)⟩ =
          some ⟨0,scanLeft ((n+1)::xs),enc bs⟩ := by
        rw [scanTail] at h
        simpa [enc,stack,scanLeft] using h
      have hx' : ∀ j ∈ (n+1)::xs, 5 ≤ j := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · exact hx j hj
      obtain ⟨t,out,ht,hout,hr⟩ := ih ((n+1)::xs) hx' hb'
      exact ⟨3*n+t,out,by omega,hout,join0 h' hr⟩
    | true =>
      simp at hn
      have h := rightPass (n-2) (scanLeft xs) (false::true::enc bs) (scanHead xs)
      rw [show n-2+2=n by omega,show n-2+3=n+1 by omega] at h
      have h' : run0 table (3*n) ⟨0,scanLeft xs,enc ((n,true)::bs)⟩ =
          some ⟨0,false::false::O (n+1)++stack xs,true::enc bs⟩ := by
        simpa [enc,scanTail] using h
      have hBounce := markBounce n (stack xs) (enc bs) (stackHead xs)
      have hBounce' : run0 table (n+8) ⟨0,false::false::O (n+1)++stack xs,true::enc bs⟩ =
          some ⟨0,(stack xs).tail,enc ((n+3,false)::bs)⟩ := by
        simpa [enc,List.append_assoc] using hBounce
      have hb'' : Valid ((n+3,false)::bs) := by
        intro b hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simp
          omega
        · exact hb' b hm
      obtain ⟨t,hr⟩ := leftSweep xs ((n+3,false)::bs) hx
      exact ⟨3*n+(n+8)+t,reset xs ((n+3,false)::bs),by omega,
        resetValid _ _ hx hb'',join0 (join0 h' hBounce') hr⟩

abbrev Good := {bs : List Block // Valid bs}
def cfg (x : Good) : Z0 := ⟨0,[],enc x.1⟩

theorem phaseStep (x : Good) :
    ∃ y : Nat × Good, 0 < y.1 ∧ run0 table y.1 (cfg x) = some (cfg y.2) := by
  obtain ⟨t,out,ht,hout,hr⟩ := advanceFrom [] x.1 (by simp) x.2
  exact ⟨(t,⟨out,hout⟩),ht,hr⟩

noncomputable def next (x : Good) : Nat × Good := Classical.choose (phaseStep x)
noncomputable def orbit : Nat → Good
  | 0 => ⟨[],by simp [Valid]⟩
  | n+1 => (next (orbit n)).2

theorem never : ∀ m, compatible table m → NeverHalts m :=
  never_of_growth table (fun k => cfg (orbit k)) 10
    (fun k => (next (orbit k)).1) (by rfl)
    (fun k => (Classical.choose_spec (phaseStep (orbit k))).1)
    (fun k => (Classical.choose_spec (phaseStep (orbit k))).2)

#print axioms advanceFrom
#print axioms never
end BB6Coverage.Agent3Raw120LACarry
