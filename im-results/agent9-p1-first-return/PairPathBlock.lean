import PairSparse
namespace BB6.Agent9PairCarry
open BB6.Agent9BatchCarry

def pathPred (r a : Nat) : Option Nat :=
  let c := ((4*a)%(2*r+1))%r
  if 1≤c ∧ c+2≤r then some c else none

def pathBirthOK (skip : List Nat) (hi r a : Nat) : Bool :=
  skip.contains (2*r-4) || !(decide (2*r-4≤hi ∧ (r-1)%2=0) && decide (a=(r-1)/2))

/-- Check each endpoint's entire reverse trail, merging only at block boundaries. -/
def scanOne (skip : List Nat) (hi r a : Nat) : Nat → Bool × Option Nat
  | 0 => (pathBirthOK skip hi r a,some a)
  | j+1 =>
    let t := scanOne skip hi r a j
    match t.2 with
    | none => (t.1,none)
    | some b =>
      match pathPred (r-(j+1)) b with
      | none => (t.1,none)
      | some c => (t.1 && pathBirthOK skip hi (r-(j+1)) c,some c)

theorem scanOne_step (skip : List Nat) (hi r a j b c : Nat)
    (h : (scanOne skip hi r a j).2=some b)
    (hp : pathPred (r-(j+1)) b=some c) :
    (scanOne skip hi r a (j+1)).2=some c := by
  simp [scanOne,h,hp]

theorem scanOne_birth (skip : List Nat) (hi r a j c : Nat)
    (h : (scanOne skip hi r a j).2=some c)
    (hok : (scanOne skip hi r a j).1=true) :
    pathBirthOK skip hi (r-j) c=true := by
  cases j with
  | zero =>
    simp [scanOne] at h hok
    simpa [←h] using hok
  | succ j =>
    cases hb : (scanOne skip hi r a j).2 with
    | none => simp [scanOne,hb] at h
    | some b =>
      cases hp : pathPred (r-(j+1)) b with
      | none => simp [scanOne,hb,hp] at h
      | some p =>
        simp [scanOne,hb,hp] at h hok
        simpa [←h] using hok.2

theorem scanOne_ok_prev (skip : List Nat) (hi r a j : Nat)
    (h : (scanOne skip hi r a (j+1)).1=true) :
    (scanOne skip hi r a j).1=true := by
  cases hb : (scanOne skip hi r a j).2 with
  | none => simpa [scanOne,hb] using h
  | some b =>
    cases hp : pathPred (r-(j+1)) b with
    | none => simpa [scanOne,hb,hp] using h
    | some p =>
      simp [scanOne,hb,hp] at h
      exact h.1

theorem scanOne_ok_le (skip : List Nat) (hi r a d j : Nat)
    (hj : j≤d) (h : (scanOne skip hi r a d).1=true) :
    (scanOne skip hi r a j).1=true := by
  induction d with
  | zero =>
    have he : j=0 := by omega
    simpa [he] using h
  | succ d ih =>
    by_cases he : j=d+1
    · simpa [he] using h
    · exact ih (by omega) (scanOne_ok_prev skip hi r a d h)

theorem scanOne_cover (skip : List Nat) (hi r k j : Nat) (xs : List Nat)
    (hlo : j+2≤r)
    (hs : ∀ c z, Walk (2*r) c (2*k+1) z → c/2∈xs)
    (c z : Nat) (hw : Walk (2*(r-j)) c (2*(k+j)+1) z) :
    ∃ a∈xs, (scanOne skip hi r a j).2=some (c/2) := by
  induction j generalizing c z with
  | zero =>
    have h : Walk (2*r) c (2*k+1) z := by simpa using hw
    exact ⟨c/2,hs c z h,by simp [scanOne]⟩
  | succ j ih =>
    let t := r-(j+1)
    have h : Walk (2*t) c (2*(k+j)+3) z := by
      simpa [t,show 2*(k+(j+1))+1=2*(k+j)+3 by omega] using hw
    obtain ⟨hc,hc₀,hc₁⟩ := even_start t c (2*(k+j)+2) z (by simpa [Nat.add_assoc] using h)
    cases h with
    | cons _ _ w _ _ he tail =>
      cases tail with
      | cons _ _ b _ _ he' tail' =>
        have ht : Walk (2*(r-j)) b (2*(k+j)+1) z := by
          simpa [t,show 2*(r-(j+1))+1+1=2*(r-j) by omega] using tail'
        obtain ⟨hb,_,_⟩ := even_start (r-j) b (2*(k+j)) z ht
        have he₁ : Edge (2*t) (2*(c/2)) w := by rwa [←hc]
        have he₂ : Edge (2*t+1) w (2*(b/2)) := by rwa [←hb]
        have hp := pair_parent t (c/2) w (b/2) he₁ he₂
        obtain ⟨a,ha,hscan⟩ := ih (by omega) b z ht
        refine ⟨a,ha,scanOne_step skip hi r a j (b/2) (c/2) hscan ?_⟩
        change pathPred t (b/2)=some (c/2)
        simp [pathPred,hp,hc₀,hc₁]

def pathSort : Nat → List Nat → List Nat
  | 0,xs => xs
  | d+1,xs =>
    if xs.length≤1 then xs else
      unionSorted (pathSort d (xs.take (xs.length/2))) (pathSort d (xs.drop (xs.length/2)))

theorem pathSort_mem (d c : Nat) (xs : List Nat) :
    c∈pathSort d xs ↔ c∈xs := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih =>
    by_cases h : xs.length≤1
    · simp [pathSort,h]
    · simp only [pathSort,h,if_false,mem_unionSorted,ih]
      rw [←List.mem_append,List.take_append_drop]

def pairPathBlock (skip : List Nat) (hi r : Nat) (xs : List Nat) (d : Nat) :
    Bool × List Nat :=
  let ts := xs.map (fun a => scanOne skip hi r a d)
  (ts.all Prod.fst,pathSort (Nat.log2 xs.length+1) (ts.filterMap Prod.snd))

theorem pairPathBlock_sound (skip : List Nat) (hi r d k : Nat) (xs out : List Nat)
    (hlo : d+2≤r)
    (hs : ∀ c z, Walk (2*r) c (2*k+1) z → c/2∈xs)
    (hcheck : pairPathBlock skip hi r xs d=(true,out)) :
    (∀ c z, Walk (2*(r-d)) c (2*(k+d)+1) z → c/2∈out) ∧
    (∀ n, 2*(r-d)≤n+4 → n+4≤2*r → n%2=0 → n≤hi → n∉skip →
      ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*r+2*k+1-(n+4)) z) := by
  have hgood : ∀ a∈xs, (scanOne skip hi r a d).1=true := by
    intro a ha
    have h : (xs.map (fun a => scanOne skip hi r a d)).all Prod.fst=true := by
      simpa [pairPathBlock] using congrArg Prod.fst hcheck
    exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hout : out=pathSort (Nat.log2 xs.length+1)
      ((xs.map (fun a => scanOne skip hi r a d)).filterMap Prod.snd) := by
    simpa [pairPathBlock] using (congrArg Prod.snd hcheck).symm
  refine ⟨?_,?_⟩
  · intro c z hw
    obtain ⟨a,ha,hscan⟩ := scanOne_cover skip hi r k d xs hlo hs c z hw
    rw [hout,pathSort_mem]
    exact List.mem_filterMap.mpr ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,hscan⟩
  · intro n hn₀ hn₁ he hnhi hn
    rintro ⟨z,hw⟩
    let j := r-(n+4)/2
    have hj : j≤d := by dsimp [j]; omega
    have hclock : 2*(r-j)=n+4 := by dsimp [j]; omega
    have hlen : 2*(k+j)+1=2*r+2*k+1-(n+4) := by omega
    have hw' : Walk (2*(r-j)) ((n+2)/2) (2*(k+j)+1) z := by rwa [hclock,hlen]
    obtain ⟨a,ha,hscan⟩ := scanOne_cover skip hi r k j xs (by omega) hs _ z hw'
    have hok := scanOne_ok_le skip hi r a d j hj (hgood a ha)
    have hb := scanOne_birth skip hi r a j (((n+2)/2)/2) hscan hok
    have hcenter : (n+2)/2=r-j-1 := by omega
    have heven := (even_start (r-j) ((n+2)/2) (2*(k+j)) z hw').1
    have hpar : (r-j-1)%2=0 := by omega
    have hn' : 2*(r-j)-4=n := by omega
    simp [pathBirthOK,hn',hnhi,hn,hcenter,hpar] at hb

theorem pairPathBlock_extend (skip : List Nat) (R hi r d : Nat) (xs out : List Nat)
    (hr : r≤R) (hlo : d+2≤r)
    (cert : PairSparseCertificate skip R hi r xs)
    (hcheck : pairPathBlock skip hi r xs d=(true,out)) :
    PairSparseCertificate skip R hi (r-d) out := by
  obtain ⟨hnew,hex⟩ := pairPathBlock_sound skip hi r d (R-r) xs out hlo cert.cover hcheck
  have hsum : 2*r+2*(R-r)+1=2*R+1 := by omega
  refine ⟨?_,?_⟩
  · simpa [show R-(r-d)=R-r+d by omega] using hnew
  · intro n hn₀ hn₁ he hnhi hn
    by_cases h : n+4≤2*r
    · simpa [hsum] using hex n hn₀ h he hnhi hn
    · exact cert.excluded n (by omega) hn₁ he hnhi hn

#print axioms scanOne_cover
#print axioms pairPathBlock_sound
#print axioms pairPathBlock_extend
end BB6.Agent9PairCarry
