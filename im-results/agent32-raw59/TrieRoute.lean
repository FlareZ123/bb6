import AsymNGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32TrieRoute
open BB6Coverage BB6.Agent1NGram

/-- Descend a zero-padded low-bit trie by one bit. A leaf represents {0}. -/
def child (t : Trie) (b : Bool) : Trie :=
  match t,b with
  | .empty,_ => .empty
  | .leaf,false => .leaf
  | .leaf,true => .empty
  | .branch e _,false => e
  | .branch _ o,true => o

theorem child_has (t : Trie) (b : Bool) (i : Nat) :
    (child t b).has i = t.has (2*i+b.toNat) := by
  cases t <;> cases b <;> simp [child,Trie.has,Bool.toNat]
  · cases i <;> simp
  · congr 1; omega

/-- Consume exactly n low bits. -/
def descend (t : Trie) : Nat → Nat → Trie
  | 0,_ => t
  | n+1,i => descend (child t (head i)) n (i/2)

theorem head_decomp (v : Nat) : (head v).toNat = v%2 := by
  unfold head
  have h : v%2=0 ∨ v%2=1 := by omega
  rcases h with h|h <;> simp [h]

theorem descend_has (t : Trie) (n v k : Nat) (hv : v < 2^n) :
    (descend t n v).has k = t.has (v + 2^n*k) := by
  induction n generalizing t v with
  | zero =>
    have hz : v = 0 := by omega
    subst v
    simp [descend]
  | succ n ih =>
    have hv' : v/2 < 2^n := by rw [Nat.pow_succ] at hv; omega
    rw [descend,ih _ _ hv',child_has,head_decomp,Nat.pow_succ]
    congr 1
    rw [Nat.mul_comm (2^n) 2,Nat.mul_assoc]
    omega

/-- Traverse source bits, optionally copying them into each of two other
    tries. Empty source cylinders are discharged immediately. -/
def scan (copyF copyT : Bool) (k : Trie → Trie → Trie → Bool) :
    Nat → Trie → Trie → Trie → Bool
  | 0,s,f,t => k s f t
  | n+1,s,f,t =>
    match s with
    | .empty => true
    | _ =>
      scan copyF copyT k n (child s false) (if copyF then child f false else f)
          (if copyT then child t false else t) &&
      scan copyF copyT k n (child s true) (if copyF then child f true else f)
          (if copyT then child t true else t)

theorem scan_sound (copyF copyT : Bool) (k : Trie → Trie → Trie → Bool)
    (n : Nat) (s f t : Trie) (v tail : Nat) (hv : v < 2^n)
    (hs : s.has (v+2^n*tail) = true)
    (hc : scan copyF copyT k n s f t = true) :
    k (descend s n v) (if copyF then descend f n v else f)
      (if copyT then descend t n v else t) = true := by
  induction n generalizing s f t v with
  | zero => simpa [scan,descend] using hc
  | succ n ih =>
    have hv' : v/2 < 2^n := by rw [Nat.pow_succ] at hv; omega
    have heq : 2*(v/2+2^n*tail)+(head v).toNat = v+2^(n+1)*tail := by
      rw [head_decomp,Nat.pow_succ,Nat.mul_comm (2^n) 2,Nat.mul_assoc]; omega
    have hs' : (child s (head v)).has (v/2+2^n*tail) = true := by rw [child_has,heq]; exact hs
    have hc' : scan copyF copyT k n (child s (head v))
        (if copyF then child f (head v) else f)
        (if copyT then child t (head v) else t) = true := by
      cases s with
      | empty => simp [Trie.has] at hs
      | leaf =>
        simp only [scan,Bool.and_eq_true] at hc
        cases h : head v
        · exact hc.1
        · exact hc.2
      | branch e o =>
        simp only [scan,Bool.and_eq_true] at hc
        cases h : head v
        · exact hc.1
        · exact hc.2
    have H := ih _ _ _ _ hv' hs' hc'
    cases copyF <;> cases copyT <;> simpa only [descend,ite_true,ite_false,Bool.false_eq_true] using H

#print axioms child_has
#print axioms descend_has
#print axioms scan_sound
end BB6.Agent32TrieRoute

namespace BB6.Agent32TrieRoute
open BB6Coverage BB6.Agent1NGram BB6.Agent32AsymNGram

/-- Route a known input segment and retain the remaining source membership. -/
theorem scan_pass (cf ct : Bool) (k : Trie → Trie → Trie → Bool)
    (n : Nat) (s f t : Trie) (v rest : Nat) (hv : v < 2^n)
    (hs : s.has (v+2^n*rest) = true)
    (hc : scan cf ct k n s f t = true) :
    k (descend s n v) (if cf then descend f n v else f)
      (if ct then descend t n v else t) = true ∧
    (descend s n v).has rest = true := by
  exact ⟨scan_sound cf ct k n s f t v rest hv hs hc, (descend_has s n v rest hv).trans hs⟩

def finish (s f t : Trie) : Bool := !(s.has 0) || !(f.has 0) || t.has 0

theorem finish_sound {s f t : Trie} (h : finish s f t = true)
    (hs : s.has 0 = true) (hf : f.has 0 = true) : t.has 0 = true := by
  simpa [finish,hs,hf] using h

theorem high_decomp (n x : Nat) (h : x < 2^(n+1)) :
    x%2^n + 2^n*(far n x).toNat = x := by
  have hp : 0 < 2^n := Nat.pow_pos (by decide)
  have hd : x/2^n < 2 := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa [Nat.pow_succ,Nat.mul_comm] using h
  have he : (far n x).toNat = x/2^n := by
    unfold far
    generalize hq : x/2^n = y at hd ⊢
    have hh : y = 0 ∨ y = 1 := by omega
    rcases hh with hh|hh <;> simp [hh]
  rw [he,Nat.mod_add_div]

theorem low_decomp (x : Nat) : 2*(x/2)+(head x).toNat = x := by
  rw [head_decomp]; omega

theorem half_lt (n x : Nat) (h : x < 2^(n+1)) : x/2 < 2^n := by
  rw [Nat.pow_succ] at h; omega

theorem lastBit_lt (b : Bool) : b.toNat < 2^1 := by cases b <;> decide

/-- Check rightward push edge by copying only left-window low bits, with
    the removed far bit fixed in advance and tested against the source. -/
def pushRight (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (w b : Bool) : Bool :=
  scan false false (fun s f t =>
    scan false true (fun s f t => finish (child s b) f t)
      c.nL s f t) (c.nR+1) s .leaf (child (child c.left b) w)

def pushLeft (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (w b : Bool) : Bool :=
  scan false true (fun s f t =>
    scan false false finish (c.nL+1) (child s b) f t)
    c.nR s .leaf (child (child c.right b) w)

/-- For a right step, copy the remaining right bits into the pop-edge and
    destination tries, insert extension/write bits, then copy left low bits. -/
def stepRight (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (q : Fin 6) (w a e : Bool) : Bool :=
  scan true true (fun s f t =>
    scan false true (fun s f t => scan false false finish 1 s f t)
      c.nL s f (child (child t e) w))
    c.nR (child s a) (child (child c.right e) a) (BB6.Agent32AsymNGram.row c q a)

def stepLeft (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (q : Fin 6) (w a e : Bool) : Bool :=
  scan false true (fun s f t =>
    scan false false (fun s f t =>
      scan true true (fun s f t => finish s f (child t e))
        c.nL (child s a) (child f a) t) 1 s f t)
    c.nR s (child c.left e) (child (BB6.Agent32AsymNGram.row c q a) w)

theorem pushRight_sound (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (w : Bool)
    (l r : Nat) (hl : l < 2^(c.nL+1)) (hr : r < 2^(c.nR+1))
    (hs : s.has (r+2^(c.nR+1)*l) = true)
    (hc : pushRight c s w (far c.nL l) = true) :
    BB6.Agent32AsymNGram.edgeOK c.left (push c.nL w l) (far c.nL l) = true := by
  let b := far c.nL l
  let lo := l%2^c.nL
  have hlo : lo < 2^c.nL := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hlx : lo+2^c.nL*b.toNat=l := high_decomp _ _ hl
  unfold pushRight at hc
  have h1 := scan_pass false false _ (c.nR+1) s .leaf (child (child c.left b) w) r l hr hs hc
  simp only [Bool.false_eq_true,ite_false] at h1
  have hs1 : (descend s (c.nR+1) r).has (lo+2^c.nL*b.toNat) = true := hlx ▸ h1.2
  have h2 := scan_pass false true _ c.nL (descend s (c.nR+1) r) .leaf
    (child (child c.left b) w) lo b.toNat hlo hs1 h1.1
  simp only [Bool.false_eq_true,ite_false,ite_true] at h2
  have hs2 : (child (descend (descend s (c.nR+1) r) c.nL lo) b).has 0 = true := by
    rw [child_has]; simpa using h2.2
  have h3 := finish_sound h2.1 hs2 (by decide : Trie.leaf.has 0 = true)
  rw [descend_has _ _ _ _ hlo,child_has,child_has] at h3
  simpa [BB6.Agent32AsymNGram.edgeOK,push,b,lo,Nat.add_comm] using h3

theorem pushLeft_sound (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (w : Bool)
    (l r : Nat) (hl : l < 2^(c.nL+1)) (hr : r < 2^(c.nR+1))
    (hs : s.has (r+2^(c.nR+1)*l) = true)
    (hc : pushLeft c s w (far c.nR r) = true) :
    BB6.Agent32AsymNGram.edgeOK c.right (push c.nR w r) (far c.nR r) = true := by
  let b := far c.nR r
  let lo := r%2^c.nR
  have hlo : lo < 2^c.nR := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hrx : lo+2^c.nR*b.toNat=r := high_decomp _ _ hr
  have hsplit : lo+2^c.nR*(2*l+b.toNat) = r+2^(c.nR+1)*l := by
    rw [Nat.mul_add,← Nat.mul_assoc,Nat.pow_succ,← hrx]
    omega
  have hs0 : s.has (lo+2^c.nR*(2*l+b.toNat)) = true := hsplit ▸ hs
  unfold pushLeft at hc
  have h1 := scan_pass false true _ c.nR s .leaf (child (child c.right b) w)
    lo (2*l+b.toNat) hlo hs0 hc
  simp only [Bool.false_eq_true,ite_false,ite_true] at h1
  have hs1 : (child (descend s c.nR lo) b).has (l+2^(c.nL+1)*0) = true := by
    rw [child_has]; simpa using h1.2
  have h2 := scan_pass false false _ (c.nL+1) (child (descend s c.nR lo) b) .leaf
    (descend (child (child c.right b) w) c.nR lo) l 0 hl hs1 h1.1
  simp only [Bool.false_eq_true,ite_false] at h2
  have h3 := finish_sound h2.1 h2.2 (by decide : Trie.leaf.has 0 = true)
  rw [descend_has _ _ _ _ hlo,child_has,child_has] at h3
  simpa [BB6.Agent32AsymNGram.edgeOK,push,b,lo,Nat.add_comm] using h3

#print axioms pushRight_sound
#print axioms pushLeft_sound
end BB6.Agent32TrieRoute

namespace BB6.Agent32TrieRoute
open BB6Coverage BB6.Agent1NGram BB6.Agent32AsymNGram

theorem stepRight_sound (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (q : Fin 6)
    (w e : Bool) (l r : Nat) (hl : l < 2^(c.nL+1)) (hr : r < 2^(c.nR+1))
    (hs : s.has (r+2^(c.nR+1)*l) = true)
    (he : BB6.Agent32AsymNGram.edgeOK c.right r e = true)
    (hc : stepRight c s q w (head r) e = true) :
    BB6.Agent32AsymNGram.stateOK c q (head r) (push c.nL w l) (pop c.nR r e) = true := by
  let a := head r
  let R := r/2
  let lo := l%2^c.nL
  let b := far c.nL l
  have hR : R < 2^c.nR := half_lt _ _ hr
  have hlo : lo < 2^c.nL := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hlx : lo+2^c.nL*b.toNat=l := high_decomp _ _ hl
  have hrx : 2*R+a.toNat=r := low_decomp r
  have hsrc : (child s a).has (R+2^c.nR*l) = true := by
    rw [child_has,Nat.mul_add,Nat.pow_succ] at *
    have hmul : (2^c.nR*2)*l = 2*(2^c.nR*l) := by ac_rfl
    rw [hmul] at hs
    have eq : 2*R+2*(2^c.nR*l)+a.toNat = r+2*(2^c.nR*l) := by omega
    rwa [eq]
  unfold stepRight at hc
  have h1 := scan_pass true true _ c.nR (child s a) (child (child c.right e) a)
    (BB6.Agent32AsymNGram.row c q a) R l hR hsrc hc
  simp only [ite_true] at h1
  have hf1 : (descend (child (child c.right e) a) c.nR R).has 0 = true := by
    rw [descend_has _ _ _ _ hR,child_has,child_has]
    simp only [Nat.mul_zero,Nat.add_zero]
    rw [hrx]
    exact he
  have hs1 : (descend (child s a) c.nR R).has (lo+2^c.nL*b.toNat) = true := hlx ▸ h1.2
  have h2 := scan_pass false true _ c.nL (descend (child s a) c.nR R)
    (descend (child (child c.right e) a) c.nR R)
    (child (child (descend (BB6.Agent32AsymNGram.row c q a) c.nR R) e) w)
    lo b.toNat hlo hs1 h1.1
  simp only [Bool.false_eq_true,ite_false,ite_true] at h2
  have hs2 : (descend (descend (child s a) c.nR R) c.nL lo).has (b.toNat+2^1*0) = true := by simpa using h2.2
  have h3 := scan_pass false false _ 1 _ _ _ b.toNat 0 (lastBit_lt b) hs2 h2.1
  simp only [Bool.false_eq_true,ite_false] at h3
  have H := finish_sound h3.1 h3.2 hf1
  rw [descend_has _ _ _ _ hlo,child_has,child_has,descend_has _ _ _ _ hR] at H
  simp only [Nat.mul_zero,Nat.add_zero] at H
  unfold BB6.Agent32AsymNGram.stateOK pop push
  have eq : R+2^c.nR*(2*(2*lo+w.toNat)+e.toNat) =
      r/2 + 2^c.nR*e.toNat+2^(c.nR+1)*(w.toNat+2*(l%2^c.nL)) := by
    change R+2^c.nR*(2*(2*lo+w.toNat)+e.toNat) =
      R + 2^c.nR*e.toNat+2^(c.nR+1)*(w.toNat+2*lo)
    simp only [Nat.pow_succ,Nat.mul_add,Nat.mul_assoc]
    ac_rfl
  rw [← eq]
  exact H

theorem stepLeft_sound (c : BB6.Agent32AsymNGram.Cert) (s : Trie) (q : Fin 6)
    (w e : Bool) (l r : Nat) (hl : l < 2^(c.nL+1)) (hr : r < 2^(c.nR+1))
    (hs : s.has (r+2^(c.nR+1)*l) = true)
    (he : BB6.Agent32AsymNGram.edgeOK c.left l e = true)
    (hc : stepLeft c s q w (head l) e = true) :
    BB6.Agent32AsymNGram.stateOK c q (head l) (pop c.nL l e) (push c.nR w r) = true := by
  let a := head l
  let L := l/2
  let lo := r%2^c.nR
  let b := far c.nR r
  have hL : L < 2^c.nL := half_lt _ _ hl
  have hlo : lo < 2^c.nR := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hrx : lo+2^c.nR*b.toNat=r := high_decomp _ _ hr
  have hlx : 2*L+a.toNat=l := low_decomp l
  have hsplit : lo+2^c.nR*(2*l+b.toNat) = r+2^(c.nR+1)*l := by
    rw [Nat.mul_add,← Nat.mul_assoc,Nat.pow_succ,← hrx]
    omega
  have hs0 : s.has (lo+2^c.nR*(2*l+b.toNat)) = true := hsplit ▸ hs
  unfold stepLeft at hc
  have h1 := scan_pass false true _ c.nR s (child c.left e)
    (child (BB6.Agent32AsymNGram.row c q a) w) lo (2*l+b.toNat) hlo hs0 hc
  simp only [Bool.false_eq_true,ite_false,ite_true] at h1
  have hs1 : (descend s c.nR lo).has (b.toNat+2^1*l) = true := by
    simpa [Nat.add_comm] using h1.2
  have h2 := scan_pass false false _ 1 _ _ _ b.toNat l (lastBit_lt b) hs1 h1.1
  simp only [Bool.false_eq_true,ite_false] at h2
  have hs2 : (child (descend (descend s c.nR lo) 1 b.toNat) a).has (L+2^c.nL*0) = true := by
    rw [child_has]; simpa [hlx] using h2.2
  have h3 := scan_pass true true _ c.nL _ (child (child c.left e) a)
    (descend (child (BB6.Agent32AsymNGram.row c q a) w) c.nR lo) L 0 hL hs2 h2.1
  simp only [ite_true] at h3
  have hf3 : (descend (child (child c.left e) a) c.nL L).has 0 = true := by
    rw [descend_has _ _ _ _ hL,child_has,child_has]
    simp only [Nat.mul_zero,Nat.add_zero]
    rw [hlx]
    exact he
  have H := finish_sound h3.1 h3.2 hf3
  rw [child_has,descend_has _ _ _ _ hL,descend_has _ _ _ _ hlo,child_has] at H
  simp only [Nat.mul_zero,Nat.zero_add] at H
  unfold BB6.Agent32AsymNGram.stateOK pop push
  have eq : 2*(lo+2^c.nR*(L+2^c.nL*e.toNat))+w.toNat =
      w.toNat+2*(r%2^c.nR)+2^(c.nR+1)*(l/2+2^c.nL*e.toNat) := by
    change 2*(lo+2^c.nR*(L+2^c.nL*e.toNat))+w.toNat =
      w.toNat+2*lo+2^(c.nR+1)*(L+2^c.nL*e.toNat)
    simp only [Nat.pow_succ,Nat.mul_add,Nat.mul_assoc]
    ac_rfl
  rw [← eq]
  exact H

#print axioms stepRight_sound
#print axioms stepLeft_sound
end BB6.Agent32TrieRoute

namespace BB6.Agent32TrieRoute
open BB6Coverage BB6.Agent1NGram


def bounded (t : Trie) (n : Nat) : Bool :=
  match t with
  | .empty | .leaf => true
  | .branch e o => match n with
    | 0 => false
    | k+1 => bounded e k && bounded o k

theorem bounded_sound (t : Trie) (n i : Nat) (hb : bounded t n = true)
    (hi : t.has i = true) : i < 2^n := by
  induction t generalizing n i with
  | empty => simp [Trie.has] at hi
  | leaf =>
    simp only [Trie.has,beq_iff_eq] at hi
    subst i
    exact Nat.pow_pos (by decide)
  | branch e o he ho =>
    cases n with
    | zero => simp [bounded] at hb
    | succ n =>
      simp only [bounded,Bool.and_eq_true] at hb
      rw [Nat.pow_succ]
      by_cases h : i%2=0
      · have hh : e.has (i/2)=true := by simpa [Trie.has,h] using hi
        have H := he n (i/2) hb.1 hh
        omega
      · have hh : o.has (i/2)=true := by simpa [Trie.has,h] using hi
        have H := ho n (i/2) hb.2 hh
        omega

theorem all_complete (t : Trie) (f : Nat → Bool)
    (h : ∀ i, t.has i = true → f i = true) : t.all f = true := by
  induction t generalizing f with
  | empty => rfl
  | leaf => exact h 0 rfl
  | branch e o he ho =>
    simp only [Trie.all,Bool.and_eq_true]
    constructor
    · apply he
      intro i hi
      apply h
      simpa [child] using (child_has (.branch e o) false i).symm.trans hi
    · apply ho
      intro i hi
      apply h
      simpa [child] using (child_has (.branch e o) true i).symm.trans hi

def routeRow (p : PartialMachine) (c : BB6.Agent32AsymNGram.Cert) (q : Fin 6) (a : Bool) : Bool :=
  let s := BB6.Agent32AsymNGram.row c q a
  bounded s (c.nR+1+(c.nL+1)) &&
    match p (q,a) with
    | some (some mv) =>
      if mv.right then
        BB6.Agent32AsymNGram.bits.all (pushRight c s mv.write) &&
        BB6.Agent32AsymNGram.bits.all (fun b => BB6.Agent32AsymNGram.bits.all (stepRight c s mv.next mv.write b))
      else
        BB6.Agent32AsymNGram.bits.all (pushLeft c s mv.write) &&
        BB6.Agent32AsymNGram.bits.all (fun b => BB6.Agent32AsymNGram.bits.all (stepLeft c s mv.next mv.write b))
    | _ => s.all (fun _ => false)

theorem routeRow_sound (p : PartialMachine) (c : BB6.Agent32AsymNGram.Cert) (q : Fin 6) (a : Bool)
    (h : routeRow p c q a = true) : (BB6.Agent32AsymNGram.row c q a).all (fun i =>
      BB6.Agent32AsymNGram.stateStepOK p c q a (i/2^(c.nR+1)) (i%2^(c.nR+1))) = true := by
  apply all_complete
  intro i hi
  let l := i/2^(c.nR+1)
  let r := i%2^(c.nR+1)
  have hp : 0 < 2^(c.nR+1) := Nat.pow_pos (by decide)
  have hr : r < 2^(c.nR+1) := Nat.mod_lt _ hp
  have hkey : r + 2^(c.nR+1)*l = i := Nat.mod_add_div _ _
  unfold routeRow at h
  simp only [Bool.and_eq_true] at h
  have hi' := bounded_sound _ _ _ h.1 hi
  have hl : l < 2^(c.nL+1) := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    rw [Nat.mul_comm, ← Nat.pow_add]
    exact hi'
  have hs : (BB6.Agent32AsymNGram.row c q a).has (r+2^(c.nR+1)*l) = true := hkey ▸ hi
  change BB6.Agent32AsymNGram.stateStepOK p c q a l r = true
  cases ht : p (q,a) with
  | none =>
    have H : (BB6.Agent32AsymNGram.row c q a).all (fun _ => false) = true := by simpa [ht] using h.2
    have hh := Trie.all_sound H hi
    contradiction
  | some v => cases v with
    | none =>
      have H : (BB6.Agent32AsymNGram.row c q a).all (fun _ => false) = true := by simpa [ht] using h.2
      have hh := Trie.all_sound H hi
      contradiction
    | some mv =>
      cases hm : mv.right with
      | true =>
        have H := h.2
        simp only [ht,hm,ite_true,Bool.and_eq_true,List.all_eq_true] at H
        simp only [BB6.Agent32AsymNGram.stateStepOK,ht,hm,ite_true,Bool.and_eq_true,List.all_eq_true]
        refine ⟨pushRight_sound c _ _ l r hl hr hs (H.1 _ (BB6.Agent32AsymNGram.mem_bits _)),?_⟩
        intro e he
        cases he' : BB6.Agent32AsymNGram.edgeOK c.right r e with
        | false => simp [he']
        | true =>
          simp only [he',Bool.not_true,Bool.false_or]
          exact stepRight_sound c _ _ _ e l r hl hr hs he' (H.2 _ (BB6.Agent32AsymNGram.mem_bits _) e he)
      | false =>
        have H := h.2
        simp only [ht,hm,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true] at H
        simp only [BB6.Agent32AsymNGram.stateStepOK,ht,hm,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true]
        refine ⟨pushLeft_sound c _ _ l r hl hr hs (H.1 _ (BB6.Agent32AsymNGram.mem_bits _)),?_⟩
        intro e he
        cases he' : BB6.Agent32AsymNGram.edgeOK c.left l e with
        | false => simp [he']
        | true =>
          simp only [he',Bool.not_true,Bool.false_or]
          exact stepLeft_sound c _ _ _ e l r hl hr hs he' (H.2 _ (BB6.Agent32AsymNGram.mem_bits _) e he)

theorem route_check_of_rows {p : PartialMachine} {c : BB6.Agent32AsymNGram.Cert}
    (hL : BB6.Agent32AsymNGram.edgeOK c.left 0 false = true)
    (hR : BB6.Agent32AsymNGram.edgeOK c.right 0 false = true)
    (hS : BB6.Agent32AsymNGram.stateOK c 0 false 0 0 = true)
    (hrows : ∀ q a, routeRow p c q a = true) : BB6.Agent32AsymNGram.check p c = true :=
  BB6.Agent32AsymNGram.check_of_rows hL hR hS (fun q a => routeRow_sound p c q a (hrows q a))

#print axioms routeRow_sound
#print axioms route_check_of_rows
end BB6.Agent32TrieRoute
