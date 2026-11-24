import Std
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
namespace Odometer172

def bump : List Nat → List Nat
  | [] => [0]
  | a::q => (a+1)::q

def ret : Bool → List Bool → List Nat → List Nat
  | false, [], R => bump (bump R)
  | true, [], R => 3 :: bump R
  | false, false :: bs, R => ret true bs (bump R)
  | false, true :: bs, R => ret true bs (bump (bump R))
  | true, false :: bs, R => ret false bs (0 :: bump R)
  | true, [true], R => 1 :: 0 :: bump R
  | true, true :: false :: bs, R => ret true bs (0 :: 0 :: bump R)
  | true, true :: true :: bs, R => ret true bs (1 :: 0 :: bump R)

def bm (m : Bool) (bs : List Bool) := if m then true::false::bs else false::bs

def scan : Bool → List Bool → List Nat → Option (List Nat)
  | false, bs, [] => some (ret false bs [0])
  | true, bs, [] => some (ret true bs [0,0])
  | m, bs, r :: R =>
    let b := bm m bs
    if r = 0 then some (ret false b R)
    else if r = 1 then some (ret true b R)
    else if r = 2 then scan false (false :: b) R
    else if r = 3 then scan true b R
    else none

def F (m : Bool) (bs : List Bool) (q : List Nat) := ret true (bm m bs) q
def G (m : Bool) (bs : List Bool) (q : List Nat) := ret false (bm m bs) q

theorem f2 (m : Bool) (bs : List Bool) (q : List Nat) :
    F false (false::bm m bs) q = F m bs (1::bump q) := by
  simp [F,bm,ret,bump]
theorem f3 (m : Bool) (bs : List Bool) (q : List Nat) :
    F true (bm m bs) q = F m bs (0::0::bump q) := by
  simp [F,bm,ret,bump]
theorem g2 (m : Bool) (bs : List Bool) (q : List Nat) :
    G false (false::bm m bs) q = G m bs (0::bump (bump q)) := by
  simp [G,bm,ret,bump]
theorem g3 (m : Bool) (bs : List Bool) (q : List Nat) :
    G true (bm m bs) q = G m bs (0::bump (bump (bump q))) := by
  simp [G,bm,ret,bump]

theorem bump_nonempty (q : List Nat) : bump q ≠ [] := by cases q <;> simp [bump]
theorem bump_append (q t : List Nat) (hq : q ≠ []) : bump (q++t) = bump q ++ t := by
  cases q with
  | nil => contradiction
  | cons a r => rfl
theorem ret_append (m : Bool) (bs : List Bool) (q t : List Nat) (hq : q ≠ []) :
    ret m bs (q++t) = ret m bs q ++ t := by
  induction m, bs, q using ret.induct generalizing t with
  | case1 R => simp [ret,bump_append, hq,bump_nonempty]
  | case2 R => simp [ret,bump_append,hq]
  | case3 bs R ih => simpa [ret,bump_append,hq] using ih t (bump_nonempty R)
  | case4 bs R ih => simpa [ret,bump_append,hq,bump_nonempty] using ih t (bump_nonempty (bump R))
  | case5 bs R ih => simpa [ret,bump_append,hq] using ih t (by simp)
  | case6 R => simp [ret,bump_append,hq]
  | case7 bs R ih => simpa [ret,bump_append,hq] using ih t (by simp)
  | case8 bs R ih => simpa [ret,bump_append,hq] using ih t (by simp)

theorem end_eq (m : Bool) (bs : List Bool) :
    (if m then ret true bs [0,0] else ret false bs [0]) ++ [0] = F m bs [] := by
  cases m <;> simp [F,bm,ret,bump,← ret_append]

def highs : List Bool → List Nat
  | [] => []
  | d::p => (if d then 3 else 2) :: highs p
def phi : List Bool → List Nat
  | [] => []
  | d::p => (if d then [1,0] else [2]) ++ phi p
def pushF (d : Bool) (q : List Nat) : List Nat := if d then 0::0::bump q else 1::bump q
def pushG (d : Bool) (q : List Nat) : List Nat := if d then 0::bump (bump (bump q)) else 0::bump (bump q)

theorem scan_one_aux (p : List Bool) (m : Bool) (bs : List Bool) (q : List Nat) :
    scan m bs (highs p ++ 1::q) = some (F m bs (p.foldr pushF q)) := by
  induction p generalizing m bs with
  | nil => simp [highs,scan,F]
  | cons d p ih =>
    cases d <;> simp [highs,scan,ih,List.foldr_cons,pushF,f2,f3]

theorem scan_zero_aux (p : List Bool) (m : Bool) (bs : List Bool) (q : List Nat) :
    scan m bs (highs p ++ 0::q) = some (G m bs (p.foldr pushG q)) := by
  induction p generalizing m bs with
  | nil => simp [highs,scan,G]
  | cons d p ih =>
    cases d <;> simp [highs,scan,ih,List.foldr_cons,pushG,g2,g3]

theorem foldF_bump (p : List Bool) (q : List Nat) :
    bump (p.foldr pushF q) = phi p ++ bump q := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    cases d
    · change 2 :: bump (p.foldr pushF q) = 2 :: (phi p ++ bump q)
      rw [ih]
    · change 1 :: 0 :: bump (p.foldr pushF q) = 1 :: 0 :: (phi p ++ bump q)
      rw [ih]

theorem scan_one (p : List Bool) (q : List Nat) :
    scan false [] (highs p ++ 1::q) = some ([2] ++ phi p ++ bump q) := by
  rw [scan_one_aux]
  change some (2 :: bump (p.foldr pushF q)) = _
  rw [foldF_bump]
  rfl

theorem foldG_tail (p : List Bool) (q : List Nat) :
    p.foldr pushG (0::q) = 0 :: highs p ++ q := by
  induction p with
  | nil => rfl
  | cons d p ih => cases d <;> simp [pushG,bump,highs,ih]

theorem scan_zero_empty (q : List Nat) :
    scan false [] (0::q) = some (3::bump (bump q)) := by rfl

theorem scan_zero_nonempty (p : List Bool) (d : Bool) (q : List Nat) :
    scan false [] (highs (p++[d]) ++ 0::q) =
      some ([3,2] ++ highs p ++ (if d then bump (bump (bump q)) else bump (bump q))) := by
  rw [scan_zero_aux,List.foldr_append]
  cases d <;> simp [pushG,foldG_tail,G,bm,ret,bump]

theorem scan_end_aux (p : List Bool) (m : Bool) (bs : List Bool) :
    (scan m bs (highs p)).map (· ++ [0]) = scan m bs (highs p ++ [1]) := by
  induction p generalizing m bs with
  | nil => cases m <;> simp [highs,scan,bm,ret,bump,← ret_append]
  | cons d p ih => cases d <;> simp [highs,scan,ih]

theorem scan_end (p : List Bool) : scan false [] (highs p) = some ([2] ++ phi p) := by
  have h := scan_end_aux p false []
  rw [show ([1] : List Nat) = 1::[] by rfl,scan_one] at h
  cases he : scan false [] (highs p) with
  | none => simp [he] at h
  | some q =>
    simp [he,bump] at h
    exact congrArg some (List.append_cancel_right (bs := [0]) (by simpa [List.append_assoc] using h))

theorem scan_halt (p : List Bool) (d : Nat) (q : List Nat) (hd : 4 ≤ d) (m : Bool) (bs : List Bool) :
    scan m bs (highs p ++ d::q) = none := by
  induction p generalizing m bs with
  | nil => simp [highs,scan,show d ≠ 0 by omega,show d ≠ 1 by omega,show d ≠ 2 by omega,show d ≠ 3 by omega]
  | cons a p ih => cases a <;> simp [highs,scan,ih]

#print axioms scan_one
#print axioms scan_zero_empty
#print axioms scan_zero_nonempty
#print axioms scan_end
#print axioms scan_halt
end Odometer172
