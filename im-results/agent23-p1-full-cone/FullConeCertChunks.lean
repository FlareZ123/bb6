import FullConeCertSource
namespace BB6.Agent23FullCone

def prefixSafe (P n Q j : Nat) (cs : List Nat) : Nat → Bool
  | 0 => true
  | k+1 => cs.all (safe P n j) && prefixSafe P n Q (j+1) (step Q j cs) k

theorem cert_append (P n Q j : Nat) (cs : List Nat) (a b : Nat) :
    cert P n Q j cs (a+b) =
    (prefixSafe P n Q j cs a && cert P n Q (j+a) (states Q j cs a) b) := by
  induction a generalizing j cs with
  | zero => simp [prefixSafe,states]
  | succ a ih =>
    rw [Nat.succ_add,cert,ih,prefixSafe,states]
    rw [show j+(a+1)=j+1+a by omega, Bool.and_assoc]

theorem cert_join (P n Q j : Nat) (cs ds : List Nat) (a b : Nat)
    (hs : prefixSafe P n Q j cs a = true)
    (he : states Q j cs a = ds)
    (ht : cert P n Q (j+a) ds b = true) : cert P n Q j cs (a+b) = true := by
  simp [cert_append,hs,he,ht]

end BB6.Agent23FullCone
