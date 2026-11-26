import Raw58LF1Sweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF1Sweep
open BB6Coverage Agent31Pump

-- Old completed 2-runs in the left accumulator contribute exactly three
-- left-sweep transitions and a returned 2-run each. A B1 hole does not sweep.
def old2 (n : Nat) : Result → Result
  | .back c w => .back (c+3*n) (List.replicate n 2 ++ w)
  | .hole c => .hole c

theorem old2_add (n c : Nat) (o : Result) : old2 n (o.add c) = (old2 n o).add c := by
  cases o <;> simp only [old2,Result.add]
  congr 1
  omega

theorem finishRuns_rep (k n : Nat) (w : List Nat) :
    finishRuns k (List.replicate n 1) w = List.replicate n 2 ++ ((k+1)::w) := by
  induction n generalizing k w with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change finishRuns 1 (List.replicate n 1) ((k+1)::w) = _
    rw [ih, List.replicate_succ']
    simp only [List.append_assoc,List.singleton_append]

theorem finishRuns_append_rep (k n : Nat) (ks w : List Nat) :
    finishRuns k (ks ++ List.replicate n 1) w = List.replicate n 2 ++ finishRuns k ks w := by
  induction ks generalizing k w with
  | nil => exact finishRuns_rep k n w
  | cons a as ih => exact ih a ((k+1)::w)

theorem finishCost_rep (k n : Nat) :
    finishCost k (List.replicate n 1) = finishCost k [] + 3*n := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ]
    change k+2 + finishCost 1 (List.replicate n 1) = _
    rw [ih]
    simp only [finishCost]
    omega

theorem finishCost_append_rep (k n : Nat) (ks : List Nat) :
    finishCost k (ks ++ List.replicate n 1) = finishCost k ks + 3*n := by
  induction ks generalizing k with
  | nil => exact finishCost_rep k n
  | cons a as ih =>
    change k+2+finishCost a (as ++ List.replicate n 1) = k+2+finishCost a as+3*n
    rw [ih]; omega

theorem finish00_old (k n : Nat) (ks w : List Nat) :
    finish00 k (ks ++ List.replicate n 1) w = old2 n (finish00 k ks w) := by
  unfold finish00 old2
  rw [show (k+1)::(ks ++ List.replicate n 1) = ((k+1)::ks) ++ List.replicate n 1 from rfl]
  rw [finishCost_append_rep,finishRuns_append_rep]
  congr 1
  omega

theorem finish0111_old (k n : Nat) (ks w : List Nat) :
    finish0111 k (ks ++ List.replicate n 1) w = old2 n (finish0111 k ks w) := by
  unfold finish0111 old2
  rw [show 0::(k+1)::(ks ++ List.replicate n 1) = (0::(k+1)::ks) ++ List.replicate n 1 from rfl]
  rw [finishCost_append_rep,finishRuns_append_rep]
  congr 1
  omega

theorem evalC_old (v : V) (k n : Nat) (ks : List Nat) (a : Nat) (w : List Nat) :
    evalC v k (ks ++ List.replicate n 1) a w = old2 n (evalC v k ks a w) := by
  match a,w with
  | 0,[] => simp only [evalC,finish00_old,old2_add]
  | 0,b::bs => simp only [evalC,evalC_old v (k+1) n ks b bs,old2_add]
  | 1,[] =>
    change (finish00 0 (((k+1)::ks) ++ List.replicate n 1) []).add (cost010 v) = _
    simp only [finish00_old,evalC,old2_add]
  | 1,0::[] =>
    change (finish00 0 ((0::(k+1)::ks) ++ List.replicate n 1) []).add 5 = _
    simp only [finish00_old,evalC,old2_add]
  | 1,0::0::bs => simp only [evalC,finish0111_old]
  | 1,0::1::bs => rfl
  | 1,0::(b+2)::bs =>
    change (evalC v 0 ((0::(k+1)::ks) ++ List.replicate n 1) b bs).add 5 = _
    simp only [evalC_old v 0 n (0::(k+1)::ks) b bs,evalC,old2_add]
  | 1,(b+1)::bs =>
    change (evalC v 0 (((k+1)::ks) ++ List.replicate n 1) b bs).add (cost010 v) = _
    simp only [evalC_old v 0 n ((k+1)::ks) b bs,evalC,old2_add]
  | a+2,bs => cases bs <;> simp only [evalC,finish00_old]
termination_by structural w

def liftPrefix (v : V) (n : Nat) (o : Result) : Result := (old2 n o).add (n*cost010 v)

theorem liftPrefix_one (v : V) (a : Nat) (w : List Nat) :
    evalSection v (2::(a+1)::w) = liftPrefix v 1 (evalSection v ((a+1)::w)) := by
  change ((evalC v 0 [1] a w).add (cost010 v)).add 2 = _
  have h := evalC_old v 0 1 [] a w
  change evalC v 0 [1] a w = _ at h
  rw [h]
  unfold liftPrefix
  change ((old2 1 (evalC v 0 [] a w)).add (cost010 v)).add 2 = (old2 1 ((evalC v 0 [] a w).add 2)).add (1*cost010 v)
  rw [old2_add]
  cases v <;> cases evalC _ 0 [] a w <;> simp only [Result.add,cost010,old2] <;> congr 1 <;> omega

theorem liftPrefix_succ (v : V) (n : Nat) (o : Result) :
    liftPrefix v 1 (liftPrefix v n o) = liftPrefix v (n+1) o := by
  cases v <;> cases o <;> simp [liftPrefix,old2,Result.add,cost010, List.replicate_succ]
  all_goals omega

theorem evalSection_prefix (v : V) (n a : Nat) (w : List Nat) :
    evalSection v (List.replicate n 2 ++ (a+1)::w) = liftPrefix v n (evalSection v ((a+1)::w)) := by
  induction n with
  | zero =>
    rw [List.replicate_zero,List.nil_append]
    cases evalSection v ((a+1)::w) <;> simp [liftPrefix,old2,Result.add]
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    have hs : evalSection v (2::(List.replicate n 2 ++ (a+1)::w)) =
        liftPrefix v 1 (evalSection v (List.replicate n 2 ++ (a+1)::w)) := by
      cases n with
      | zero => exact liftPrefix_one v a w
      | succ m => exact liftPrefix_one v 1 (List.replicate m 2 ++ (a+1)::w)
    rw [hs,ih,liftPrefix_succ]

#print axioms evalSection_prefix
end BB6Coverage.Agent4LF1Sweep
