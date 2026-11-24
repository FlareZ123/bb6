import Q0BarrierChain

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Native-evaluated finite certificate; the generic coverage and source
    implication theorems use only the ordinary Lean axioms. -/
theorem native_chain_5_30 :
    (List.range 26).all (fun n => coeffs.all (fun a => barrierFast a (n+5)))=true := by
  native_decide

theorem native_chain_cert (a j : Nat) (ha : a∈coeffs) (hj : 5≤j) (hh : j≤30) :
    barrierFast a j=true := by
  have hm : j-5 ∈ List.range 26 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp native_chain_5_30 (j-5) hm
  have he : j-5+5=j := by omega
  rw [he] at h
  exact List.all_eq_true.mp h a ha

theorem q0_native_30 {Reach : Nat→Nat→Prop} (src : Source Reach)
    {u n x y : Nat} (hu : 1000000≤u) (hh : u≤upper 41 30)
    (hn : n=23+32*u) (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) :
    ¬ Reach x y := by
  exact q0_chain src (k:=30) (by decide) hu hh native_chain_cert hn hx hy

#eval upper 41 30
#print axioms native_chain_5_30
#print axioms q0_native_30
end BB429Q0Macro.RankBarrier
