import SourceSynthetic
import SourceCompleteGate

namespace Agent4ValuationBridge
open Agent9SourceSRun Agent9SProjection Agent4Synthetic
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB

theorem scalar_zero_rem (n k u : Nat) (hk : k<n) :
    (4^k*3^(n-k)*u)%3 = 0 := by
  have he : n-k=(n-k-1)+1 := by omega
  rw [he, Nat.pow_succ]
  simp [Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem scalar_zero_rem729 (n k u : Nat) (hk : k+6≤n) :
    (4^k*3^(n-k)*u)%729 = 0 := by
  have he : n-k=(n-k-6)+6 := by omega
  rw [he, Nat.pow_add]
  change (4^k*(3^(n-k-6)*729)*u)%729 = 0
  simp [Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem nonzero_val_prefix (b c n u δ : Nat)
    (hs : Sstep (b+16) c = some (3^n*u,c+δ))
    (hk : c+δ≤n) :
    scalarRun (c+δ+1) (some (b+16,c)) =
        some (4^(c+δ)*3^(n-(c+δ))*u,0) := by
  have hp := zero_prefix (c+δ) n 0 u hk
  rw [show c+δ+1=1+(c+δ) by omega,scalarRun_add]
  change scalarRun (c+δ) (Sstep (b+16) c) = _
  rw [hs]
  simpa using hp

theorem nonzero_val_transfer (b c n u δ : Nat)
    (hs : Sstep (b+16) c = some (3^n*u,c+δ))
    (hk : c+δ<n) :
    ∃ m, sourceRun (c+δ+2) (some (.S b c)) =
         some (.T m) := by
  have hlive := nonzero_val_prefix b c n u δ hs (by omega)
  have hrem := scalar_zero_rem n (c+δ) u hk
  have ht : scalarRun (c+δ+2) (some (b+16,c)) = none := by
    rw [show c+δ+2=(c+δ+1)+1 by omega]
    change (scalarRun (c+δ+1) (some (b+16,c))).bind
      (fun z => Sstep z.1 z.2) = none
    rw [hlive]
    simp [Sstep,hrem]
  obtain ⟨b',m,hq,hr,hs2⟩ := first_transfer_source
      (c+δ+1) b c (4^(c+δ)*3^(n-(c+δ))*u) 0
      hlive (by simpa [show c+δ+2=(c+δ+1)+1 by omega] using ht)
  exact ⟨m,by simpa [show c+δ+2=(c+δ+1)+1 by omega] using hs2⟩

theorem nonzero_val_immediate_halt (b c n u δ : Nat)
    (hs : Sstep (b+16) c = some (3^n*u,c+δ))
    (hk : c+δ+6≤n) :
    sourceRun (c+δ+3) (some (.S b c)) = none := by
  have hlive := nonzero_val_prefix b c n u δ hs (by omega)
  have hrem := scalar_zero_rem n (c+δ) u (by omega)
  have ht : scalarRun (c+δ+2) (some (b+16,c)) = none := by
    rw [show c+δ+2=(c+δ+1)+1 by omega]
    change (scalarRun (c+δ+1) (some (b+16,c))).bind
      (fun z => Sstep z.1 z.2) = none
    rw [hlive]
    simp [Sstep,hrem]
  have hm := scalar_zero_rem729 n (c+δ) u hk
  have hh := source_immediate_halt_after_transfer
    (c+δ+1) b c (4^(c+δ)*3^(n-(c+δ))*u) 0
    hlive (by simpa [show c+δ+2=(c+δ+1)+1 by omega] using ht) hm
  simpa [show c+δ+3=(c+δ+1)+2 by omega] using hh

#print axioms nonzero_val_prefix
#print axioms nonzero_val_transfer
#print axioms nonzero_val_immediate_halt
end Agent4ValuationBridge
