import F418NormalReturn
import F418PzeroGate

namespace BB6.Agent32F418.PzeroBlock
open EventSystem EventSystem.State Arithmetic ReturnBounds

def atPure (N W : Nat) : State := shift2 N 1 (2^W) (W+1)

theorem atPure_safe {N W : Nat} (hN : 0<N) (hw : N<2^W) : Safe (atPure N W) := by
  simp only [atPure,Safe,RightWidth,gap,Nat.add_sub_cancel,Nat.pow_succ 2 W]
  have hp := Nat.two_pow_pos W
  exact ⟨hN,by decide,⟨by omega,by omega,by omega⟩,hw,by omega⟩

theorem pzero_step (M W : Nat) (hM : 7<M) (heven : M%2=0)
    (hs : Safe (atPure (M-7) W)) :
    iterate 2 (atPure (M-7) W) = some (atPure (M/2+2^(W+2)-7) (W+3)) := by
  have hw : M-7<2^W := hs.2.2.2.1
  let Q := (M-7)/2
  have he : (Prefix.last 0).value Q=M-7 := by simp [Prefix.value,Q]; omega
  have h := Prefix.normal_return_exact (Prefix.last 0) Q W (by rw [he]; exact hw)
  rw [he] at h
  simp only [Prefix.steps,Prefix.E_last,Prefix.next,Prefix.C] at h
  have hn : 2^(W+2)+Q-3=M/2+2^(W+2)-7 := by dsimp [Q]; omega
  rw [hn] at h
  simpa [atPure,Nat.add_assoc] using h

theorem replay_source (u l W j : Nat) (hj : j≤l) (hl : l≤W)
    (hs : Safe (atPure (2^l*u-7) W)) :
    iterate (2*j) (atPure (2^l*u-7) W) =
      some (atPure (replay (2^l*u) W j-7) (W+3*j)) := by
  induction j with
  | zero => simp [iterate,replay]
  | succ j ih =>
    have h := ih (by omega)
    have hs' := safe_iterate hs h
    have he := replay_even u l W j (by omega) hl
    have hp : 0<replay (2^l*u) W j-7 := hs'.1
    have hstep := pzero_step (replay (2^l*u) W j) (W+3*j) (by omega) he hs'
    rw [show 2*(j+1)=2*j+2 by omega,iterate_add,h]
    simp only [Option.bind_some]
    rw [hstep,replay]
    simp only [Nat.mul_succ,Nat.add_assoc]

theorem prepared_fatal (v m l : Nat) (hm : 3≤m) (hl : 2≤l) :
    ∃ k, iterate k (atPure (preparedInput v m l) (l+2*m))=none := by
  have hs := atPure_safe (prepared_positive v m l hl) (prepared_width v m l hm)
  have h := replay_source (lowWord v m+7) l (l+2*m) l (by omega) (by omega)
    (by rw [←prepared_augmented]; simpa using hs)
  rw [←prepared_augmented] at h
  simp only [Nat.add_sub_cancel] at h
  rw [prepared_endpoint] at h
  have hs' := safe_iterate hs h
  have hc := prepared_family OddChain OddChain.last OddChain.more v m l hl
  obtain ⟨Q,n',w',ht,_⟩ := fatal_episode hc (by decide) hs'
  obtain ⟨k,hk⟩ := reaches_iff.mp ht
  refine ⟨2*l+k+1,?_⟩
  rw [iterate_add,iterate_add,h]
  simp [atPure,hk,iterate,advance]

/-- A block of at least two p=0 returns cannot have a recoverable odd-only endpoint. -/
theorem gate_after_block_fatal (N W u l : Nat) (hW : 3≤W) (hl : 2≤l)
    (hu : u%2=1) (hM : N+7=2^l*u) (hN : 0<N) (hwidth : N<2^W)
    (hg : NoEven (replay (N+7) W l-7)) :
    ∃ k, iterate k (atPure N W)=none := by
  have hlw := block_length_bound hW hwidth hu hM
  have he : 2^l*u-7=N := by omega
  have hs := atPure_safe hN hwidth
  have h := replay_source u l W l (by omega) hlw (by rw [he]; exact hs)
  rw [he,←hM] at h
  have hs' := safe_iterate hs h
  have hc := terminal_oddchain OddChain OddChain.last OddChain.more hl hlw hW hu
    (by rw [he]; exact hwidth) (by rw [←hM]; exact hg)
  rw [←hM] at hc
  obtain ⟨Q,n',w',ht,_⟩ := fatal_episode hc (by decide) hs'
  obtain ⟨k,hk⟩ := reaches_iff.mp ht
  refine ⟨2*l+k+1,?_⟩
  rw [iterate_add,iterate_add,h]
  simp [atPure,hk,iterate,advance]

#print axioms gate_after_block_fatal
#print axioms replay_source
#print axioms prepared_fatal
end BB6.Agent32F418.PzeroBlock
