import P1R14Final
import P1R62Final
import P1R94Final
import P1R110Final
import P1R158Final
import P1R190Final
import P1R206Final
import P1R254Final
import P1R302Final
import P1R366Final
import P1R414Final
import P1R430Final
import P1R446Final
import P1R462Final
import P1R478Final
import P1R510Final
import P1R558Final
import P1R622Final
import P1R638Final
import P1R654Final
import P1R670Final
import P1R686Final
import P1R702Final
import P1R718Final
import P1R734Final
import P1R782Final
import P1R798Final
import P1R846Final
import P1R862Final
import P1R878Final
import P1R894Final
import P1R910Final
import P1R926Final
import P1R958Final
import P1R974Final
import P1R1006Final
import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace BB6.Agent47AllMod1024
def excludedResidues : List Nat := [14, 62, 94, 110, 158, 190, 206, 254, 302, 366, 414, 430, 446, 462, 478, 510, 558, 622, 638, 654, 670, 686, 702, 718, 734, 782, 798, 846, 862, 878, 894, 910, 926, 958, 974, 1006]
theorem blank_no_critical_closed_mod1024 (n : Nat)
    (h : n%1024 ∈ excludedResidues) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  simp only [excludedResidues, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h14 | h62 | h94 | h110 | h158 | h190 | h206 | h254 | h302 | h366 | h414 | h430 | h446 | h462 | h478 | h510 | h558 | h622 | h638 | h654 | h670 | h686 | h702 | h718 | h734 | h782 | h798 | h846 | h862 | h878 | h894 | h910 | h926 | h958 | h974 | h1006
  · have hn : n = 1024*(n/1024)+14 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R14.blank_no_critical_14_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+62 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R62.blank_no_critical_62_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+94 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R94.blank_no_critical_94_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+110 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R110.blank_no_critical_110_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+158 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R158.blank_no_critical_158_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+190 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R190.blank_no_critical_190_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+206 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R206.blank_no_critical_206_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+254 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R254.blank_no_critical_254_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+302 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R302.blank_no_critical_302_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+366 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R366.blank_no_critical_366_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+414 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R414.blank_no_critical_414_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+430 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R430.blank_no_critical_430_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+446 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R446.blank_no_critical_446_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+462 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R462.blank_no_critical_462_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+478 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R478.blank_no_critical_478_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+510 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R510.blank_no_critical_510_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+558 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R558.blank_no_critical_558_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+622 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R622.blank_no_critical_622_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+638 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R638.blank_no_critical_638_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+654 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R654.blank_no_critical_654_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+670 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R670.blank_no_critical_670_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+686 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R686.blank_no_critical_686_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+702 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R702.blank_no_critical_702_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+718 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R718.blank_no_critical_718_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+734 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R734.blank_no_critical_734_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+782 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R782.blank_no_critical_782_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+798 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R798.blank_no_critical_798_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+846 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R846.blank_no_critical_846_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+862 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R862.blank_no_critical_862_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+878 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R878.blank_no_critical_878_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+894 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R894.blank_no_critical_894_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+910 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R910.blank_no_critical_910_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+926 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R926.blank_no_critical_926_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+958 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R958.blank_no_critical_958_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+974 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R974.blank_no_critical_974_mod1024 (n/1024)
  · have hn : n = 1024*(n/1024)+1006 := by
      have hm := Nat.mod_add_div n 1024
      omega
    rw [hn]
    exact BB6.Agent47P1R1006.blank_no_critical_1006_mod1024 (n/1024)
#print axioms blank_no_critical_closed_mod1024
end BB6.Agent47AllMod1024
