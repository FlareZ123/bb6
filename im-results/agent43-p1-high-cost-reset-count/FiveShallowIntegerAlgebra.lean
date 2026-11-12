import Lean

namespace BB6.Agent43FiveShallow

/-- Expand the five-shallow source equation into the first shallow remainder. -/
theorem algebraic_first_five
  (p P q d T1 C1 C2 C3 C4 C5 L1 O1
   A1 A2 A3 A4 A5 R1 R2 R3 R4 R5 E K : Nat)
  (hPInt : (q:Int)*(p:Int)=(P:Int))
  (hDInt : (q:Int)*(d:Int)=14*(T1:Int)-6)
  (hKInt :
    (K:Int)+98 =
      (C1:Int)*(q:Int)+(C2:Int)*(q:Int)*(A1:Int)+
      (C3:Int)*(q:Int)*(A1:Int)*(A2:Int)+
      (C4:Int)*(q:Int)*(A1:Int)*(A2:Int)*(A3:Int)+
      (C5:Int)*(q:Int)*(A1:Int)*(A2:Int)*(A3:Int)*(A4:Int))
  (hR1Int : (R1:Int)+(O1:Int)+(d:Int)=(L1:Int)*(T1:Int))
  (hEqInt :
    (K:Int)*(p:Int) =
      (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((A5:Int)*(E:Int))+
        (A4:Int)*(R5:Int))+(R4:Int))+(R3:Int))+(R2:Int))+(R1:Int)) :
  (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(T1:Int)-(O1:Int) =
    (A1:Int)*((C2:Int)*(P:Int))-(A1:Int)*(R2:Int)+
    (A1:Int)*((A2:Int)*((C3:Int)*(P:Int)))-(A1:Int)*((A2:Int)*(R3:Int))+
    (A1:Int)*((A2:Int)*((A3:Int)*((C4:Int)*(P:Int))))-
      (A1:Int)*((A2:Int)*((A3:Int)*(R4:Int)))+
    (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((C5:Int)*(P:Int)))))-
      (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*(R5:Int))))-
      (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((A5:Int)*(E:Int)))) := by
  have hKExpanded :
      (K:Int)*(p:Int)+98*(p:Int) =
        (C1:Int)*(P:Int)+(A1:Int)*((C2:Int)*(P:Int))+
        (A1:Int)*((A2:Int)*((C3:Int)*(P:Int)))+
        (A1:Int)*((A2:Int)*((A3:Int)*((C4:Int)*(P:Int))))+
        (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((C5:Int)*(P:Int))))) := by
    calc
      (K:Int)*(p:Int)+98*(p:Int)=((K:Int)+98)*(p:Int) := by omega
      _=((C1:Int)*(q:Int)+(C2:Int)*(q:Int)*(A1:Int)+
          (C3:Int)*(q:Int)*(A1:Int)*(A2:Int)+
          (C4:Int)*(q:Int)*(A1:Int)*(A2:Int)*(A3:Int)+
          (C5:Int)*(q:Int)*(A1:Int)*(A2:Int)*(A3:Int)*(A4:Int))*(p:Int) := by
        rw [hKInt]
      _=(C1:Int)*(P:Int)+(A1:Int)*((C2:Int)*(P:Int))+
          (A1:Int)*((A2:Int)*((C3:Int)*(P:Int)))+
          (A1:Int)*((A2:Int)*((A3:Int)*((C4:Int)*(P:Int))))+
          (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((C5:Int)*(P:Int))))) := by
        rw [←hPInt]
        simp only [Int.add_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
  have hEqExpanded :
      (K:Int)*(p:Int) =
        (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((A5:Int)*(E:Int))+
          (A4:Int)*(R5:Int))+(R4:Int))+(R3:Int))+(R2:Int))+(R1:Int) := by
    rw [hEqInt]
    simp only [Int.mul_add,Int.add_assoc]
  have htarget :
      (98:Int)*(p:Int)-(C1:Int)*(P:Int)+(R1:Int) =
        (A1:Int)*((C2:Int)*(P:Int))-(A1:Int)*(R2:Int)+
        (A1:Int)*((A2:Int)*((C3:Int)*(P:Int)))-(A1:Int)*((A2:Int)*(R3:Int))+
        (A1:Int)*((A2:Int)*((A3:Int)*((C4:Int)*(P:Int))))-
          (A1:Int)*((A2:Int)*((A3:Int)*(R4:Int)))+
        (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((C5:Int)*(P:Int)))))-
          (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*(R5:Int))))-
          (A1:Int)*((A2:Int)*((A3:Int)*((A4:Int)*((A5:Int)*(E:Int)))) := by
    simp only [Int.mul_add,Int.mul_sub]
    omega
  rw [htarget]
  rw [←hR1Int]
  omega

#print axioms algebraic_first_five

end BB6.Agent43FiveShallow
