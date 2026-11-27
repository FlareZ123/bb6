import Raw36FirstCounters
import Raw36FirstOverflowBank

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstAlign
open BB6Coverage Agent31Pump Auto Raw36FirstCounters

def p : PartialMachine := Raw36FirstOverflowA2.p

theorem in_A0 (n : Nat) :
    Raw36FirstOverflowA0.source.eval n = A (2*n+5) 0 := by
  rw [A_special n 5 0 (by omega)]
  simp [Raw36FirstOverflowA0.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A0 (n : Nat) :
    Raw36FirstOverflowA0.target.eval n = B 17 (2*n+1) := by
  rw [B_target n 17 1]
  simp [Raw36FirstOverflowA0.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A0 (n : Nat) :
    run0 p (36*n+912) (A (2*n+5) 0) =
    some (B 17 (2*n+1)) := by
  rw [← in_A0 n,← out_A0 n]
  exact Raw36FirstOverflowA0.transport n

theorem in_A1 (n : Nat) :
    Raw36FirstOverflowA1.source.eval n = A (2*n+1) 1 := by
  rw [A_special n 1 1 (by omega)]
  simp [Raw36FirstOverflowA1.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A1 (n : Nat) :
    Raw36FirstOverflowA1.target.eval n = B 15 (2*n+0) := by
  rw [B_target n 15 0]
  simp [Raw36FirstOverflowA1.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A1 (n : Nat) :
    run0 p (54*n+768) (A (2*n+1) 1) =
    some (B 15 (2*n+0)) := by
  rw [← in_A1 n,← out_A1 n]
  exact Raw36FirstOverflowA1.transport n

theorem in_A2 (n : Nat) :
    Raw36FirstOverflowA2.source.eval n = A (2*n+1) 2 := by
  rw [A_special n 1 2 (by omega)]
  simp [Raw36FirstOverflowA2.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A2 (n : Nat) :
    Raw36FirstOverflowA2.target.eval n = B 13 (2*n+3) := by
  rw [B_target n 13 3]
  simp [Raw36FirstOverflowA2.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A2 (n : Nat) :
    run0 p (72*n+732) (A (2*n+1) 2) =
    some (B 13 (2*n+3)) := by
  rw [← in_A2 n,← out_A2 n]
  exact Raw36FirstOverflowA2.transport n

theorem in_A3 (n : Nat) :
    Raw36FirstOverflowA3.source.eval n = A (2*n+1) 3 := by
  rw [A_special n 1 3 (by omega)]
  simp [Raw36FirstOverflowA3.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A3 (n : Nat) :
    Raw36FirstOverflowA3.target.eval n = B 11 (2*n+6) := by
  rw [B_target n 11 6]
  simp [Raw36FirstOverflowA3.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A3 (n : Nat) :
    run0 p (90*n+732) (A (2*n+1) 3) =
    some (B 11 (2*n+6)) := by
  rw [← in_A3 n,← out_A3 n]
  exact Raw36FirstOverflowA3.transport n

theorem in_A4 (n : Nat) :
    Raw36FirstOverflowA4.source.eval n = A (2*n+1) 4 := by
  rw [A_special n 1 4 (by omega)]
  simp [Raw36FirstOverflowA4.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A4 (n : Nat) :
    Raw36FirstOverflowA4.target.eval n = B 9 (2*n+9) := by
  rw [B_target n 9 9]
  simp [Raw36FirstOverflowA4.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A4 (n : Nat) :
    run0 p (108*n+768) (A (2*n+1) 4) =
    some (B 9 (2*n+9)) := by
  rw [← in_A4 n,← out_A4 n]
  exact Raw36FirstOverflowA4.transport n

theorem in_A5 (n : Nat) :
    Raw36FirstOverflowA5.source.eval n = A (2*n+1) 5 := by
  rw [A_special n 1 5 (by omega)]
  simp [Raw36FirstOverflowA5.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A5 (n : Nat) :
    Raw36FirstOverflowA5.target.eval n = B 7 (2*n+12) := by
  rw [B_target n 7 12]
  simp [Raw36FirstOverflowA5.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A5 (n : Nat) :
    run0 p (126*n+840) (A (2*n+1) 5) =
    some (B 7 (2*n+12)) := by
  rw [← in_A5 n,← out_A5 n]
  exact Raw36FirstOverflowA5.transport n

theorem in_A6 (n : Nat) :
    Raw36FirstOverflowA6.source.eval n = A (2*n+1) 6 := by
  rw [A_special n 1 6 (by omega)]
  simp [Raw36FirstOverflowA6.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A6 (n : Nat) :
    Raw36FirstOverflowA6.target.eval n = B 5 (2*n+15) := by
  rw [B_target n 5 15]
  simp [Raw36FirstOverflowA6.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A6 (n : Nat) :
    run0 p (144*n+948) (A (2*n+1) 6) =
    some (B 5 (2*n+15)) := by
  rw [← in_A6 n,← out_A6 n]
  exact Raw36FirstOverflowA6.transport n

theorem in_A7 (n : Nat) :
    Raw36FirstOverflowA7.source.eval n = A (2*n+1) 7 := by
  rw [A_special n 1 7 (by omega)]
  simp [Raw36FirstOverflowA7.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A7 (n : Nat) :
    Raw36FirstOverflowA7.target.eval n = B 3 (2*n+18) := by
  rw [B_target n 3 18]
  simp [Raw36FirstOverflowA7.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A7 (n : Nat) :
    run0 p (162*n+1092) (A (2*n+1) 7) =
    some (B 3 (2*n+18)) := by
  rw [← in_A7 n,← out_A7 n]
  exact Raw36FirstOverflowA7.transport n

theorem in_A8 (n : Nat) :
    Raw36FirstOverflowA8.source.eval n = A (2*n+1) 8 := by
  rw [A_special n 1 8 (by omega)]
  simp [Raw36FirstOverflowA8.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A8 (n : Nat) :
    Raw36FirstOverflowA8.target.eval n = B 1 (2*n+21) := by
  rw [B_target n 1 21]
  simp [Raw36FirstOverflowA8.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A8 (n : Nat) :
    run0 p (180*n+1272) (A (2*n+1) 8) =
    some (B 1 (2*n+21)) := by
  rw [← in_A8 n,← out_A8 n]
  exact Raw36FirstOverflowA8.transport n

theorem in_A9 (n : Nat) :
    Raw36FirstOverflowA9.source.eval n = A (2*n+1) 9 := by
  rw [A_special n 1 9 (by omega)]
  simp [Raw36FirstOverflowA9.source,PZ.eval,Word.eval,
        Apre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_A9 (n : Nat) :
    Raw36FirstOverflowA9.target.eval n = B 19 (2*n+14) := by
  rw [B_target n 19 14]
  simp [Raw36FirstOverflowA9.target,PZ.eval,Word.eval,
        Bpre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_A9 (n : Nat) :
    run0 p (198*n+2398) (A (2*n+1) 9) =
    some (B 19 (2*n+14)) := by
  rw [← in_A9 n,← out_A9 n]
  exact Raw36FirstOverflowA9.transport n

theorem in_B0 (n : Nat) :
    Raw36FirstOverflowB0.source.eval n = B (2*n+7) 0 := by
  rw [B_special n 7 0 (by omega)]
  simp [Raw36FirstOverflowB0.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B0 (n : Nat) :
    Raw36FirstOverflowB0.target.eval n = A 13 (2*n+2) := by
  rw [A_target n 13 2]
  simp [Raw36FirstOverflowB0.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B0 (n : Nat) :
    run0 p (36*n+768) (B (2*n+7) 0) =
    some (A 13 (2*n+2)) := by
  rw [← in_B0 n,← out_B0 n]
  exact Raw36FirstOverflowB0.transport n

theorem in_B1 (n : Nat) :
    Raw36FirstOverflowB1.source.eval n = B (2*n+3) 1 := by
  rw [B_special n 3 1 (by omega)]
  simp [Raw36FirstOverflowB1.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B1 (n : Nat) :
    Raw36FirstOverflowB1.target.eval n = A 11 (2*n+1) := by
  rw [A_target n 11 1]
  simp [Raw36FirstOverflowB1.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B1 (n : Nat) :
    run0 p (54*n+642) (B (2*n+3) 1) =
    some (A 11 (2*n+1)) := by
  rw [← in_B1 n,← out_B1 n]
  exact Raw36FirstOverflowB1.transport n

theorem in_B2 (n : Nat) :
    Raw36FirstOverflowB2.source.eval n = B (2*n+3) 2 := by
  rw [B_special n 3 2 (by omega)]
  simp [Raw36FirstOverflowB2.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B2 (n : Nat) :
    Raw36FirstOverflowB2.target.eval n = A 9 (2*n+4) := by
  rw [A_target n 9 4]
  simp [Raw36FirstOverflowB2.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B2 (n : Nat) :
    run0 p (72*n+624) (B (2*n+3) 2) =
    some (A 9 (2*n+4)) := by
  rw [← in_B2 n,← out_B2 n]
  exact Raw36FirstOverflowB2.transport n

theorem in_B3 (n : Nat) :
    Raw36FirstOverflowB3.source.eval n = B (2*n+3) 3 := by
  rw [B_special n 3 3 (by omega)]
  simp [Raw36FirstOverflowB3.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B3 (n : Nat) :
    Raw36FirstOverflowB3.target.eval n = A 7 (2*n+7) := by
  rw [A_target n 7 7]
  simp [Raw36FirstOverflowB3.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B3 (n : Nat) :
    run0 p (90*n+642) (B (2*n+3) 3) =
    some (A 7 (2*n+7)) := by
  rw [← in_B3 n,← out_B3 n]
  exact Raw36FirstOverflowB3.transport n

theorem in_B4 (n : Nat) :
    Raw36FirstOverflowB4.source.eval n = B (2*n+3) 4 := by
  rw [B_special n 3 4 (by omega)]
  simp [Raw36FirstOverflowB4.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B4 (n : Nat) :
    Raw36FirstOverflowB4.target.eval n = A 5 (2*n+10) := by
  rw [A_target n 5 10]
  simp [Raw36FirstOverflowB4.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B4 (n : Nat) :
    run0 p (108*n+696) (B (2*n+3) 4) =
    some (A 5 (2*n+10)) := by
  rw [← in_B4 n,← out_B4 n]
  exact Raw36FirstOverflowB4.transport n

theorem in_B5 (n : Nat) :
    Raw36FirstOverflowB5.source.eval n = B (2*n+3) 5 := by
  rw [B_special n 3 5 (by omega)]
  simp [Raw36FirstOverflowB5.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B5 (n : Nat) :
    Raw36FirstOverflowB5.target.eval n = A 3 (2*n+13) := by
  rw [A_target n 3 13]
  simp [Raw36FirstOverflowB5.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B5 (n : Nat) :
    run0 p (126*n+786) (B (2*n+3) 5) =
    some (A 3 (2*n+13)) := by
  rw [← in_B5 n,← out_B5 n]
  exact Raw36FirstOverflowB5.transport n

theorem in_B6 (n : Nat) :
    Raw36FirstOverflowB6.source.eval n = B (2*n+3) 6 := by
  rw [B_special n 3 6 (by omega)]
  simp [Raw36FirstOverflowB6.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B6 (n : Nat) :
    Raw36FirstOverflowB6.target.eval n = A 1 (2*n+16) := by
  rw [A_target n 1 16]
  simp [Raw36FirstOverflowB6.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B6 (n : Nat) :
    run0 p (144*n+912) (B (2*n+3) 6) =
    some (A 1 (2*n+16)) := by
  rw [← in_B6 n,← out_B6 n]
  exact Raw36FirstOverflowB6.transport n

theorem in_B7 (n : Nat) :
    Raw36FirstOverflowB7.source.eval n = B (2*n+3) 7 := by
  rw [B_special n 3 7 (by omega)]
  simp [Raw36FirstOverflowB7.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B7 (n : Nat) :
    Raw36FirstOverflowB7.target.eval n = A 19 (2*n+9) := by
  rw [A_target n 19 9]
  simp [Raw36FirstOverflowB7.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B7 (n : Nat) :
    run0 p (162*n+2164) (B (2*n+3) 7) =
    some (A 19 (2*n+9)) := by
  rw [← in_B7 n,← out_B7 n]
  exact Raw36FirstOverflowB7.transport n

theorem in_B8 (n : Nat) :
    Raw36FirstOverflowB8.source.eval n = B (2*n+3) 8 := by
  rw [B_special n 3 8 (by omega)]
  simp [Raw36FirstOverflowB8.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B8 (n : Nat) :
    Raw36FirstOverflowB8.target.eval n = A 17 (2*n+12) := by
  rw [A_target n 17 12]
  simp [Raw36FirstOverflowB8.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B8 (n : Nat) :
    run0 p (180*n+2182) (B (2*n+3) 8) =
    some (A 17 (2*n+12)) := by
  rw [← in_B8 n,← out_B8 n]
  exact Raw36FirstOverflowB8.transport n

theorem in_B9 (n : Nat) :
    Raw36FirstOverflowB9.source.eval n = B (2*n+3) 9 := by
  rw [B_special n 3 9 (by omega)]
  simp [Raw36FirstOverflowB9.source,PZ.eval,Word.eval,
        Bpre,tailWord,pair,quad,mark,suffix,rep,List.append_assoc]

theorem out_B9 (n : Nat) :
    Raw36FirstOverflowB9.target.eval n = A 15 (2*n+15) := by
  rw [A_target n 15 15]
  simp [Raw36FirstOverflowB9.target,PZ.eval,Word.eval,
        Apre,pair,quad,mark,suffix,rep,List.append_assoc]

theorem transfer_B9 (n : Nat) :
    run0 p (198*n+2236) (B (2*n+3) 9) =
    some (A 15 (2*n+15)) := by
  rw [← in_B9 n,← out_B9 n]
  exact Raw36FirstOverflowB9.transport n

#print axioms transfer_A0
#print axioms transfer_A9
#print axioms transfer_B9
end BB6Coverage.Agent31Pump.Auto.Raw36FirstAlign
