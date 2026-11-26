import Raw11ClosedSubset
import Raw11SweepA1LA

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Raw11
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
def parent : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | _, _ => none)
def p0 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨false, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 2⟩)
  | _, _ => none)
def p1 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨false, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 0⟩)
  | _, _ => none)
def p2 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨false, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 0⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, false, 0⟩)
  | _, _ => none)
def p3 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 0⟩)
  | _, _ => none)
def p4 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 1⟩)
  | _, _ => none)
def p5 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, false, 0⟩)
  | _, _ => none)
def p6 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 2⟩)
  | _, _ => none)
def p7 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | _, _ => none)
def p8 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 2⟩)
  | _, _ => none)
def p9 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 2⟩)
  | _, _ => none)
def p10 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | _, _ => none)
def p11 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 1⟩)
  | _, _ => none)
def p12 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 0⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 2⟩)
  | _, _ => none)
def p13 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, false, 0⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 2⟩)
  | _, _ => none)
def p14 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, false, 0⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 1⟩)
  | _, _ => none)
def p15 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 0⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 0⟩)
  | _, _ => none)
def p16 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 0⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 2⟩)
  | _, _ => none)
def p17 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, true, 2⟩)
  | _, _ => none)
def p18 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 0⟩)
  | _, _ => none)
def p19 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 2⟩)
  | _, _ => none)
def p20 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 0⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, false, 1⟩)
  | _, _ => none)
def p21 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | _, _ => none)
def p22 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | _, _ => none)
def p23 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, false, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | _, _ => none)
def p24 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 1⟩)
  | _, _ => none)
def p25 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, false, 0⟩)
  | _, _ => none)
def p26 : PartialMachine := (fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, false, 2⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨true, true, 1⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨true, false, 0⟩)
  | _, _ => none)

def audit : PartialAudit := .split 3 (0,true) (byPartialMove [
.closed (.cycle 0 5 false (2)),
.split 4 (1,true) (byPartialMove [
.closed (.cycle 0 5 false (2)),
.closed (.cycle 5 3 false (0)),
.closed (.cycle 0 6 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 5 true (0)),
.closed (.cycle 5 3 false (2)),
.closed (.cycle 0 6 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 7 3 false (-1)),
.split 6 (2,true) (byPartialMove [
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 4 3 false (0)),
.closed (.cycle 0 9 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 7 true (-1)),
.closed (.cycle 1 9 false (2)),
.closed (.proven p0 (closedSubsetOK_never p0 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 4 3 false (0)),
.closed (.cycle 6 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 12 5 false (0)),
.closed (.cycle 10 5 false (0)),
.closed (.cycle 2 5 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.split 8 (2,true) (byPartialMove [
.closed (.cycle 3 6 false (1)),
.closed (.cycle 11 3 false (-2)),
.closed (.cycle 0 12 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p1 (closedSubsetOK_never p1 3 (by decide) (by decide))),
.closed (.cycle 4 13 false (2)),
.closed (.cycle 23 3 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 6 false (1)),
.closed (.cycle 4 9 false (0)),
.closed (.cycle 5 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 18 false (3)),
.closed (.cycle 12 2 true (-1)),
.closed (.cycle 2 12 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 5 true (0)),
.closed (.cycle 1 4 true (0)),
.closed (.cycle 5 3 false (1)),
.unresolved,
.unresolved,
.unresolved]),
.split 4 (2,true) (byPartialMove [
.closed (.cycle 0 5 false (2)),
.closed (.cycle 0 9 false (2)),
.closed (.cycle 0 6 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 5 true (0)),
.closed (.cycle 0 9 false (2)),
.closed (.cycle 0 6 true (0)),
.unresolved,
.unresolved,
.unresolved,
.split 6 (1,true) (byPartialMove [
.closed (.cycle 0 9 false (2)),
.closed (.cycle 0 12 false (2)),
.closed (.cycle 4 3 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 7 true (-1)),
.closed (.cycle 0 13 false (2)),
.closed (.cycle 0 15 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 9 false (2)),
.closed (.cycle 0 12 false (2)),
.closed (.cycle 4 3 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p2 (closedSubsetOK_never p2 3 (by decide) (by decide))),
.closed (.cycle 0 13 false (2)),
.closed (.cycle 2 5 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.split 7 (1,true) (byPartialMove [
.closed (.cycle 0 14 false (2)),
.closed (.cycle 0 12 false (2)),
.closed (.cycle 0 9 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 false (2)),
.closed (.cycle 0 13 false (2)),
.closed (.cycle 4 4 true (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 12 false (2)),
.closed (.cycle 5 3 false (0)),
.closed (.cycle 4 9 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 5 false (1)),
.closed (.cycle 6 6 true (-1)),
.closed (.cycle 6 2 true (-1)),
.unresolved,
.unresolved,
.unresolved]),
.closed (.cycle 4 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 5 true (0)),
.closed (.cycle 1 4 true (0)),
.closed (.cycle 0 8 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 4 true (0)),
.closed (.cycle 1 3 true (1)),
.closed (.cycle 0 5 true (0)),
.unresolved,
.unresolved,
.unresolved,
.split 6 (1,true) (byPartialMove [
.closed (.cycle 4 3 false (0)),
.closed (.cycle 4 6 false (0)),
.split 7 (2,true) (byPartialMove [
.closed (.cycle 0 8 false (2)),
.closed (.cycle 4 6 false (0)),
.closed (.cycle 0 9 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 11 true (-1)),
.closed (.cycle 9 6 true (1)),
.closed (.cycle 0 30 true (-2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (0)),
.closed (.cycle 0 12 false (2)),
.closed (.cycle 7 6 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p3 (closedSubsetOK_never p3 3 (by decide) (by decide))),
.closed (.proven p4 (closedSubsetOK_never p4 3 (by decide) (by decide))),
.closed (.cycle 4 5 false (0)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (-1)),
.closed (.cycle 7 5 true (1)),
.split 7 (2,true) (byPartialMove [
.closed (.cycle 11 9 false (1)),
.closed (.cycle 1 7 false (2)),
.closed (.cycle 3 14 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (-1)),
.closed (.cycle 0 25 true (-1)),
.closed (.cycle 0 9 true (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p5 (closedSubsetOK_never p5 3 (by decide) (by decide))),
.closed (.cycle 6 4 true (0)),
.closed (.cycle 16 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 14 true (-1)),
.closed (.cycle 1 7 true (-1)),
.closed (.proven p6 (closedSubsetOK_never p6 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 4 3 false (0)),
.split 9 (2,true) (byPartialMove [
.closed (.cycle 4 6 false (0)),
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 0 12 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 7 false (0)),
.closed (.proven p7 (closedSubsetOK_never p7 3 (by decide) (by decide))),
.closed (.cycle 0 13 true (-2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 4 6 false (0)),
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 9 6 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 8 false (1)),
.closed (.cycle 6 5 false (0)),
.closed (.proven p8 (closedSubsetOK_never p8 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.split 7 (2,true) (byPartialMove [
.closed (.cycle 3 8 false (1)),
.closed (.cycle 4 6 false (0)),
.closed (.cycle 0 9 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 4 4 true (-1)),
.closed (.cycle 2 12 false (2)),
.closed (.cycle 0 11 true (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (0)),
.closed (.cycle 6 9 false (0)),
.closed (.cycle 7 6 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 5 false (1)),
.closed (.cycle 6 2 true (-1)),
.closed (.proven p9 (closedSubsetOK_never p9 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 5 false (1)),
.closed (.proven BB6.Agent44Raw11A1LA.table BB6.Agent44Raw11A1LA.never),
.split 7 (2,true) (byPartialMove [
.closed (.cycle 3 5 false (1)),
.closed (.cycle 2 7 false (2)),
.closed (.cycle 0 11 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (-1)),
.closed (.proven p10 (closedSubsetOK_never p10 3 (by decide) (by decide))),
.closed (.cycle 0 22 true (-2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 5 false (1)),
.closed (.cycle 6 2 true (0)),
.closed (.cycle 7 6 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 12 7 false (2)),
.closed (.proven p11 (closedSubsetOK_never p11 3 (by decide) (by decide))),
.closed (.proven p12 (closedSubsetOK_never p12 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved]),
.split 4 (1,true) (byPartialMove [
.split 7 (2,true) (byPartialMove [
.closed (.cycle 3 5 false (1)),
.closed (.cycle 0 13 false (2)),
.closed (.cycle 0 11 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (-1)),
.closed (.cycle 6 5 true (0)),
.closed (.proven p13 (closedSubsetOK_never p13 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 5 false (1)),
.closed (.cycle 4 8 false (1)),
.closed (.cycle 5 6 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 12 7 false (2)),
.closed (.proven p14 (closedSubsetOK_never p14 3 (by decide) (by decide))),
.closed (.cycle 2 12 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.split 9 (2,true) (byPartialMove [
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 4 6 false (0)),
.closed (.cycle 0 12 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 12 false (2)),
.closed (.cycle 10 5 true (0)),
.closed (.cycle 21 12 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 4 6 false (0)),
.closed (.cycle 9 6 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 12 12 false (0)),
.closed (.cycle 17 10 false (-1)),
.closed (.cycle 2 8 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.closed (.cycle 0 6 false (2)),
.unresolved,
.unresolved,
.unresolved,
.split 7 (2,true) (byPartialMove [
.closed (.cycle 5 3 false (1)),
.closed (.cycle 0 9 true (0)),
.closed (.cycle 0 10 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 5 5 true (0)),
.closed (.cycle 0 9 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (1)),
.closed (.cycle 4 4 true (0)),
.closed (.cycle 7 6 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (0)),
.closed (.cycle 2 6 true (0)),
.unresolved,
.unresolved,
.unresolved]),
.split 10 (2,true) (byPartialMove [
.closed (.cycle 8 3 false (2)),
.closed (.cycle 5 6 true (1)),
.closed (.cycle 0 13 false (3)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 11 true (0)),
.closed (.cycle 6 5 true (1)),
.closed (.cycle 0 12 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 3 false (2)),
.closed (.cycle 4 7 true (0)),
.closed (.cycle 10 6 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 11 true (0)),
.closed (.cycle 1 10 true (0)),
.closed (.cycle 2 9 true (0)),
.unresolved,
.unresolved,
.unresolved]),
.split 5 (2,true) (byPartialMove [
.closed (.cycle 0 6 true (0)),
.closed (.cycle 0 13 false (2)),
.closed (.cycle 0 7 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 5 5 true (1)),
.closed (.cycle 0 7 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 9 true (0)),
.closed (.cycle 4 4 true (0)),
.closed (.cycle 5 6 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 1 5 true (0)),
.closed (.cycle 2 8 true (0)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.split 9 (2,true) (byPartialMove [
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 4 6 false (0)),
.closed (.cycle 0 12 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p15 (closedSubsetOK_never p15 3 (by decide) (by decide))),
.closed (.cycle 3 10 false (1)),
.closed (.cycle 0 13 true (-2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 7 3 false (-1)),
.closed (.cycle 4 6 false (0)),
.closed (.cycle 9 6 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 5 false (0)),
.closed (.cycle 3 8 false (1)),
.closed (.proven p16 (closedSubsetOK_never p16 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.split 6 (2,true) (byPartialMove [
.closed (.cycle 5 3 false (0)),
.closed (.cycle 4 3 false (0)),
.closed (.cycle 0 9 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (-1)),
.closed (.cycle 8 5 true (0)),
.closed (.cycle 0 9 true (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (0)),
.closed (.cycle 4 3 false (0)),
.closed (.cycle 6 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 4 5 false (1)),
.closed (.cycle 4 5 false (1)),
.closed (.proven p17 (closedSubsetOK_never p17 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.split 8 (2,true) (byPartialMove [
.closed (.cycle 3 6 false (1)),
.closed (.cycle 4 12 false (0)),
.closed (.cycle 0 12 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p18 (closedSubsetOK_never p18 3 (by decide) (by decide))),
.closed (.cycle 2 8 false (2)),
.closed (.proven p19 (closedSubsetOK_never p19 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 6 false (1)),
.closed (.cycle 4 9 false (0)),
.closed (.cycle 5 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 12 false (1)),
.closed (.cycle 8 2 true (0)),
.closed (.cycle 8 6 true (-1)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 2 true (0)),
.closed (.cycle 1 5 true (0)),
.split 5 (2,true) (byPartialMove [
.closed (.cycle 5 3 false (1)),
.closed (.cycle 5 5 false (1)),
.closed (.cycle 0 8 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 5 5 true (1)),
.closed (.cycle 0 7 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 3 false (1)),
.closed (.cycle 4 2 true (0)),
.closed (.cycle 5 6 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 1 5 true (0)),
.closed (.cycle 2 4 true (0)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved]),
.split 4 (2,true) (byPartialMove [
.closed (.cycle 3 5 false (1)),
.split 12 (1,true) (byPartialMove [
.closed (.cycle 7 6 false (-1)),
.closed (.cycle 5 9 false (0)),
.closed (.cycle 4 9 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.proven p20 (closedSubsetOK_never p20 3 (by decide) (by decide))),
.closed (.cycle 6 10 false (0)),
.closed (.cycle 8 12 true (-3)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 7 6 false (-1)),
.closed (.cycle 13 3 false (-3)),
.closed (.cycle 4 9 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 16 8 true (0)),
.closed (.cycle 10 8 true (-3)),
.closed (.cycle 2 11 false (2)),
.unresolved,
.unresolved,
.unresolved]),
.closed (.cycle 0 6 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (-1)),
.split 5 (1,true) (byPartialMove [
.closed (.cycle 0 6 true (0)),
.closed (.cycle 2 14 false (2)),
.closed (.cycle 0 7 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.proven p21 (closedSubsetOK_never p21 3 (by decide) (by decide))),
.closed (.cycle 0 7 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 18 false (1)),
.closed (.proven p22 (closedSubsetOK_never p22 3 (by decide) (by decide))),
.closed (.proven p23 (closedSubsetOK_never p23 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 1 5 true (0)),
.closed (.proven p24 (closedSubsetOK_never p24 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved]),
.closed (.cycle 0 7 true (0)),
.unresolved,
.unresolved,
.unresolved,
.split 6 (1,true) (byPartialMove [
.closed (.cycle 3 9 false (1)),
.closed (.cycle 3 12 false (1)),
.closed (.cycle 4 3 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 11 false (1)),
.closed (.cycle 28 13 true (0)),
.closed (.proven p25 (closedSubsetOK_never p25 3 (by decide) (by decide))),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 9 false (1)),
.closed (.cycle 3 12 false (1)),
.closed (.cycle 4 3 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 11 false (1)),
.closed (.proven p26 (closedSubsetOK_never p26 3 (by decide) (by decide))),
.closed (.cycle 3 5 false (1)),
.unresolved,
.unresolved,
.unresolved]),
.split 7 (1,true) (byPartialMove [
.closed (.cycle 8 6 false (0)),
.closed (.cycle 7 9 false (-1)),
.closed (.cycle 0 9 false (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 8 false (0)),
.closed (.cycle 8 9 true (0)),
.closed (.cycle 4 4 true (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 9 6 false (-1)),
.closed (.cycle 5 3 false (0)),
.closed (.cycle 4 9 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 5 false (1)),
.closed (.cycle 6 7 true (-1)),
.closed (.cycle 6 2 true (-1)),
.unresolved,
.unresolved,
.unresolved]),
.closed (.cycle 4 6 false (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 2 true (0)),
.split 5 (1,true) (byPartialMove [
.closed (.cycle 3 16 false (2)),
.closed (.cycle 5 15 false (1)),
.closed (.cycle 1 6 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 15 14 true (1)),
.closed (.cycle 0 7 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 3 12 false (1)),
.closed (.cycle 5 5 false (1)),
.closed (.cycle 4 2 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 6 true (0)),
.closed (.cycle 1 5 true (0)),
.closed (.cycle 2 4 true (0)),
.unresolved,
.unresolved,
.unresolved]),
.closed (.cycle 2 4 true (0)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 4 true (0)),
.closed (.cycle 1 3 true (1)),
.closed (.cycle 2 2 true (1)),
.unresolved,
.unresolved,
.unresolved])

def bound : Nat := 18
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem supported : TNFSupport parent 3 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck bound parent 3 audit = true := by decide +kernel

def frontier := canonicalResiduals parent 3 audit

theorem frontier_count : frontier.length = 116 := by decide +kernel

theorem partition (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound bound m ∨ ∃ e ∈ frontier, TNFQuotientCompatible e.2 m :=
  canonicalSound bound parent 3 audit (by decide) supported root nohalt checked m hm

/-- Consume the exact frontier at any larger common weighted bound. -/
theorem cover_from_frontier (B : Nat) (hB : bound ≤ B)
    (h : ∀ e ∈ frontier, ∀ m, TNFQuotientCompatible e.2 m → WeightedBound B m) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases partition m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · exact h e he m hq

#print axioms cover_from_frontier
#print axioms partition
#print axioms frontier_count
end BB6.Agent44Raw11
