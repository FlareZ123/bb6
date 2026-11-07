from pathlib import Path

source = Path(__file__).with_name("test-root119-odd-wave-audit.cjs")
text = source.read_text(encoding="utf-8")

replacements = [
    (
        """let previousBit = null;

function bit(x) {""",
        """let previousBit = null;
let predictedIntervals = 0;

function bit(x) {""",
    ),
    (
        """  for (const prediction of due) {
    assert.equal(q, 'B', `predicted B/0 at time ${time}`);
    assert.equal(head, prediction.head, `predicted head at time ${time}`);
  }""",
        """  for (const prediction of due) {
    assert.equal(q, 'B', `predicted B/0 at time ${time}`);
    assert.equal(head, prediction.head, `predicted head at time ${time}`);
    assert.equal(bit(head), 0, `predicted B/0 reads zero at time ${time}`);
  }""",
    ),
    (
        """    if (previousB0 && due.length === 0) {
      residuals.push({
        from: previousB0.time,
        to: time,
        duration: time - previousB0.time,
        delta: head - previousB0.head,
        start: previousB0.context,
        fEvents: previousB0.fEvents,
        dEvents: previousB0.dEvents,
      });
    }

    let leftRun = 0;""",
        """    if (previousB0 && due.length === 0) {
      residuals.push({
        from: previousB0.time,
        to: time,
        duration: time - previousB0.time,
        delta: head - previousB0.head,
        start: previousB0.context,
        fEvents: previousB0.fEvents,
        dEvents: previousB0.dEvents,
      });
    } else if (previousB0) {
      predictedIntervals++;
    }

    let leftRun = 0;""",
    ),
    (
        """  simulatedSteps: LIMIT,
  unmatchedB0Intervals: residuals.length,
  classifiedByParameterizedWaveMacros: counts,""",
        """  simulatedSteps: LIMIT,
  completedB0Intervals: residuals.length + predictedIntervals,
  predictedB0Intervals: predictedIntervals,
  unmatchedB0Intervals: residuals.length,
  pendingPredictionsAtCutoff: Array.from(pending.entries()),
  lastB0AtCutoff: previousB0 ? { time: previousB0.time, head: previousB0.head } : null,
  classifiedByParameterizedWaveMacros: counts,""",
    ),
]

for old, new in replacements:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"Expected one audit source match, found {count}: {old[:80]!r}")
    text = text.replace(old, new)

source.write_text(text, encoding="utf-8")
print("Patched odd-wave audit: assert predicted B/0 reads zero and report cutoff coverage.")
