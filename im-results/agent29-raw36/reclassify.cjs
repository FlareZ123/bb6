#!/usr/bin/env node
"use strict";
/* Reclassify the Raw36 C1 siblings with the *fixed-point-correct* FAR
   generator. This is deliberately a new, non-certifying census, NOT a
   source theorem. Each row is flushed independently to survive a timeout.
   It does not trust or mutate candidate.json's old 24 result rows. */
const fs = require("fs");
const {makeSearch} = require("./search.cjs");
const spec = JSON.parse(fs.readFileSync(__dirname + "/candidate.json", "utf8"));
const search = makeSearch(spec.codes, spec.options);
const path = process.argv[2];
const indices = process.argv.slice(3).map(Number);
if (!path || !indices.length || indices.some(i => !Number.isInteger(i) || i < 0 || i >= 24))
  throw Error("Usage: node reclassify.cjs OUT.jsonl I [I...]");
fs.writeFileSync(path, "");
for (const i of indices) {
  const p = search.parse(spec.parent);
  p[spec.query[2]] = i;
  const old = spec.results[i];
  const before = Date.now();
  const row = {i, move: search.decode(i), source: "corrected least-fixed-point FAR",
    old: {stats: old.stats, mass: old.mass},
    options: spec.options};
  try {
    const next = search.run(p);
    row.status = "classified";
    row.stats = next.stats;
    row.mass = next.mass;
    row.expected = next.expected;
    row.used = next.used;
    row.opensSample = next.opens.slice(0, 30);
    row.changed = JSON.stringify(old.stats) !== JSON.stringify(next.stats) ||
       JSON.stringify(old.mass) !== JSON.stringify(next.mass);
  } catch (err) {
    row.status = "failed-to-complete";
    row.error = String(err.stack || err);
  }
  row.seconds = (Date.now() - before) / 1000;
  fs.appendFileSync(path, JSON.stringify(row) + "\n");
  process.stdout.write(JSON.stringify({i:row.i,move:row.move,
    status:row.status,stats:row.stats,error:row.error,changed:row.changed,
    seconds:row.seconds})+"\n");
}
