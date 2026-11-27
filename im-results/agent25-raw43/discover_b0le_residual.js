#!/usr/bin/env node
// Discovery-only census for the eight Raw43 B1=0LE E0 cylinders not covered by
// the existing reduced parent. Lean generation rechecks every certificate.
const fs = require("fs");
const path = require("path");
const api = new Function(fs.readFileSync(path.join(__dirname, "discover.js"), "utf8"))();
const variants = new Set(["0la","0lf","1la","1lb","1le","1lf","1ra","1rf"]);
const v = (process.argv[2] || "").toLowerCase();
if (!variants.has(v)) throw new Error("expected one of: " + [...variants].join(","));
const action = v[0] + v[1].toUpperCase() + v[2].toUpperCase();
const table = `1RB---_1RC0LE_0RD---_1LD0RB_${action}---_------`;
const solved = api.solve(table, 1000, 4, 10000);
const lateNs = Object.values(solved.lateLast || {}).map(x => x.n);
const bound = Math.max(solved.maxQuery || 0, ...lateNs, 0) + 6;
const root = solved.root && solved.root[0] === "q"
  ? ["split", solved.root[1], solved.root[2]] : solved.root;
const out = {
  table, cap: 1000, lookback: 32, stats: solved.stats,
  rootQuery: root, openRows: solved.opens, bound,
  witnesses: solved.witnesses, bidfa: {}, lateLast: solved.lateLast,
  lateCycle: solved.lateCycle, growth: {}, unresolved: solved.unresolved
};
const outPath = process.argv[3] || `/tmp/spec_b0le_e${v}.json`;
fs.writeFileSync(outPath, JSON.stringify(out, null, 2) + "\n");
console.log(JSON.stringify({
  variant:v, table, bound, stats:out.stats,
  far:Object.keys(out.witnesses).length,
  lateLast:Object.keys(out.lateLast).length,
  lateCycle:Object.keys(out.lateCycle).length,
  unresolved:out.unresolved.length,
  output:outPath
}));
