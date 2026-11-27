#!/usr/bin/env node
"use strict";

/* Original six-state partial table, F1 undefined; one raw transition per tick.
   This script is an untrusted independent falsifier, not a proof checker. */
const table = "1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---";
const moves = table.split("_").map(pair =>
  [pair.slice(0, 3), pair.slice(3, 6)].map(s =>
    s === "---" ? null : [+s[0], s[1] === "R" ? 1 : -1, s.charCodeAt(2) - 65]));
const P = "F0 E0 A0 B1 E1 A0 B0 C0 D0 D0 D1 B1 E0";
const Q = "A0 B0 C0 D0 D0 D1 B1 E0";
const R = "A0 B0 C1";
const expand = (word, times) =>
  times === 0 ? "" : Array(times).fill(word).join(" ");

function expectedTrace(rs) {
  let parts = [P, expand("A1", rs[rs.length - 1] + 2), Q];
  for (let j = rs.length - 2; j >= 0; --j)
    parts.push(expand("A1", rs[j] + 1), Q);
  parts.push("A1", R);
  return parts.join(" ").split(" ");
}

function validate(rs, seed) {
  const n = rs.length;
  if (!n || rs.some((r, i) => !Number.isSafeInteger(r) ||
      r < ((i === 0 && n === 1 || i === n - 1) ? 1 : 2)))
    throw new Error("tuple outside claimed domain: " + JSON.stringify(rs));
  const sum = rs.reduce((a, b) => a + b, 0);
  const input = "00" + rs.map(r => "1".repeat(r)).join("0") + "00000";
  const low = 5 - input.length;
  const high = 4;
  const bits = new Set();
  for (let i = 0; i < input.length; ++i)
    if (input[i] === "1") bits.add(low + i);
  // Deterministic nonempty arbitrary tails on BOTH sides.
  for (let x = low - 24; x < low; ++x)
    if (((x * x + seed * 17 + 3) % 11 + 11) % 11 < 5) bits.add(x);
  for (let x = high + 1; x <= high + 24; ++x)
    if (((x * x + seed * 19 + 7) % 13 + 13) % 13 < 6) bits.add(x);
  const exterior = [...bits].filter(x => x < low || x > high).sort((a,b) => a-b);
  const trace = expectedTrace(rs);
  let state = 5, head = 0;
  for (let t = 0; t < trace.length; ++t) {
    if (head < low || head > high)
      throw new Error("macro crossed prescribed boundary: " + JSON.stringify({rs,t,head}));
    const read = +bits.has(head);
    const tag = "ABCDEF"[state] + read;
    if (trace[t] !== tag)
      throw new Error("trace discrepancy: " + JSON.stringify({rs,t,tag,expected:trace[t],head}));
    const instruction = moves[state][read];
    if (!instruction) throw new Error("queried unassigned transition: " + JSON.stringify({rs,t,tag}));
    if (instruction[0]) bits.add(head); else bits.delete(head);
    head += instruction[1];
    state = instruction[2];
    if (t < trace.length - 1 && state === 5)
      throw new Error("unexpected early return to F: " + JSON.stringify({rs,t}));
  }
  const output = rs.length === 1
    ? "11101" + "0".repeat(rs[0] - 1) + "101"
    : "11101" + rs.slice(0,-1).map(r => "0".repeat(r - 2) + "101").join("") +
         "0".repeat(rs[rs.length - 1] - 1) + "101";
  let actual = "";
  for (let x=low; x<=high; ++x) actual += bits.has(x) ? "1" : "0";
  const actualExterior = [...bits].filter(x => x < low || x > high).sort((a,b) => a-b);
  if (actual !== output || trace.length !== sum + 18 + 9*n ||
      head !== 2 - sum - n || state !== 5 || bits.has(head) ||
      actualExterior.join(",") !== exterior.join(","))
    throw new Error("macro discrepancy: " +
      JSON.stringify({rs,actual,output,steps:trace.length,head,state}));
}

let tested = 0;
for (let n=1; n<=4; ++n) {
  let count = 7**n;
  for (let num=0; num<count; ++num) {
    let i=num,rs=[];
    for (let j=0;j<n;++j) {rs.push(i%7 + 1);i=Math.floor(i/7);}
    if (rs.some((r,j) => r < ((j===0 && n===1 || j===n-1) ? 1 : 2))) continue;
    validate(rs,num+n*7919); ++tested;
  }
}
if (tested !== 1813) throw new Error("wrong exhaustive sample count: " + tested);
for (let n=1;n<=12;++n) for (let z=0;z<40;++z) {
  let rs=Array.from({length:n},(_,i)=> {
    const min=(i===0&&n===1 || i===n-1)?1:2;
    return min + (5*z + i*i*7 + n*13) % 47;
  });
  validate(rs,n*47+z);++tested;
}
console.log(JSON.stringify({machine:table, status:"finite test passed", cases:tested,
  exhaustiveSmallDomain:1813, longerCases:480, formalProof:false}));
