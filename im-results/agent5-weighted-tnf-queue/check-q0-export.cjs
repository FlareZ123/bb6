#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");

const PINNED_SOURCE = "33209bc7dc282b38c8cd6be507bfc551fea56108";
const STATES = "ABCDEF";

function die(message) {
  console.error("q0-export-check: " + message);
  process.exit(1);
}

function sha256(data) {
  return crypto.createHash("sha256").update(data).digest("hex");
}

function walk(dir) {
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...walk(p));
    else out.push(p);
  }
  return out;
}

function balancedValue(text, start) {
  if (text[start] !== "(") throw new Error("packed queue value does not start with '('");
  let depth = 0;
  let inString = false;
  let escaped = false;
  for (let i = start; i < text.length; i++) {
    const c = text[i];
    if (inString) {
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') inString = false;
      continue;
    }
    if (c === '"') inString = true;
    else if (c === "(") depth++;
    else if (c === ")") {
      depth--;
      if (depth === 0) return text.slice(start, i + 1);
    }
  }
  throw new Error("unterminated packed queue value");
}

function extractPair(text, marker) {
  const at = text.lastIndexOf(marker);
  if (at < 0) throw new Error("missing output marker " + JSON.stringify(marker));
  const start = text.indexOf("(", at + marker.length);
  if (start < 0) throw new Error("missing packed queue pair after output marker");
  return balancedValue(text, start);
}

function splitTopLevelPair(value) {
  const body = value.slice(1, -1);
  let parens = 0;
  let brackets = 0;
  let inString = false;
  let escaped = false;
  for (let i = 0; i < body.length; i++) {
    const c = body[i];
    if (inString) {
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') inString = false;
      continue;
    }
    if (c === '"') inString = true;
    else if (c === "(") parens++;
    else if (c === ")") parens--;
    else if (c === "[") brackets++;
    else if (c === "]") brackets--;
    else if (c === "," && parens === 0 && brackets === 0) {
      return [body.slice(0, i).trim(), body.slice(i + 1).trim()];
    }
  }
  throw new Error("packed queue is not a pair of lists");
}

function parsePackedList(source) {
  const text = source.trim();
  if (text === "[]") return [];
  if (!text.startsWith("[") || !text.endsWith("]")) {
    throw new Error("expected list notation, got " + text.slice(0, 80));
  }
  const body = text.slice(1, -1);
  const tuple = /\(\s*"([^"]*)"\s*,\s*(\d+)\s*,\s*(\d+)\s*\)/g;
  const nodes = [...body.matchAll(tuple)].map((m) => ({
    table: m[1],
    holes: Number(m[2]),
    fresh: Number(m[3]),
  }));
  const residue = body.replace(tuple, "").replace(/[;\s]/g, "");
  if (residue !== "") throw new Error("unparsed Coq list residue: " + residue.slice(0, 100));
  return nodes;
}

function validateNode(node, where) {
  const rows = node.table.split("_");
  if (rows.length !== 6 || rows.some((row) => row.length !== 6)) {
    throw new Error(where + ": malformed six-row table " + node.table);
  }
  const holes = [...node.table.matchAll(/---/g)].length;
  if (holes !== node.holes) {
    throw new Error(where + ": encoded hole count " + node.holes + ", table has " + holes);
  }
  const targets = new Set(["A"]); // the initial state is in the support
  for (const row of rows) {
    for (const slot of [row.slice(0, 3), row.slice(3, 6)]) {
      if (slot === "---") continue;
      if (!/^[01][LR][A-F]$/.test(slot)) {
        throw new Error(where + ": malformed transition " + slot + " in " + node.table);
      }
      targets.add(slot[2]);
    }
  }
  let fresh = 0;
  while (fresh < 6 && targets.has(STATES[fresh])) fresh++;
  if (fresh !== node.fresh) {
    throw new Error(where + ": encoded fresh state " + node.fresh + ", table implies " + fresh);
  }
  if (!Number.isInteger(node.fresh) || node.fresh < 0 || node.fresh > 6) {
    throw new Error(where + ": fresh-state metadata outside 0..6");
  }
}

function validateAssumptions(log, moduleName) {
  const start = log.lastIndexOf("Axioms:");
  if (start < 0) {
    if (log.includes("Closed under the global context")) return;
    throw new Error(moduleName + ": no closed-context or assumptions output found");
  }
  const end = log.indexOf("chunk_data =", start);
  const block = log.slice(start, end < 0 ? log.length : end);
  const allowed = (name) => name === "Nat.of_num_uint" ||
    name.startsWith("PrimInt63.") || name.startsWith("PArray.") || name.startsWith("Uint63.");
  const names = [];
  for (const line of block.split(/\r?\n/)) {
    if (!line.trim() || line.trim() === "Axioms:" || /^\s/.test(line)) continue;
    const name = line.trim().split(/[\s:]/)[0].replace(/\.$/, "");
    if (!allowed(name)) throw new Error(moduleName + ": unexpected assumption " + name);
    names.push(name);
  }
  if (!names.length) throw new Error(moduleName + ": empty or unreadable assumptions block");
  const standalone = log.split(/\r?\n/).map((line) => line.trim()).filter((line) => /^(\S+)\s*\.\s*\[/.test(line));
  for (const line of standalone) {
    const name = line.match(/^(\S+)/)[1].replace(/\.$/, "");
    if (!allowed(name)) throw new Error(moduleName + ": unexpected standalone assumption " + name);
  }
}
function parseLog(log, moduleName) {
  const value = extractPair(log, "chunk_data =");
  const pair = splitTopLevelPair(value);
  const active = parsePackedList(pair[0]);
  const held = parsePackedList(pair[1]);
  const summaryMatches = [...log.matchAll(/=\s*\((\d+)\s*,\s*(\d+)\)/g)];
  if (summaryMatches.length) {
    const last = summaryMatches[summaryMatches.length - 1];
    if (Number(last[1]) !== active.length || Number(last[2]) !== held.length) {
      throw new Error(moduleName + ": summary says (" + last[1] + "," + last[2] + ") but parsed (" + active.length + "," + held.length + ")");
    }
  }
  validateAssumptions(log, moduleName);
  [...active, ...held].forEach((node, i) => validateNode(node, moduleName + " residual " + i));
  return { active, held, valueSha256: sha256(value) };
}

function parseManifest(file) {
  const lines = fs.readFileSync(file, "utf8").trim().split(/\r?\n/);
  if (lines.shift() !== "offset\tsize\tfuel\tstatus") {
    throw new Error(file + ": unexpected manifest header");
  }
  return lines.filter(Boolean).map((line) => {
    const [offset, size, fuel, status] = line.split("\t");
    return { offset: Number(offset), size: Number(size), fuel: Number(fuel), status };
  });
}

function selfTest(repoRoot) {
  const file = path.join(repoRoot, "im-results/agent5-weighted-tnf-queue/Agent5PackedChunk12800_20_1000000.v");
  const source = fs.readFileSync(file, "utf8");
  const marker = "Definition packed_chunk_12800_20_1000000 : packed_queue :=";
  const value = extractPair(source, marker);
  const pair = splitTopLevelPair(value);
  const active = parsePackedList(pair[0]);
  const held = parsePackedList(pair[1]);
  [...active, ...held].forEach((node, i) => validateNode(node, "self-test residual " + i));
  if (active.length !== 56 || held.length !== 0) {
    throw new Error("self-test expected (56,0), got (" + active.length + "," + held.length + ")");
  }
  const syntheticLog = "Closed under the global context\\nNat.of_num_uint. [abstract-large-number,numbers,default]\\nAxioms:\\nPrimInt63.sub : primitive\\nPArray.set : primitive\\nchunk_data = " + value;
  const parsed = parseLog(syntheticLog, "self-test");
  if (parsed.active.length !== 56 || parsed.held.length !== 0) {
    throw new Error("self-test log parser returned the wrong queue lengths");
  }
  console.log("self-test: final-20 Coq value/log parser accepts 56 active, 0 held; all table metadata is consistent");
}

function main() {
  const args = process.argv.slice(2);
  if (args[0] === "--self-test") {
    selfTest(path.resolve(args[1] || process.cwd()));
    return;
  }
  const inputRoot = path.resolve(args[0] || ".");
  const outputRoot = path.resolve(args[1] || inputRoot);
  const manifests = walk(inputRoot).filter((p) => path.basename(p) === "manifest.tsv");
  if (!manifests.length) die("no manifest.tsv files under " + inputRoot);

  const chunks = [];
  const revisions = new Set();
  for (const manifestFile of manifests) {
    const dir = path.dirname(manifestFile);
    const originalRevision = fs.readFileSync(path.join(dir, "original-revision.txt"), "utf8").trim();
    const researchRevision = fs.readFileSync(path.join(dir, "research-revision.txt"), "utf8").trim();
    revisions.add(originalRevision + ":" + researchRevision);
    if (originalRevision !== PINNED_SOURCE) {
      throw new Error(manifestFile + ": source revision " + originalRevision + " differs from pinned " + PINNED_SOURCE);
    }
    for (const row of parseManifest(manifestFile)) {
      if (row.status !== "verified") throw new Error(manifestFile + ": chunk " + row.offset + " status " + row.status);
      const moduleName = "Agent8Batch_" + row.offset + "_" + row.size + "_" + row.fuel;
      const logFile = path.join(dir, moduleName + ".log");
      const sourceFile = path.join(dir, moduleName + ".v");
      if (!fs.existsSync(logFile) || !fs.existsSync(sourceFile)) {
        throw new Error(manifestFile + ": missing source/log for " + moduleName);
      }
      const source = fs.readFileSync(sourceFile, "utf8");
      if (!source.includes("Theorem chunk_data_exact") || !source.includes("source_checkpoint_decode")) {
        throw new Error(moduleName + ": missing source checkpoint exactness theorem");
      }
      if (/^\\s*(Admitted|Axiom)\\b/m.test(source)) {
        throw new Error(moduleName + ": source contains an admission or explicit axiom");
      }
      const log = fs.readFileSync(logFile, "utf8");
      const parsed = parseLog(log, moduleName);
      chunks.push({
        ...row,
        module: moduleName,
        active: parsed.active,
        held: parsed.held,
        activeCount: parsed.active.length,
        heldCount: parsed.held.length,
        logSha256: sha256(log),
        sourceSha256: sha256(source),
        valueSha256: parsed.valueSha256,
        originalRevision,
        researchRevision,
      });
    }
  }

  chunks.sort((a, b) => a.offset - b.offset);
  if (chunks.length !== 129) throw new Error("expected 129 chunks, found " + chunks.length);
  for (let i = 0; i < 129; i++) {
    const c = chunks[i];
    if (c.offset !== 100 * i || c.size !== 100) {
      throw new Error("chunk " + i + ": expected offset=" + (100 * i) + ", size=100; got offset=" + c.offset + ", size=" + c.size);
    }
  }
  if (revisions.size !== 1) throw new Error("mixed source/research revisions across batches: " + [...revisions].join(", "));

  const roster = [];
  const seen = new Map();
  let activeCount = 0;
  let heldCount = 0;
  for (let i = 0; i < chunks.length; i++) {
    const c = chunks[i];
    activeCount += c.activeCount;
    heldCount += c.heldCount;
    for (const [side, nodes] of [["active", c.active], ["held", c.held]]) {
      nodes.forEach((node, ordinal) => {
        const key = node.table + "\t" + node.holes + "\t" + node.fresh;
        seen.set(key, (seen.get(key) || 0) + 1);
        roster.push([i, c.offset, c.size, c.fuel, side, ordinal, node.holes, node.fresh, node.table].join("\t"));
      });
    }
  }
  const duplicateCount = [...seen.values()].reduce((n, k) => n + Math.max(0, k - 1), 0);
  const header = "chunk_index\toffset\tsize\tfuel\tqueue_side\tordinal\tholes\tfresh\ttable";
  fs.mkdirSync(outputRoot, { recursive: true });
  fs.writeFileSync(path.join(outputRoot, "q0-checkpoint-roster.tsv"), [header, ...roster].join("\n") + "\n");
  const summary = {
    sourceRevision: PINNED_SOURCE,
    researchRevision: chunks[0].researchRevision,
    chunkCount: chunks.length,
    requestedChunkSize: 100,
    q0Length: 12820,
    activeCount,
    heldCount,
    residualCount: activeCount + heldCount,
    uniqueResidualCount: seen.size,
    duplicateCount,
    chunks: chunks.map(({ active, held, ...rest }) => rest),
  };
  fs.writeFileSync(path.join(outputRoot, "q0-checkpoint-manifest.json"), JSON.stringify(summary, null, 2) + "\n");
  console.log(JSON.stringify({
    chunkCount: chunks.length,
    activeCount,
    heldCount,
    residualCount: activeCount + heldCount,
    uniqueResidualCount: seen.size,
    duplicateCount,
    output: outputRoot,
  }, null, 2));
}

try {
  main();
} catch (error) {
  die(error && error.stack ? error.stack : String(error));
}
