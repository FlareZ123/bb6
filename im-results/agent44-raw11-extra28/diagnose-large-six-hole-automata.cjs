'use strict';

const fs = require('node:fs');
const path = require('node:path');
const { cert } = require('../agent47-raw11-adapter/generate-q0-lean.cjs');

const dir = process.argv[2];
if (!dir) throw new Error('usage: node diagnose-large-six-hole-automata.cjs <six-hole-dir>');

const rows = [];
for (const file of fs.readdirSync(dir).filter(f => /^six-hole-scan-\d+\.json$/.test(f)).sort()) {
  const data = JSON.parse(fs.readFileSync(path.join(dir, file), 'utf8'));
  for (const row of data.rows || []) {
    for (const item of row.certs || []) {
      const c = item.cert;
      if (!c || !c.table) continue;
      const lean = cert(c);
      rows.push({
        file,
        parentId: row.id,
        table: c.table,
        kind: c.kind,
        k: c.k,
        mirror: c.mirror,
        cap: c.cap,
        depth: c.depth,
        certLeanBytes: Buffer.byteLength(lean),
        jsonBytes: Buffer.byteLength(JSON.stringify(c)),
        leftStates: c.left?.push?.length,
        rightStates: c.right?.push?.length,
        transitionRows: c.rows?.length,
      });
    }
  }
}
rows.sort((a,b) => b.certLeanBytes - a.certLeanBytes || a.table.localeCompare(b.table));
console.log(JSON.stringify({count: rows.length, top: rows.slice(0,30)}, null, 2));
