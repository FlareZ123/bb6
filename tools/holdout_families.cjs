"use strict";

/**
 * List rooted and unrooted transition-table isomorphism families.
 * Only state renaming and left/right reflection are allowed.
 * Blank symbol 0 is fixed. The rooted form fixes initial state A.
 * Runtime: Node.js (CommonJS), usage: node holdout_families.cjs INPUT.txt
 */
const fs = require("node:fs");

/** @param {number[]} a @param {number[]} remaining @param {number[][]} out */
function enumerate(a, remaining, out) {
  if (!remaining.length) { out.push(a); return; }
  for (let i=0; i<remaining.length; i++) {
    enumerate([...a, remaining[i]], remaining.filter((_,j)=>j!==i), out);
  }
}
const perms=[];
enumerate([],[0,1,2,3,4,5],perms);

/** @param {string} s */
function parse(s) {
  if (!/^(?:[01][LR][A-F]|---){2}(?:_(?:[01][LR][A-F]|---){2}){5}$/.test(s))
    throw new Error("Invalid RLE: "+s);
  return s.split("_").map(r=>[r.slice(0,3),r.slice(3,6)]);
}

/** @param {string[][]} table @param {number[]} order @param {boolean} reflect */
function changeLabels(table, order, reflect) {
  const inverse=Array(6);
  for(let i=0;i<6;i++) inverse[order[i]]=i;
  const encode=t=>t==="---"?"---":t[0]+
    (reflect ? (t[1]==="L"?"R":"L"):t[1])+
    String.fromCharCode(65+inverse[t.charCodeAt(2)-65]);
  return { code:order.map(old=>table[old].map(encode).join("")).join("_"),
    start:inverse[0] };
}

/** @param {string} machine */
function normalize(machine) {
  const table=parse(machine);
  let best,rooted;
  for(const order of perms) {
    for(const reflect of [false,true]) {
      const t=changeLabels(table,order,reflect);
      if(!best||t.code<best.normalized||(t.code===best.normalized&&t.start<best.start))
        best={machine,normalized:t.code,start:t.start,reflect,order};
      if(order[0]===0 && (rooted===undefined||t.code<rooted)) rooted=t.code;
    }
  }
  return {...best,rooted};
}

function main() {
  const args=process.argv.slice(2);
  if(args.length!==1) throw new Error("Expected one RLE list file");
  const input=fs.readFileSync(args[0],"utf8").trim().split(/\s+/);
  if(new Set(input).size!==input.length) throw new Error("Duplicate machine string");
  const entries=input.map(normalize);
  const grouped=new Map();
  for(const item of entries) {
    const group=grouped.get(item.normalized)||[];
    group.push(item);grouped.set(item.normalized,group);
  }
  const nontrivial=[...grouped].filter(([,v])=>v.length>1);
  const sizes=[...grouped.values()].map(x=>x.length).sort((a,b)=>b-a);
  const results={
    entries:input.length, rootedClasses:new Set(entries.map(x=>x.rooted)).size,
    tableFamilies:grouped.size,multiStartFamilies:nontrivial.length,
    membersInMultiStartFamilies:nontrivial.reduce((n,[,v])=>n+v.length,0),
    largestFamilySize:sizes[0],
    familySizes:Object.fromEntries([...new Set(sizes)].sort((a,b)=>a-b).map(size=>
      [size,sizes.filter(x=>x===size).length])),
    witnesses:nontrivial.map(([table,items])=>({table,items:items.map(x=>({
      rle:x.machine,canonicalStart:x.start,reflect:x.reflect,order:x.order
    }))}))
  };
  console.log(JSON.stringify(results,null,2));
}
if(require.main===module) main();
module.exports={parse,changeLabels,normalize};
