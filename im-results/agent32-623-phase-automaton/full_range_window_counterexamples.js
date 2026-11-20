#!/usr/bin/env node
"use strict";
const fs = require("node:fs");
const path = require("node:path");
const dfa = JSON.parse(fs.readFileSync(path.join(__dirname, "ResetPatternDFA.json"), "utf8"));
const accepting = new Set(dfa.accepting_states);
const mod3 = n => ((n % 3) + 3) % 3;
const pairText = z => String(Math.floor(z / 3)) + String(z % 3);
const stateKey = s => [s.xp,s.yp,s.a,s.b].join(",");
function step(branch,s,z) {
  const x=Math.floor(z/3),y=z%3;
  const tx=branch==="L"?x-s.yp+s.a:-x-s.xp-s.yp+s.a;
  const ty=branch==="L"?s.yp+s.b:s.xp+s.yp+s.b;
  return {next:{xp:x,yp:y,a:Math.floor(tx/3),b:Math.floor(ty/3)},
    output:3*mod3(tx)+mod3(ty)};
}
function inRectangle(branch,s) {
  const amin=branch==="L"?-2:-4,amax=branch==="L"?2:1;
  return s.a>=amin&&s.a<=amax&&s.b>=-2&&s.b<=2;
}
function allStarts(branch) {
  const amin=branch==="L"?-2:-4,amax=branch==="L"?2:1,out=[];
  for(let xp=0;xp<3;xp++)for(let yp=0;yp<3;yp++)
    for(let a=amin;a<=amax;a++)for(let b=-2;b<=2;b++)out.push({xp,yp,a,b});
  return out;
}
function firstResetEnd(word) {
  let s=dfa.initial_state;
  for(let i=0;i<word.length;i++){s=dfa.transitions[s][word[i]];if(accepting.has(s))return i+1;}
  return null;
}
function xNonmonochromatic(word) {
  const xs=word.map(z=>Math.floor(z/3));
  return xs.some(x=>x!==0)&&xs.some(x=>x!==2);
}
function verifyCommonReset(pattern) {
  const branches={};
  for(const branch of ["L","R"]) {
    let final=null,checked=0;
    for(const start of allStarts(branch)) {
      let s=start,flags=0;
      for(const z of pattern) {
        const r=step(branch,s,z);s=r.next;
        if(!inRectangle(branch,s))throw Error("reset leaves carry rectangle");
        const ox=Math.floor(r.output/3);
        if(ox!==0)flags|=1;if(ox!==2)flags|=2;
      }
      if(flags!==3)throw Error("reset fails x-output nonmonochromaticity");
      if(final===null)final=stateKey(s);else if(final!==stateKey(s))throw Error("reset fails to synchronize "+branch);
      checked++;
    }
    branches[branch]={starts_checked:checked,common_final_state:final};
  }
  const first=firstResetEnd(pattern);
  if(first!==pattern.length)throw Error("DFA did not accept reset at its end");
  return{first_accepting_end:first,branches};
}
function verifyCase(t) {
  const input=t.window.slice(),allInput=input.concat(t.extension===null?[]:[t.extension]);
  let s={...t.start};const output=[],trace=[];
  for(const z of allInput) {
    const r=step(t.branch,s,z);s=r.next;
    if(!inRectangle(t.branch,s))throw Error("trajectory leaves full carry rectangle");
    output.push(r.output);trace.push([s.a,s.b]);
  }
  const target=output.slice(t.kShift),high=t.extension===null?0:1;
  const inputReset=firstResetEnd(input),targetReset=firstResetEnd(target);
  const inputNonmono=xNonmonochromatic(input),targetNonmono=xNonmonochromatic(target);
  if(input.length!==8||target.length!==8+high-t.kShift)throw Error("window length mismatch");
  if(inputReset===null||inputReset>13)throw Error("input has no reset by symbol 13");
  if(targetReset!==null)throw Error("target unexpectedly resets");
  if(!inputNonmono||!targetNonmono)throw Error("input or target x-block is monochromatic");
  if(![[0,0],[0,1],[1,1]].some(p=>p[0]===t.kShift&&p[1]===high))throw Error("invalid shift");
  return{
    source_sector:t.sourceSector,branch:t.branch,shift:[t.kShift,high],start:t.start,
    input_window:input.map(pairText),high_extension:t.extension===null?null:pairText(t.extension),
    input_first_reset_end:inputReset,input_x_nonmonochromatic:inputNonmono,
    target_window:target.map(pairText),target_reset_end:targetReset,
    target_x_nonmonochromatic:targetNonmono,all_carries_in_full_rectangle:true,carry_trace:trace
  };
}
const patterns=[{name:"00 02 00",word:[0,2,0]},{name:"00 01 00",word:[0,1,0]}];
const resetChecks=patterns.map(p=>({pattern:p.name,verification:verifyCommonReset(p.word)}));
const cases=[
 {sourceSector:"LO",branch:"L",start:{xp:0,yp:0,a:-2,b:-2},window:[0,2,0,3,6,0,6,0],extension:null,kShift:0},
 {sourceSector:"LO",branch:"L",start:{xp:0,yp:0,a:-2,b:-2},window:[0,2,0,3,6,0,6,0],extension:0,kShift:0},
 {sourceSector:"LO",branch:"L",start:{xp:0,yp:0,a:-2,b:-2},window:[0,2,0,0,0,0,0,3],extension:0,kShift:1},
 {sourceSector:"RO",branch:"R",start:{xp:0,yp:0,a:-4,b:-2},window:[0,1,0,6,3,6,0,3],extension:null,kShift:0},
 {sourceSector:"RO",branch:"R",start:{xp:0,yp:0,a:-4,b:-2},window:[0,1,0,6,3,6,0,3],extension:0,kShift:0},
 {sourceSector:"RO",branch:"R",start:{xp:0,yp:0,a:-4,b:-2},window:[0,1,0,6,0,0,6,0],extension:0,kShift:1},
];
const results=cases.map(verifyCase);
console.log(JSON.stringify({title:"Full-range eight-symbol S-window reset counterexamples",
 reset_pattern_checks:resetChecks,cases_checked:results.length,results},null,2));
