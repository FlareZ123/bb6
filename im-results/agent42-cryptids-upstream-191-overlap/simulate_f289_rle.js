// Deterministic JavaScript/BigInt port of the Cryptids RLE state engine
// for either F289 rooted RLE module with the shared primitive rule-cost signature.
// Requires Node.js with BigInt support.
// Usage: node simulate_f289_rle.js /path/to/M_<F289-rooted-RLE>.lean
//
// Source basis: google-deepmind/cryptids commit
// 3647718b5df22e1a61462dec0376bd204526285a, BusyBeaver/Calculi/HaltShared.lean.
// This script validates state updates against the proof's checkpoints and
// accumulates manually derived primitive-step upper bounds. It is NOT a
// formal proof that those costs are sound for the primitive TM relation.

'use strict';
const fs = require('node:fs');
const assert = require('node:assert/strict');
const proofPath = process.argv[2];
if (!proofPath) throw new Error('pass the upstream F289 Lean proof file path');
const source = fs.readFileSync(proofPath, 'utf8');
const lines = source.split(/\r?\n/);

function checkpoint(name) {
  const i = lines.findIndex(x => x.startsWith('def ' + name + ' : RleFullState'));
  if (i < 0) throw new Error('missing checkpoint ' + name);
  const j = lines.findIndex((x,k) => k > i && /^(def|theorem) /.test(x));
  return lines.slice(i, j < 0 ? lines.length : j).join('\n').split(':=').slice(1).join(':=').trim();
}
const tokenRE = /⟨|⟩|\[|\]|\(|\)|,|\.DR0|\.BR|\.B|\.C|\.raw|\.clean|\.z|\.d|\.k|false|true|\d+/g;
function parseState(text) {
  const t = text.match(tokenRE);
  let p = 0;
  const take = () => t[p++];
  const expect = x => { const a = take(); if (a !== x) throw new Error('expected ' + x + ', got ' + a); };
  const nat = () => BigInt(take());
  const parseItems = () => {
    expect('['); const a = [];
    while (t[p] !== ']') {
      const tag = take();
      if (tag === '.z') a.push({t:'z',c:nat()});
      else if (tag === '.d') a.push({t:'d',v:nat()});
      else if (tag === '.k') a.push({t:'k',r:nat(),c:nat()});
      else throw new Error('bad item ' + tag);
      if (t[p] === ',') take(); else break;
    }
    expect(']'); return a;
  };
  const parsePairs = () => {
    expect('['); const a = [];
    while (t[p] !== ']') {
      expect('('); const r = nat(); expect(','); const c = nat(); expect(')');
      a.push([r,c]); if (t[p] === ',') take(); else break;
    }
    expect(']'); return a;
  };
  expect('⟨'); const mode = take().slice(1); expect(',');
  const lk = take(); let ls;
  if (lk === '.raw') ls = {t:'raw',items:parseItems()};
  else if (lk === '.clean') ls = {t:'clean',c0:nat(),segs:parsePairs(),bot:nat()};
  else throw new Error('bad LState ' + lk);
  expect(','); const R = parseItems(); expect(',');
  const halted = take() === 'true'; expect('⟩');
  return {mode,ls,R,halted};
}

const z = c => ({t:'z',c}), d = v => ({t:'d',v}), k = (r,c) => ({t:'k',r,c});
const pushL0 = (c,L) => c===0n ? L : L[0]?.t==='z' ? [z(c+L[0].c),...L.slice(1)] : [z(c),...L];
const pushLk2 = (r,c,L) => c===0n ? L : L[0]?.t==='k' && L[0].r===r ? [k(r,c+L[0].c),...L.slice(1)] : [k(r,c),...L];
function pushLd(v,L) {
  if (v===0n) return pushL0(1n,L);
  if (v===1n) {
    if (L[0]?.t==='z' && L[1]?.t==='d' && L[1].v===1n && L[0].c>=2n)
      return [d(1n),...pushLk2(L[0].c-2n,1n,L.slice(2))];
    return [d(1n),...L];
  }
  return [d(v),...L];
}
const popKTail = (r,c,xs) => c===1n ? xs : [k(r,c-1n),...xs];
function popL1(L) {
  if (!L.length) return null;
  const [h,...xs] = L;
  if (h.t==='z') {
    if (h.c===0n) return popL1(xs);
    if (h.c===1n) return [0n,xs];
    return [0n,[z(h.c-1n),...xs]];
  }
  if (h.t==='k') {
    if (h.c===0n) return popL1(xs);
    return [0n,pushL0(h.r+1n,pushLd(1n,popKTail(h.r,h.c,xs)))];
  }
  return [h.v,xs];
}
const bumpL = L => { const p=popL1(L); return p===null ? [z(1n)] : pushLd(p[0]+1n,p[1]); };
const pushR0 = (c,R) => c===0n ? R : R[0]?.t==='z' ? [z(c+R[0].c),...R.slice(1)] : [z(c),...R];
function mergeRk2Pre(r,c,R) {
  if (r>=1n && R[0]?.t==='z' && R[1]?.t==='d' && R[2]?.t==='d' &&
      R[0].c===r && R[1].v===2n && R[2].v===1n) return [c+1n,R.slice(3)];
  return [c,R];
}
function pushRk2(r,c,R) {
  if (c===0n) return R;
  const p=mergeRk2Pre(r,c,R), tail=p[1];
  return tail[0]?.t==='k' && tail[0].r===r
    ? [k(r,p[0]+tail[0].c),...tail.slice(1)] : [k(r,p[0]),...tail];
}
function pushRd(v,R) {
  if (v===0n) return pushR0(1n,R);
  if (v===2n) return R[0]?.t==='d' && R[0].v===1n ? pushRk2(0n,1n,R.slice(1)) : [d(2n),...R];
  return [d(v),...R];
}
function popR1(R) {
  if (!R.length) return null;
  const [h,...xs]=R;
  if (h.t==='z') {
    if (h.c===0n) return popR1(xs);
    if (h.c===1n) return [0n,xs];
    return [0n,[z(h.c-1n),...xs]];
  }
  if (h.t==='k') {
    if (h.c===0n) return popR1(xs);
    if (h.r===0n) return [2n,[d(1n),...popKTail(h.r,h.c,xs)]];
    return [0n,pushR0(h.r-1n,[d(2n),d(1n),...popKTail(h.r,h.c,xs)])];
  }
  return [h.v,xs];
}
const bumpR = R => { const p=popR1(R); return p===null ? [z(1n)] : pushRd(p[0]+1n,p[1]); };
const pushSeg = (r,c,segs) => c===0n ? segs : segs[0]?.[0]===r ? [[r,c+segs[0][1]],...segs.slice(1)] : [[r,c],...segs];
function segsToItems(segs,acc) {
  let out=acc;
  for (let i=segs.length-1;i>=0;i--) { const [r,c]=segs[i]; if(c!==0n) out=[k(r,c),...out]; }
  return out;
}
const unpackClean = (c0,segs,bot) => {
  const tail=segsToItems(segs,[z(bot+2n)]);
  return c0===0n ? [d(1n),...tail] : [z(c0),d(1n),...tail];
};
function packTail(cur0,items) {
  if (!items.length) return cur0>=2n ? [[],cur0-2n] : null;
  const [h,...rest]=items;
  if (h.t==='z') return packTail(cur0+h.c,rest);
  if (h.t==='d') {
    if (h.v!==1n || cur0<2n) return null;
    const p=packTail(0n,rest); return p===null ? null : [pushSeg(cur0-2n,1n,p[0]),p[1]];
  }
  if (h.c===0n) return packTail(cur0,rest);
  const p=packTail(0n,rest);
  return p===null ? null : [pushSeg(cur0+h.r,1n,pushSeg(h.r,h.c-1n,p[0])),p[1]];
}
function packHead(cur0,items) {
  if (!items.length) return null;
  const [h,...rest]=items;
  if (h.t==='z') return packHead(cur0+h.c,rest);
  if (h.t==='d') {
    if (h.v!==1n) return null;
    const p=packTail(0n,rest);
    return p===null ? null : {t:'clean',c0:cur0,segs:p[0],bot:p[1]};
  }
  if (h.c===0n) return packHead(cur0,rest);
  const p=packTail(0n,rest);
  return p===null ? null : {t:'clean',c0:cur0+h.r+2n,segs:pushSeg(h.r,h.c-1n,p[0]),bot:p[1]};
}
const isTopD1 = items => items[0]?.t==='d' && items[0].v===1n;
function tryPack(mode,items,R) {
  const can = mode==='B' ? (!R.length || isTopD1(items)) : mode==='BR' ? !R.length : mode==='DR0';
  if (!can) return null;
  const p=packHead(0n,items);
  return p && p.bot>=1n ? p : null;
}
const st = (mode,ls,R,halted=false) => ({mode,ls,R,halted});
function stepRawB(items,R) {
  if (!R.length) return st('C',{t:'raw',items:bumpL(items)},[],false);
  if (R[0].t==='z') return st('B',{t:'raw',items:pushL0(R[0].c,items)},R.slice(1),false);
  const p=popR1(R);
  if (p===null) return st('C',{t:'raw',items:bumpL(items)},[],false);
  if (p[0]===0n) return st('B',{t:'raw',items:pushL0(1n,items)},p[1],false);
  return st('BR',{t:'raw',items},pushR0(1n,pushRd(p[0]-1n,p[1])),false);
}
function stepRawBRPop(items,R) {
  const p=popR1(R);
  if (p===null) return st('C',{t:'raw',items:bumpL(items)},[],false);
  if (p[0]===0n) return st('BR',{t:'raw',items:pushL0(1n,items)},p[1],false);
  if (p[0]===1n) return st('DR0',{t:'raw',items},bumpR(p[1]),false);
  return st('B',{t:'raw',items:bumpL(items)},pushRd(p[0]-2n,p[1]),false);
}
function stepRawBR(items,R) {
  if (!R.length) return st('C',{t:'raw',items:bumpL(items)},[],false);
  if (R[0].t==='z') return st('BR',{t:'raw',items:pushL0(R[0].c,items)},R.slice(1),false);
  if (R[0].t==='k') {
    const r=R[0].r,m=R[0].c;
    if (m>=1n) {
      const p=popL1(items);
      if (p!==null && p[0]===0n)
        return st('BR',{t:'raw',items:pushL0(3n,pushLd(1n,pushLk2(r,m-1n,pushL0(r,p[1]))))},R.slice(1),false);
      return stepRawBRPop(items,R);
    }
    return st('BR',{t:'raw',items},R.slice(1),false);
  }
  return stepRawBRPop(items,R);
}
function stepRawDR0Atomic(items,R) {
  const p=popL1(items);
  if (p===null) return st('C',{t:'raw',items:[d(1n)]},R,false);
  if (p[0]===0n) {
    if (items[0]?.t==='z') return st('DR0',{t:'raw',items:items.slice(1)},pushR0(items[0].c,R),false);
    return st('DR0',{t:'raw',items:p[1]},pushR0(1n,R),false);
  }
  return st('C',{t:'raw',items:pushLd(p[0]-1n,p[1])},pushR0(1n,R),false);
}
function stepRawDR0(items,R) {
  if (items.length===1 && items[0].t==='z') {
    const c=items[0].c;
    if (R[0]?.t==='d' && R[1]?.t==='z') {
      if (R[0].v===1n) return st('DR0',{t:'raw',items:[z(c+3n*R[1].c)]},[d(1n),...R.slice(2)],false);
      return st('BR',{t:'raw',items:[z(c+3n)]},R,false);
    }
    return st('BR',{t:'raw',items:[z(c+3n)]},R,false);
  }
  return stepRawDR0Atomic(items,R);
}
function stepRawCAtomic(items,R) {
  const p=popL1(items);
  if (p===null) return st('DR0',{t:'raw',items:[]},R,false);
  if (p[0]===0n) {
    const p2=popL1(p[1]);
    if (p2===null) return st('C',{t:'raw',items:[]},pushRd(1n,R),false);
    if (p2[0]===0n) return st('C',{t:'raw',items:bumpL(p2[1])},pushRd(1n,R),false);
    if (p2[0]===1n) return st('C',{t:'raw',items:bumpL(bumpL(p2[1]))},pushR0(1n,bumpR(R)),false);
    return st('BR',{t:'raw',items:pushLd(p2[0]-2n,p2[1])},pushR0(1n,pushRd(1n,R)),false);
  }
  if (p[0]===1n) {
    const p2=popL1(p[1]);
    if (p2===null) return st('B',{t:'raw',items:[z(1n)]},pushRd(1n,R),false);
    if (p2[0]===0n) return st('DR0',{t:'raw',items:p2[1]},pushRd(2n,R),false);
    return st('C',{t:'raw',items:pushLd(p2[0]-1n,p2[1])},pushRd(2n,R),false);
  }
  return st('C',{t:'raw',items:pushLd(p[0],p[1])},R,true);
}
function stepRawC(items,R) {
  if (items[0]?.t==='z' && items[1]?.t==='k') {
    const cz=items[0].c,r=items[1].r,m=items[1].c,L2=items.slice(2);
    if (cz===1n) return st('C',{t:'raw',items:pushL0(1n,L2)},pushRk2(r,m,R),false);
  }
  if (items[0]?.t==='z' && items[1]?.t==='d') {
    const cz=items[0].c,v1=items[1].v,L2=items.slice(2);
    if (cz>=4n && v1===1n) return st('C',{t:'raw',items:pushL0(1n,L2)},pushRk2(cz-3n,1n,R),false);
  }
  if (items.length===1 && items[0].t==='z' && items[0].c>=4n)
    return st('DR0',{t:'raw',items:[]},pushRk2(items[0].c-4n,1n,R),false);
  return stepRawCAtomic(items,R);
}
function stepCleanBPop(c0,segs,bot,R) {
  const p=popR1(R);
  if (p===null) return st('B',{t:'raw',items:unpackClean(c0,segs,bot)},R,false);
  if (p[0]===0n) return st('B',{t:'clean',c0:c0+1n,segs,bot},p[1],false);
  return st('BR',{t:'clean',c0,segs,bot},pushR0(1n,pushRd(p[0]-1n,p[1])),false);
}
function stepCleanB(c0,segs,bot,R) {
  if (!R.length) {
    if (c0>=1n && bot>=1n) return st('B',{t:'clean',c0:1n,segs:pushSeg(0n,bot-1n,pushSeg(c0-1n,1n,segs)),bot:0n},[],false);
    return st('B',{t:'raw',items:unpackClean(c0,segs,bot)},[],false);
  }
  if (R[0].t==='z' && R[1]?.t==='k') {
    const cz=R[0].c,r=R[1].r,cnt=R[1].c;
    if (c0===0n && bot>=1n && cz===1n) {
      const q=cnt<bot?cnt:bot;
      if (q>=1n) {
        const Rnew=cnt===q?[z(1n),...R.slice(2)]:[z(1n),k(r,cnt-q),...R.slice(2)];
        return st('B',{t:'clean',c0:0n,segs:pushSeg(r+3n,q,segs),bot:bot-q},Rnew,false);
      }
      return st('B',{t:'clean',c0:c0+cz,segs,bot},[k(r,cnt),...R.slice(2)],false);
    }
    return st('B',{t:'clean',c0:c0+cz,segs,bot},[k(r,cnt),...R.slice(2)],false);
  }
  if (R[0].t==='z') return st('B',{t:'clean',c0:c0+R[0].c,segs,bot},R.slice(1),false);
  if (R[0].t==='d' && R[1]?.t==='d' && R[2]?.t==='k') {
    const v1=R[0].v,v2=R[1].v,r=R[2].r,cnt=R[2].c;
    if (c0===0n && v1===1n && v2===1n) {
      const q=cnt<(bot/(r+1n))?cnt:(bot/(r+1n));
      if (q>=1n) {
        const Rnew=cnt===q?[d(1n),d(1n),...R.slice(3)]:[d(1n),d(1n),k(r,cnt-q),...R.slice(3)];
        return st('B',{t:'clean',c0:0n,segs:pushSeg(4n*r+3n,q,segs),bot:bot-q*(r+1n)},Rnew,false);
      }
      return st('BR',{t:'clean',c0,segs,bot},pushR0(1n,pushRd(0n,[d(v2),k(r,cnt),...R.slice(3)])),false);
    }
    return stepCleanBPop(c0,segs,bot,R);
  }
  return stepCleanBPop(c0,segs,bot,R);
}
function stepCleanBR(c0,segs,bot,R) {
  if (!R.length) {
    if (c0>=1n && bot>=1n) return st('B',{t:'clean',c0:1n,segs:pushSeg(0n,bot-1n,pushSeg(c0-1n,1n,segs)),bot:0n},[],false);
    return st('BR',{t:'raw',items:unpackClean(c0,segs,bot)},[],false);
  }
  if (R[0].t==='z') return st('BR',{t:'clean',c0:c0+R[0].c,segs,bot},R.slice(1),false);
  if (R[0].t==='k') {
    const r=R[0].r,m=R[0].c;
    if (m>=1n && c0>=1n && r+c0>=3n)
      return st('BR',{t:'clean',c0:3n,segs:pushSeg(r,m-1n,pushSeg(r+c0-3n,1n,segs)),bot},R.slice(1),false);
    return st('BR',{t:'raw',items:unpackClean(c0,segs,bot)},R,false);
  }
  const p=popR1(R);
  if (p===null) return st('BR',{t:'raw',items:unpackClean(c0,segs,bot)},R,false);
  if (p[0]===0n) return st('BR',{t:'clean',c0:c0+1n,segs,bot},p[1],false);
  if (p[0]===1n) return st('DR0',{t:'clean',c0,segs,bot},bumpR(p[1]),false);
  if (c0>=3n) return st('B',{t:'clean',c0:0n,segs:pushSeg(c0-3n,1n,segs),bot},pushRd(p[0]-2n,p[1]),false);
  return st('BR',{t:'raw',items:unpackClean(c0,segs,bot)},R,false);
}
function stepCleanDR0(c0,segs,bot,R) {
  if (bot>=1n) {
    if (R[0]?.t==='d' && R[1]?.t==='z') {
      if (R[0].v===1n) {
        const q=R[1].c<bot?R[1].c:bot;
        if (q>=1n) {
          const Rnew=R[1].c===q?[d(1n),...R.slice(2)]:[d(1n),z(R[1].c-q),...R.slice(2)];
          return st('DR0',{t:'clean',c0:c0+4n*q,segs,bot:bot-q},Rnew,false);
        }
        return st('BR',{t:'clean',c0:c0+4n,segs,bot:bot-1n},R,false);
      }
      return st('BR',{t:'clean',c0:c0+4n,segs,bot:bot-1n},R,false);
    }
    return st('BR',{t:'clean',c0:c0+4n,segs,bot:bot-1n},R,false);
  }
  return st('DR0',{t:'raw',items:unpackClean(c0,segs,bot)},R,false);
}
function rleStep(s) {
  if (s.ls.t==='raw') {
    const p=tryPack(s.mode,s.ls.items,s.R);
    if (p!==null) return st(s.mode,p,s.R,false);
    switch(s.mode) {
      case 'B': return stepRawB(s.ls.items,s.R);
      case 'BR': return stepRawBR(s.ls.items,s.R);
      case 'DR0': return stepRawDR0(s.ls.items,s.R);
      case 'C': return stepRawC(s.ls.items,s.R);
    }
  } else {
    const {c0,segs,bot}=s.ls;
    switch(s.mode) {
      case 'B': return stepCleanB(c0,segs,bot,s.R);
      case 'BR': return stepCleanBR(c0,segs,bot,s.R);
      case 'DR0': return stepCleanDR0(c0,segs,bot,s.R);
      case 'C': return st('C',{t:'raw',items:unpackClean(c0,segs,bot)},s.R,false);
    }
  }
  throw new Error('bad mode');
}

// Upper bounds derived from the execute-counted primitive rule proofs in HaltShared.
const segWeight = segs => segs.reduce((a,[r,c])=>a+c*(6n*r+30n),0n);
const cleanDR0One = (c0,bot,S) => 6n*c0+6n*bot+46n+S;
const cleanDR0Zeros = (q,c0,bot,S) => 6n*q*(c0+bot)+15n*q*q+41n*q+q*S;
const cleanRNILOne = (c0,bot,S) => 6n*c0+6n*bot+61n+S;
const cleanRNILZeroPow = (q,bot,S) => 6n*q*bot+18n*q*q+49n*q+q*S;
const cleanP1Pow = (q,r,bot,S) => q*(10n*r+6n*bot+6n*q+75n+S)+(6n*r+42n)*q*(q-1n)/2n;
const cleanP2Pow = (q,r,bot,S) => q*(15n*r*r+113n*r+165n)+(6n*r+12n)*(q*bot+(r+1n)*q*(q+1n)/2n)+(r+2n)*(q*S+(24n*r+48n)*q*(q-1n)/2n);
const ruleDR0Bot = c => 6n*c+14n;
const ruleDR0BotZeros = (q,c) => 6n*c*q+9n*q*q+9n*q;
function rleStepBound(s) {
  if (s.halted) return 0n;
  if (s.ls.t==='raw') {
    const items=s.ls.items,R=s.R,p=tryPack(s.mode,items,R);
    if (p!==null) return 0n;
    if (s.mode==='B') {
      if (!R.length) return 1n;
      if (R[0].t==='z') return 4n*R[0].c;
      const x=popR1(R); return x===null?1n:x[0]===0n?4n:2n;
    }
    if (s.mode==='BR') {
      if (!R.length) return 1n;
      if (R[0].t==='z') return 2n*R[0].c;
      if (R[0].t==='k') {
        const m=R[0].c,r=R[0].r;
        if (m===0n) return 0n;
        const x=popL1(items); if (x!==null && x[0]===0n) return m*(2n*r+15n);
      }
      const x=popR1(R); return x===null?1n:x[0]===0n?2n:x[0]===1n?4n:5n;
    }
    if (s.mode==='DR0') {
      if (items.length===1 && items[0].t==='z') {
        const c=items[0].c;
        if (R[0]?.t==='d' && R[1]?.t==='z' && R[0].v===1n) return ruleDR0BotZeros(R[1].c,c);
        return ruleDR0Bot(c);
      }
      const x=popL1(items);
      if (x===null) return 3n;
      if (x[0]===0n) return items[0]?.t==='z'?4n*items[0].c:4n;
      return 3n;
    }
    if (s.mode==='C') {
      if (items[0]?.t==='z' && items[1]?.t==='k' && items[0].c===1n) return items[1].c*(4n*items[1].r+15n);
      if (items[0]?.t==='z' && items[1]?.t==='d' && items[0].c>=4n && items[1].v===1n) return 4n*(items[0].c-3n)+15n;
      if (items.length===1 && items[0].t==='z' && items[0].c>=4n) return 4n*(items[0].c-4n)+12n;
      const x=popL1(items);
      if (x===null) return 1n;
      if (x[0]===0n) { const y=popL1(x[1]); return y===null?3n:y[0]===0n?5n:y[0]===1n?17n:4n; }
      if (x[0]===1n) { const y=popL1(x[1]); return y===null?5n:y[0]===0n?7n:6n; }
      return 3n;
    }
  } else {
    const {c0,segs,bot}=s.ls,R=s.R,S=segWeight(segs);
    if (s.mode==='B') {
      if (!R.length) {
        if (c0>=1n && bot>=1n) return cleanRNILOne(c0-1n,bot-1n,S)+cleanRNILZeroPow(bot-1n,0n,S+6n*(c0-1n)+30n);
        return 0n;
      }
      if (R[0].t==='z') {
        if (R[1]?.t==='k' && c0===0n && bot>=1n && R[0].c===1n) {
          const q=R[1].c<bot?R[1].c:bot;
          if (q>=1n) return cleanP1Pow(q,R[1].r,bot-q,S);
        }
        return 4n*R[0].c;
      }
      if (R[0].t==='d' && R[1]?.t==='d' && R[2]?.t==='k' && c0===0n && R[0].v===1n && R[1].v===1n) {
        const r=R[2].r,cnt=R[2].c,q=cnt<(bot/(r+1n))?cnt:(bot/(r+1n));
        if (q>=1n) return cleanP2Pow(q,r,bot-q*(r+1n),S);
        return 2n;
      }
      const x=popR1(R); return x===null?0n:x[0]===0n?4n:2n;
    }
    if (s.mode==='BR') {
      if (!R.length) {
        if (c0>=1n && bot>=1n) return cleanRNILOne(c0-1n,bot-1n,S)+cleanRNILZeroPow(bot-1n,0n,S+6n*(c0-1n)+30n);
        return 0n;
      }
      if (R[0].t==='z') return 2n*R[0].c;
      if (R[0].t==='k') {
        const r=R[0].r,m=R[0].c;
        return m>=1n && c0>=1n && r+c0>=3n ? m*(2n*r+15n) : 0n;
      }
      const x=popR1(R); return x===null?0n:x[0]===0n?2n:x[0]===1n?4n:c0>=3n?5n:0n;
    }
    if (s.mode==='DR0') {
      if (bot===0n) return 0n;
      if (R[0]?.t==='d' && R[1]?.t==='z' && R[0].v===1n) {
        const q=R[1].c<bot?R[1].c:bot;
        if (q>=1n) return cleanDR0Zeros(q,c0,bot-q,S);
      }
      return cleanDR0One(c0,bot-1n,S);
    }
    if (s.mode==='C') return 0n;
  }
  throw new Error('bad mode cost');
}
function runSteps(n,s) {
  let cost=0n;
  for(let i=0;i<n;i++) { if(s.halted) break; cost+=rleStepBound(s); s=rleStep(s); }
  return [s,cost];
}
function runBatches(b,s) {
  let cost=0n;
  for(let i=0;i<b;i++) { const p=runSteps(25,s); s=p[0]; cost+=p[1]; }
  return [s,cost];
}
const stable = s => JSON.stringify(s,(k,v)=>typeof v==='bigint'?v.toString():v);
const machineMatch=source.match(/load_rle_machine%\s+"([^"]+)"/);
if (!machineMatch) throw new Error('could not identify source machine RLE');
const machineRLE=machineMatch[1];
const allowedRLEs=[
  '1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH',
  '1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH'
];
assert.ok(allowedRLEs.includes(machineRLE),'this cost table is only checked for the two F289 RLE modules');
const expectedRuleCosts = {
  rule_B_nil:1, rule_B_zero:4, rule_B_succ:2,
  rule_BR_nil:1, rule_BR_zero:2, rule_BR_one:4, rule_BR_add_two:5,
  rule_DR0_nil:3, rule_DR0_zero:4, rule_DR0_succ:3,
  rule_C_nil:1, rule_C_zero_nil:3, rule_C_zero_zero:5, rule_C_zero_one:17,
  rule_C_zero_add_two:4, rule_C_one_nil:5, rule_C_one_zero:7,
  rule_C_one_succ:6, rule_C_add_two_step:3
};
function theoremBlock(name) {
  const i=lines.findIndex(x=>x.startsWith('theorem '+name+' '));
  if(i<0) throw new Error('missing primitive rule theorem '+name);
  const j=lines.findIndex((x,k)=>k>i && /^(private )?(theorem|def|abbrev|opaque|instance) /.test(x));
  return lines.slice(i,j<0?lines.length:j).join('\n');
}
function namedRuleCost(name) {
  const block=theoremBlock(name);
  const match=block.match(/execute ([0-9]+)/);
  if(match) return Number(match[1]);
  if(name==='rule_BR_nil' && block.includes('rule_B_nil L')) return namedRuleCost('rule_B_nil');
  throw new Error('could not extract primitive cost for '+name);
}
const ruleCostAudit=Object.fromEntries(Object.entries(expectedRuleCosts).map(([name,expected])=>{
  const actual=namedRuleCost(name);
  assert.equal(actual,expected,'primitive cost changed for '+name);
  return [name,actual];
}));
const initCostMatch=theoremBlock('init_reaches_stack').match(/execute ([0-9]+)/);
assert.ok(initCostMatch,'missing initial source-to-stack execution cost');
const initialPrimitiveStepBound=BigInt(initCostMatch[1]);
assert.equal(initialPrimitiveStepBound,1n,'initial source-to-stack cost changed');

const hasCkpt0=lines.some(x=>x.startsWith('def ckpt0 : RleFullState'));
const ckpt0=hasCkpt0
  ? parseState(checkpoint('ckpt0'))
  : {mode:'B',ls:{t:'raw',items:[z(1n)]},R:[],halted:false};
const chunks=lines.flatMap(line=>{
  const id=line.match(/^theorem chunk_(\d+)\b/);
  if(!id) return [];
  const normal=line.match(/runBatches\s+(\d+)\s+(ckpt\d+)\s*=\s*(ckpt\d+)/);
  if(normal) return [{index:Number(id[1]),batches:Number(normal[1]),from:normal[2],to:normal[3]}];
  const final=line.match(/\(runBatches\s+(\d+)\s+(ckpt\d+)\)\.halted\s*=\s*true/);
  if(final) return [{index:Number(id[1]),batches:Number(final[1]),from:final[2],to:null}];
  throw new Error('unrecognized chunk theorem: '+line);
}).sort((a,b)=>a.index-b.index);
assert.ok(chunks.length>0,'no chunk schedule found');

let state=ckpt0,total=0n,currentName='ckpt0';
const chunkResults=[];
for(const chunk of chunks) {
  assert.equal(chunk.from,currentName,'chunk schedule is not contiguous');
  if(currentName!=='ckpt0') assert.equal(stable(state),stable(parseState(checkpoint(currentName))),'chunk input checkpoint mismatch');
  const p=runBatches(chunk.batches,state);
  state=p[0]; total+=p[1];
  if(chunk.to) assert.equal(stable(state),stable(parseState(checkpoint(chunk.to))),'checkpoint mismatch at '+chunk.to);
  else assert.equal(state.halted,true,'final RLE state is not halted');
  chunkResults.push({index:chunk.index,batches:chunk.batches,from:chunk.from,to:chunk.to,bound:String(p[1])});
  if(chunk.to) currentName=chunk.to;
}
assert.equal(state.halted,true,'final RLE state is not halted');
if(machineRLE===allowedRLEs[0])
  assert.equal(total,1003448704258405241756955830449585121679083838719n,'first F289 cost bound changed');

const primitiveStepUpperBound=initialPrimitiveStepBound+total;
console.log(JSON.stringify({
  machineRLE,
  checkpointMatches:chunkResults.filter(x=>x.to!==null).map(x=>x.to),
  finalHalted:state.halted,
  rleTransitionsUpperBound:chunks.reduce((a,x)=>a+x.batches*25,0),
  primitiveRuleCosts:ruleCostAudit,
  initialPrimitiveStepBound:String(initialPrimitiveStepBound),
  chunkBounds:chunkResults,
  rleTransitionCostUpperBound:String(total),
  primitiveStepUpperBound:String(primitiveStepUpperBound),
  boundBits:primitiveStepUpperBound.toString(2).length,
  below2pow160:primitiveStepUpperBound<(1n<<160n)
},null,2));
