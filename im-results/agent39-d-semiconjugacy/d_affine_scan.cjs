'use strict';

/** @typedef {{n: bigint, suffix: string, time: bigint}} Section */
/** @typedef {{section: Section, branch: string, tripleCount: number}} Transition */

/** @param {string} s @param {number} i @returns {string} */
function bit(s, i) { return s[i] ?? '0'; }

/** @param {bigint} n @param {string} suffix @param {bigint} time @returns {Section} */
function canonical(n, suffix, time) {
  const trimmed = suffix.replace(/0+$/, '');
  const leading = /^1*/.exec(trimmed)[0].length;
  return {n: n + BigInt(leading), suffix: trimmed.slice(leading), time};
}

/** @param {Section} state @returns {Transition} */
function advance(state) {
  const {n, suffix, time} = state;
  if (n < 2n || bit(suffix, 0) !== '0') throw Error('Invalid input section');
  let nn; let ss; let dt; let branch; let tripleCount = 0;
  if (n % 3n === 2n) {
    const k = (n - 2n) / 3n;
    nn = 8n*k+9n;
    ss = suffix.slice(1);
    dt = 12n*k*k + 49n*k + 40n;
    branch = 'B';
  } else if (n % 3n === 0n) {
    const k = (n - 3n) / 3n;
    let i = 1; let inc = 0n; let cost = 0n; let m = 4n*k+3n;
    for (;;) {
      if (bit(suffix, i) === '0') {
        nn = 8n*k+11n+2n*inc;
        ss = suffix.slice(i+1);
        dt = 12n*k*k+41n*k+32n+cost+2n*m+6n;
        branch = 'A-close';
        break;
      }
      if (bit(suffix,i+1) === '0') {
        i += 2; inc += 1n; cost += 2n; m += 1n;
        continue;
      }
      if (bit(suffix,i+2) === '1') {
        i += 3; inc += 4n; cost += 6n*m+41n; m += 4n; tripleCount++;
        continue;
      }
      if (bit(suffix,i+3) === '0') {
        nn = 8n*k+7n+2n*inc;
        ss = '0'+'1'.repeat(6)+suffix.slice(i+4);
        dt = 12n*k*k+41n*k+32n+cost+2n*m+16n;
        branch = 'A-double';
        break;
      }
      if ([3,4,5,6,7,8].every(j => bit(suffix,i+j)==='1') && bit(suffix,i+9)==='0') {
        nn = 8n*k+11n+2n*inc;
        ss = '010101110'+suffix.slice(i+10);
        dt = 12n*k*k+41n*k+32n+cost+2n*m+24n;
        branch = 'A-six';
        break;
      }
      throw Error('A gate unavailable');
    }
  } else {
    const k = (n - 4n) / 3n;
    let i = 1; let q = 0;
    while (bit(suffix,i)==='1' && bit(suffix,i+1)==='0') {
      i+=2; q++;
    }
    const qn = BigInt(q);
    if (bit(suffix,i)==='0') {
      nn = 8n*k+5n;
      ss='0'+'1'.repeat(2*q+6)+suffix.slice(i+1);
      dt=12n*k*k+49n*k+50n+4n*qn;
      branch='E-pairs';
    } else if ([0,1,2].every(j => bit(suffix,i+j)==='1')) {
      nn=8n*k+9n;
      ss='01'.repeat(q+2)+'0'+suffix.slice(i+3);
      dt=12n*k*k+49n*k+58n+6n*qn;
      branch='E-triple';
    } else if (q>=1 && [0,1,2,3].map(j=>bit(suffix,i+j)).join('')==='1100') {
      nn=8n*k+5n;
      ss='0'+'1'.repeat(2*q+2)+'0'+'1'.repeat(6)+suffix.slice(i+4);
      dt=12n*k*k+49n*k+60n+4n*qn;
      branch='E-double';
    } else if (q===0 && [0,1,2,3].map(j=>bit(suffix,i+j)).join('')==='1100') {
      nn=8n*k+3n;
      ss='011110101010'+suffix.slice(i+4);
      dt=12n*k*k+49n*k+96n;
      branch='E-zero-double';
    } else {
      throw Error('E gate unavailable');
    }
  }
  return {section:canonical(nn,ss,time+dt),branch,tripleCount};
}

const seeds=[['D0-A',9n,36n],['D3-B',5n,15n],['D2-C',15n,92n],['D1-F',39n,403n]];
const traces = new Map();
for (const [name,seed,offset] of seeds) {
  let s={n:seed,suffix:'',time:offset};
  const history=[];
  const branches=new Map();
  for(let i=0;i<5000;i++) {
    const t=advance(s);
    const variations=[1n,3n,13n,100n];
    for (const d of variations) {
      const shifted=advance({...s,n:s.n+3n*d});
      if (shifted.branch!==t.branch || shifted.section.suffix!==t.section.suffix ||
        shifted.section.n!==t.section.n+8n*d) throw Error(`${name} shadow invariant failed at ${i}`);
      const base= s.n%3n===2n ? 2n : (s.n%3n===0n ? 3n : 4n);
      const k=(s.n-base)/3n;
      const predictedTimeDiff=24n*k*d+12n*d*d+(49n+24n*BigInt(t.tripleCount))*d;
      if (shifted.section.time-t.section.time!==predictedTimeDiff)
        throw Error(`${name} primitive-time shift invariant failed at ${i}`);
    }
    history.push({n:s.n,suffix:s.suffix,branch:t.branch});
    branches.set(t.branch,(branches.get(t.branch)??0)+1);
    s=t.section;
  }
  traces.set(name,history);
  console.log(JSON.stringify({name,macros:history.length,finalBits:s.n.toString(2).length,
      timeBits:s.time.toString(2).length,finalSuffix:s.suffix,branchCounts:Object.fromEntries(branches),
      first12:history.slice(0,12).map(x=>[x.n.toString(),x.suffix,x.branch])}));
}
const names=[...traces.keys()];
for(let a=0;a<names.length;a++) for(let b=a+1;b<names.length;b++) {
  const A=traces.get(names[a]); const B=traces.get(names[b]);
  let sameSectionAtSameIndex=0, sameSuffixSameBranch=0, longest=0,now=0,firstDifferent=null;
  for (let i=0;i<5000;i++) {
    const x=A[i],y=B[i];
    if(x.n===y.n && x.suffix===y.suffix) sameSectionAtSameIndex++;
    if(x.suffix===y.suffix && x.branch===y.branch) {sameSuffixSameBranch++;now++;longest=Math.max(longest,now);}
    else {if(firstDifferent===null) firstDifferent=i;now=0;}
  }
  const observed=new Set(A.map(x=>`${x.n}:${x.suffix}`));
  let asyncMatches=0;
  for(const x of B) if(observed.has(`${x.n}:${x.suffix}`)) asyncMatches++;
  const delta=seeds[b][1]-seeds[a][1];
  console.log(JSON.stringify({pair:[names[a],names[b]],initialSignedDelta:delta.toString(),
    sameSectionAtSameIndex,asyncMatches,sameSuffixSameBranch,longest,firstDifferent}));
}
