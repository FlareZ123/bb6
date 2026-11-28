// Reproduce canonical discovery on the fourteen B1 siblings of B1=0LA.
const {canonicalRun}=require('./canonical_search.cjs');
const {makeSearch}=require('./search.cjs');
const spec=require('./candidate.json');
const engine=makeSearch(spec.codes,spec.options);
const base=engine.parse('1RB---_1RC---_0RD---_0LD1LB_------_------');
const order=[1,6,7,8,9,12,13,14,18,20,4,10,16,22];
for(const i of order){
 const p=base.slice();p[3]=i;
 const result=canonicalRun(engine.show(p),Math.max(4,i%6+1));
 console.log(JSON.stringify({i,...result}));
}
