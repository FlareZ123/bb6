const {rule}=require('./generate_raw140_variant_transfer.js');
const specs=[
 ['bEvenStart','base','3^p 2','0 2 3 Y',0,1,'2 2 3^p 2','3 Y',4,1,'AR0 DR2 BL7 DR3 EL6 ER3 DR3 EL6'],
 ['bEvenMark','base','2 3 3 X','2 2 Y',1,0,'2 7 X','3 3 3 Y',4,1,'BL2 CR2 DR2 BL6^2 BL3 CR2 DR2 BL6 BL7 DR2 BL6 BL3 CR2 DR3 EL6'],
 ['bBounceSeed','base','3^p 2','2 2 3 Y',0,1,'2 6^p+2 4','3 Y',4,1,'AR2 EL3^p EL2 BL0 CR1^p+2 CR2 DR3 EL6'],
 ['bBounceExit','base','4','2^p 3 Y',1,0,'3^p+1 2','2 Y',0,1,'BL4 BR2^p BR3 DL5^p+1 DL0 AR4^p+1']
];
console.log('import Raw140VariantTransfer\nnamespace Raw14042BEvenLocal\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000');
for (const spec of specs) console.log(rule(...spec));
console.log('end Raw14042BEvenLocal');
