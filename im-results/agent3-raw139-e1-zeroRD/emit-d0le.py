"""Original E1=0RD audit for D0=0LE, including reflected FAR and unary growth."""
import pathlib,sys,emit
emit.PARENT=[7,24,11,24,14,24,16,16,24,13,24,24]
emit.NS='BB6.Agent3Raw139E1ZeroRDD0ZeroLE'
emit.PREFIX='A3E1ZeroRDD0ZeroLE'
emit.COUNTER_NS='BB6.Agent3UnaryGrow'
emit.COUNTER_MODULE='UnaryGrowBridge'
emit.COUNTER_IDS=(346,348,349)
# The original partition query cutoff is 450. No extended last-hole leaves.
emit.MIN_BOUND=456
emit.main(pathlib.Path(sys.argv[1]),pathlib.Path(__file__).with_name('recipes-d0le.json'),pathlib.Path(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 600)
