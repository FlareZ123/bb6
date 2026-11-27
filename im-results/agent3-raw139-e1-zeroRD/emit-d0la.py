"""Original E1=0RD audit for D0=0LA, with three exact counter proofs."""
import pathlib,sys,emit
emit.PARENT=[7,24,11,24,14,24,0,16,24,13,24,24]
emit.NS='BB6.Agent3Raw139E1ZeroRDD0ZeroLA'
emit.PREFIX='A3E1ZeroRDD0ZeroLA'
emit.main(pathlib.Path(sys.argv[1]),pathlib.Path(__file__).with_name('recipes-d0la.json'),pathlib.Path(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 600)
