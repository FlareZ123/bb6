"""Use the existing exact audit emitter with the D0=0RD cylinder."""
import pathlib,sys,emit
emit.PARENT=[7,24,11,24,14,24,13,16,24,13,24,24]
emit.NS='BB6.Agent3Raw139E1ZeroRDD0ZeroRD'
emit.PREFIX='A3E1ZeroRDD0ZeroRD'
emit.main(pathlib.Path(sys.argv[1]),pathlib.Path(__file__).with_name('recipes-d0rd.json'),pathlib.Path(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 600)
