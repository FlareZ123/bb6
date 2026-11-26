"""Use the established support-complete block-FAR checker for Raw108 witnesses.

The former dense width-six checker stalled for 120 minutes on LA114.
The active checker validates the same finite automaton through sparse support;
it does not weaken any original-machine or completion proof obligation.
"""
from build_lb import emit_block

def emit(mod, namespace, table, params):
    emit_block(mod, namespace, table, params, active=True)
