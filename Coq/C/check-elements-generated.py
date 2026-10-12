#!/usr/bin/env python3
"""Check that every generated or mechanically ported Elements proof module
is exactly what its generator produces from the current sources, and that
the primitive signature still matches the Haskell source.

Usage: check-elements-generated.py   (run from Coq/)"""
import os, subprocess, sys, tempfile

PURE_PORTS = """call effects env_load env_read field_eval frame_access getter32_exec
getter32_layout hash_getter_writehash hash_getters hash_helpers hash_write indexed_exec
indexed_ptr indexed_ptr_then indexed_scalar indexed_then locktime_local read_step
script_cmr_local steps version_canonical version_exec version_layout version_local
word_helpers wrapper write32_exec write32_layout write32s_exec write32s_layout
write8_step""".split()

def same(a, b, what):
    if open(a).read() != open(b).read():
        sys.exit("stale: %s differs from its generator's output" % what)

ns = {}
exec(open('C/port-bitcoin-to-elements.py').read().split("for name in sys.argv")[0], ns)
for name in PURE_PORTS:
    if ns['port'](open('C/jet_bitcoin_%s.v' % name).read()) != open('C/jet_elements_%s.v' % name).read():
        sys.exit("stale: jet_elements_%s.v is not the port of jet_bitcoin_%s.v" % (name, name))

with tempfile.TemporaryDirectory() as tmp:
    def run(*args):
        subprocess.run([sys.executable] + list(args), check=True, stdout=subprocess.DEVNULL)
    out = os.path.join(tmp, "indexed_gen.v")
    run("C/gen-elements-indexed-gen.py", out); same(out, "C/jet_elements_indexed_gen.v", "jet_elements_indexed_gen.v")
    out = os.path.join(tmp, "input_hash.v")
    run("C/gen-elements-input-hash-jets.py", "C/jet_elements_indexed_ptr_jets.v", out)
    same(out, "C/jet_elements_input_hash_jets.v", "jet_elements_input_hash_jets.v")
    out = os.path.join(tmp, "pegin.v")
    run("C/gen-elements-pegin-jet.py", "C/jet_elements_annex_local.v", out)
    same(out, "C/jet_elements_pegin_local.v", "jet_elements_pegin_local.v")
    run("C/gen-elements-current-ptr-jets.py", tmp)
    run("C/port-bitcoin-timelock-to-elements.py", tmp)
    run("C/port-bitcoin-count-to-elements.py", tmp)
    generated = """current_ptr_jets current_input_jets tx_field_set prim_sem is_final_spec is_final_local
        lock_spec lock_exec lock_local bool_wrapper check_lock count_canonical count_bridge count_local""".split()
    for name in generated:
        same(os.path.join(tmp, "jet_elements_%s.v" % name), "C/jet_elements_%s.v" % name,
             "jet_elements_%s.v" % name)
subprocess.run([sys.executable, "C/check-elements-prim-port.py", ".."], check=True)
print("generated Elements modules are current: %d exact ports, %d generated"
      % (len(PURE_PORTS), 3 + len(generated)))
