#!/usr/bin/env python3
"""Derive the five linked call-site modules from the accepted sources.

In the linked program the callee of memcpy is an internal function, so the
premise/conclusion `external_call (EF_external "memcpy" ...) ge0 args m t v m'`
becomes `memcpy_call ge0 args m t v m'` (the big-step call of that function)
and the call node is that derivation itself instead of the external-call
rule.  Nothing else is edited; each rule must apply the recorded number of
times.
"""
import sys

OLD_CALL = 'external_call (EF_external "memcpy" memcpy_sig) ge0'
NEW_CALL = "memcpy_call ge0"
OLD_NODE = "eapply eval_funcall_external. exact Hext."
NEW_NODE = "exact Hext."
CORE = {OLD_CALL: NEW_CALL, OLD_NODE: NEW_NODE}

# SHA translation unit: the generic copy lemma is stated for a Clight global
# environment (as the linked model is), and the callee found at the memcpy
# symbol of sha_ge is the linked internal definition.
SHA_PREP = {
    "Lemma memcpy_bytes_effect (Hmodel : memcpy_model) (ge : Senv.t) m":
        "Lemma memcpy_bytes_effect (Hmodel : memcpy_model) (ge : genv) m",
    'external_call (EF_external "memcpy" memcpy_sig) ge\n': "memcpy_call ge\n",
    """    Some (External (EF_external "memcpy" memcpy_sig)
      (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default).""":
        "    Some (Internal f_memcpy).",
}
SHA_LOOP = {
    "memcpy_bytes_effect Hmodel (Clight.genv_genv sha_ge) m":
        "memcpy_bytes_effect Hmodel sha_ge m",
    "rewrite HVn. apply eval_funcall_external. exact HX.": "rewrite HVn. exact HX.",
}
# module -> (rewrites, {old text: required number of occurrences})
RULES = {
    "jet_copyBits_memcpy_exec.v": (CORE, {OLD_CALL: 1, OLD_NODE: 1}),
    "jet_copyBits_memcpy_helper.v": (CORE, {OLD_CALL: 3, OLD_NODE: 0}),
    "jet_copyBits_wide_memcpy.v": (CORE, {OLD_CALL: 3, OLD_NODE: 1}),
    "jet_sha_uchars_prep.v": (SHA_PREP, {k: 1 for k in SHA_PREP}),
    "jet_sha_uchars_loop.v": (SHA_LOOP, {k: 1 for k in SHA_LOOP}),
}

src_dir, out_dir = sys.argv[1:3]
for name, (rewrites, counts) in RULES.items():
    text = open("%s/%s" % (src_dir, name)).read()
    for old, new in rewrites.items():
        if text.count(old) != counts[old]:
            sys.exit("%s: unexpected number of rewrite sites for %r" % (name, old))
        text = text.replace(old, new)
    if "EF_external" in text or "eval_funcall_external" in text:
        sys.exit("%s: residual external-call reference" % name)
    open("%s/%s" % (out_dir, name), "w").write(text)
