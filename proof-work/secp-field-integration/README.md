# Regular-module integration candidate for field multiplication

This packet promotes the completed `FieldLiteral.Jet` proof into an isolated
candidate using ordinary `C.*` module names and the regular `_CoqProject.jets`
make dependency graph. It does not edit the checkout's pending shared sources,
registries or staged patch, and does not rewrite historical verification.

`assemble.py prepare` reads only committed proof blobs at `727caf16` and the
exact source closure of `secp-field-literal/CHECKED.json`: 176 existing modules
and 59 extension modules. The latter receive distinct
`C.jet_secp_multiply_<group>_<module>` names. Only qualified module tokens are
renamed, with an exact reverse-transformation check. The C program, literal
specification, theorem statements, tactics and unqualified definitions are not
substituted. Missing shared sources are restored from committed archives into
the isolated candidate, never over the checkout's uncommitted originals.

`PREPARATION.json` records all source origins, hashes, module mappings, normal
project additions and checkout preservation inputs. `assemble.py build` invokes
`coq_makefile` on the regular project and makes the final theorem's `.vo`
target, with the same pinned dependency paths as `build-jets.sh`. It does not
claim to rebuild unrelated registered jets. No private namespace flags or
old compiled objects are used.

```sh
python3 -B proof-work/secp-field-integration/assemble.py prepare
python3 -B proof-work/secp-field-integration/assemble.py build
python3 -B proof-work/secp-field-integration/verify.py reports
python3 -B proof-work/secp-field-integration/verify.py kernel
python3 -B proof-work/secp-field-integration/verify.py check
```

Each mutating phase is one-shot: poll its live process rather than restarting
on a tool observation timeout. A launch file is not a successful result.
Fresh full types/definitions, all 413 inherited theorem assumption profiles,
the exact loaded source-built closure, original-target guard and recursive
kernel check are required. The public endpoint must retain exactly the six
inherited Coq/CompCert assumptions; no external-library model is introduced.

The ordinary-module endpoint is
`C.jet_secp_multiply_literal_jet.fe_multiply_literal_local_spec`, with the same
unrestricted Word256 pair domain and complete frame/memory contract as the
previous checked literal proof. The original LP64 program/configuration is the
target. No other architecture or generation settings are claimed.

This remains an **unregistered integration candidate**. Shared acceptance still
requires review of the candidate sources, source-correspondence gates and
contract/assumption snapshots, then a complete normal acceptance run. The
accepted-coverage delta is zero until that is done; neither metadata nor a
focused successful build establishes coverage of every jet.
