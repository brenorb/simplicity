# Square helper: real storage to writer contract

`SquareCaller.Bridge` supplies the concrete adapters needed to use the checked
numeric/literal square result in a public jet proof. Its endpoint is
`eval_square_for_writer`, not a complete public-jet equivalence theorem.

Given the `fe_at` normalized storage produced by the existing canonical reader
and its local Freeable permission, the endpoint proves the original
`f_secp256k1_fe_sqr` call, establishes the existing wide writer's input
representation, retains local Freeable ownership, and frames every other
block. There is no beta-global readiness condition, input/output non-aliasing
assumption for the in-place helper, or assumed helper execution/result.

The five results reuse existing region construction and denotation-preserving
cell revaluation. In particular, `square_output_owned` obtains concrete output
storage from the actual symbolic output representation and its proved values;
it does not assume that the output memory contains the desired square.

## Next composition

Port the structure of `C.jet_secp_beta_chain.eval_beta_read_mul_write`, replacing
its multiplication/global-state step with `eval_square_for_writer`. Keep the
actual square callee and two arguments. Use
`diagonal (square_reader_rho value)` for `product_writer_rho`, and obtain writer
bounds via `diagonal_input_bounds` and `square_reader_bounds`. The existing
`square_product_matches_literal` gives the final literal output after
`product_writer_output`. No beta initialization or preservation premise is
needed.

Then prove the actual public entry, source-frame copy, return and local frees
before exposing `secp_jet_local_spec f_simplicity_fe_square ... literal_fe_square`.
The general frame contract must be retained. Neither this adapter nor the
numeric helper packet completes those lifecycle obligations. Both packets add
zero accepted coverage; normal registration must not bypass the separately
recorded frozen Bitcoin identity/domain failures.
