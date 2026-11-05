# M31 arithmetic opcodes for efficient STARK verification on Bitcoin

_Hypothetical thought experiments and design ideas_

## Introduction

Verifying STARK proofs on Bitcoin is notoriously challenging due to the limitations of Bitcoin Script.
This article explores a more direct solution: introducing new arithmetic opcodes tailored to the M31 Mersenne prime field ($2^{31}-1$). These hypothetical opcodes (e.g., `OP_M31ADD`, `OP_M31SUB`, `OP_M31MUL`, `OP_M31INV`) would enable direct addition, subtraction, multiplication, and inversion modulo $2^{31}-1$ within script. The primary motivation, in such a scenario, could be to facilitate on-chain verification of STARK proofs (a type of zero-knowledge proof) by providing native field operations. By focusing on a specific prime field, this approach would aim to avoid the broad complexity of a more generic opcode, potentially reducing risks. The following sections outline the rationale for specialized M31 opcodes, describe their possible semantics, and consider both security and feasibility concerns in a hypothetical, backward-compatible **soft fork** upgrade that extends Bitcoin’s scripting capabilities in a targeted and safe manner.

[STARKs (Scalable Transparent Argument of Knowledge)](https://eprint.iacr.org/2018/046.pdf) allow a prover to demonstrate the validity of a computation without revealing some details (the formal ZK part of it is not granted by default and require some additional work, i.e STARKs can be used for scaling only), offering both scalability and privacy advantages. Enabling Bitcoin Script to verify a STARK proof efficiently would let developers build trustless bridges to Layer-2 systems or run complex off-chain computations with minimal on-chain data. However, STARK verification commonly requires extensive finite field arithmetic, and many STARK constructions rely on prime fields. A compelling choice might be the Mersenne prime $2^{31} - 1$ (denoted **M31**), which [research](https://eprint.iacr.org/2024/278) shows is especially efficient on standard hardware. This prime fits into a single 32-bit word, making addition and multiplication faster on modern CPUs.

By introducing dedicated M31 field opcodes, one might directly support the arithmetic needed for STARKs, making on-chain verification practical and efficient.

---

## Why specialized M31 opcodes instead of a generic approach?

> Disclaimer: I am actually supportive of `OP_CAT`, and I personally think it should be seriously considered as part of a potential next soft-fork. Here, I am semi playing devil's advocate (and reusing typical arguments made against `OP_CAT`) to justify why we might prefer dedicated M31 arithmetic opcodes over a more general approach. Also, in reality, we would in anycase need covenants and efficient merkle tree verification to be able to verify STARKs on-chain.

A more general opcode (such as `OP_CAT`) has often been discussed to expand Script’s flexibility. Dedicated M31 arithmetic opcodes could have some advantages for STARK verification, for several reasons:

- **Safety and predictability:**
   More general opcodes (like `OP_CAT`) open the door to a wide range of new use cases. This flexibility is cool but can bring “unknown unknowns”: potential security or consensus issues we haven’t even imagined. We already saw `OP_CAT` get disabled in the past over security concerns. In contrast, M31 opcodes do one thing—modular arithmetic. That narrow focus is easier to analyze, easier to test, and less likely to yield surprising new issues.

- **Mitigating MEV and complexity risks:**
  Another concern with making Bitcoin Script more expressive involves **Maximal Extractable Value (MEV)** scenarios. Complex on-chain contracts might allow miners to reorder or front-run transactions for profit. Some observers might suggest that a specialized opcode for STARK-proof verification would not introduce new economic states or front-running opportunities, since such arithmetic is purely a check. By restricting to specialized opcodes, the network might avoid classes of new programs that could lead to on-chain bidding wars or other exploitable complexities.

- **Efficiency and performance:**
  A hypothetical general approach to emulate 31-bit arithmetic via concatenation or string manipulation would likely be inefficient. Experimentation in current Script has suggested that implementing M31 multiplication by hand could be very large in weight and cumbersome (about _1415 weight units_ for a single multiplication). In contrast, a native `OP_M31MUL` would hypothetically be a single opcode, pushing the result in one step. This would make verification scripts smaller and cheaper to execute on-chain. Since the goal (supporting STARK verification) is already identified, specialized opcodes might be introduced **directly**, sparing the network from large, inefficient scripts. Open question: do we need varops style model here (assign a cost for each of the opcodes to take into account the worst case, check [GSR proposal to understand the concept of varops](https://bitcoinmagazine.com/technical/the-great-script-restoration-a-path-forward-for-bitcoin)) ?

- **Minimal impact on other use-cases:**
  M31 opcodes would be _domain-specific_. They would mostly appeal to ZK-proof related scripts, leaving typical Bitcoin usage unaffected. A more universal feature like `OP_CAT` could spill into many different script designs, potentially complicating the ecosystem. Sticking to M31 arithmetic might ensure clarity about what is being added and why, aiding review and deployment under Bitcoin’s conservative upgrade ethos.

In essence, specialized M31 opcodes could meet the STARK verification needs while staying within a comfortable security boundary. They might be safer and more efficient than a catch-all opcode, aligning with a more conservative approach.

---

## Bonus: could M31 opcodes enable post-quantum signature schemes?

While the primary motivation has been facilitating efficient STARK proof verification, an intriguing secondary possibility emerges: could these M31 arithmetic opcodes support building post-quantum signature schemes on Bitcoin?

The ongoing efforts by NIST to standardize post-quantum cryptographic algorithms bring several interesting candidates into focus. Here are a few worth exploring in relation to M31:

- **[CRYSTALS-Dilithium](https://eprint.iacr.org/2017/633.pdf):** A lattice-based signature scheme and a finalist in the NIST post-quantum competition. It currently uses the prime $8380417 = 2^{23} - 2^{13} + 1$. While the security implications of changing the underlying prime need careful evaluation, emulating or adapting Dilithium's arithmetic operations to the M31 field could be practical and worth investigating further.

- **[FALCON](https://falcon-sign.info/):** Another lattice-based finalist utilizing the small Mersenne prime $2^{11}-1$. Due to structural similarities, adapting its operations to use M31 ($2^{31}-1$) might be straightforward and secure. This could present a direct route to implementing post-quantum signatures leveraging existing Bitcoin primitives.

- **[Rainbow](https://www.pqcrainbow.org/):** A multivariate quadratic-based finalist relying on the significantly larger prime $2^{127}-1$. Unfortunately, the substantial size difference likely makes M31 unsuitable for Rainbow’s specific cryptographic needs, ruling out easy adaptation.

While these considerations remain preliminary (and most of them are not battle-tested yet), the potential compatibility between M31 arithmetic and certain post-quantum signature schemes opens an exciting direction for future exploration.

---

## Specification

### New opcodes for M31 field arithmetic

One might propose the following new opcodes for **Taproot tapscript** context (to be activated via a hypothetical soft fork). Each opcode would operate on 31-bit Mersenne field elements, modulo $(p = 2^{31} - 1 = 2147483647)$. Unless otherwise stated, values would be taken as unsigned 31-bit integers in little-endian encoding, with minimal encoding rules as usual.

1. **`OP_M31ADD` (M31 addition)**
   Would pop two stack elements `x` and `y` and interpret them as integers modulo $p$. The sum $s = (x + y) \mod p$ would be pushed onto the stack as a minimally encoded number.

2. **`OP_M31SUB` (M31 subtraction)**
   Would pop `x` and `y` and compute $d = (x - y) \mod p$, wrapping around under modulo if $x < y$. The result would be pushed onto the stack.

3. **`OP_M31MUL` (M31 multiplication)**
   Would pop `x` and `y`, then compute $m = (x \times y) \mod p$ before pushing the result. A 64-bit intermediate could handle 31-bit multiplications safely.

4. **`OP_M31INV` (M31 multiplicative inverse)**
   Would pop the top stack element `x` and push $x^{-1} \mod p$ (the value satisfying $(x \cdot x^{-1}) \equiv 1 \pmod p$). If `x` were 0 modulo $p$, the opcode would fail (no inverse). For any other `x`, an inverse would exist in the field.

### Opcode number assignments

In a hypothetical soft-fork design, these opcodes might be allocated to currently unused **OP_SUCCESS** ranges, ensuring that older nodes see these as trivially valid but do not execute them (thus enabling backward compatibility). They would be recognized and properly executed only by upgraded nodes.

### Taproot-only context

These opcodes could be active only in Taproot script-path spends (e.g., a new tapscript version). Legacy script types might remain unchanged and unaffected by these additions.

---

## Backward compatibility

Such additions would be designed as a **soft fork**: pre-upgrade nodes would treat these new opcodes as `OP_SUCCESS`, allowing scripts to pass validation (under policy constraints). After activation, upgraded nodes would enforce the intended M31 arithmetic. Because the opcodes would apply only within Taproot-based scripts, legacy outputs would be untouched. This approach might ensure that existing transaction validity remains the same while adding the new, optional functionality.

---

## Security considerations

1. **Denial-of-service (DoS) and resource consumption:**
   Each operation (`OP_M31ADD`, `OP_M31SUB`, `OP_M31MUL`, `OP_M31INV`) would essentially be fast integer arithmetic, which are trivial operations compared to signature checks or hashing. Scripts full of these opcodes might still be constrained by overall block weight, so spamming might be economically disincentivized. Developers might nonetheless account for a small resource cost per operation if needed, similar to “sigop” counting.

2. **Memory and stack safety:**
   All inputs and outputs would remain at most 4 bytes long, with no large allocations. This would avoid the potential memory-inflation concerns of more general string manipulation opcodes. Standard stack size limits would continue to apply.

3. **Field arithmetic soundness:**
   $2^{31}-1$ is a relatively small prime, which would be considered insufficient for certain cryptographic primitives (like large-discrete-log-based systems). However, STARKs typically rely on hashing for security; the field is used mostly for algebraic checks, not secrecy. Provided the underlying STARK protocol is well-designed, using M31 for verification steps would not introduce fundamental weaknesses.

4. **Consensus and validation risks:**
   Proper implementation would need to be thoroughly tested. Special care would be taken around edge cases (e.g. 0, $p-1$, negative inputs) to avoid consensus splits. A robust reference implementation and test suite could help mitigate these risks.

5. **Miner policy and fee market:**
   Including large STARK proofs on-chain would remain subject to normal weight-based fees. Because any user broadcasting large proofs would pay proportionally, the system might self-regulate. The presence of these opcodes alone would not guarantee widespread use unless real applications (like L2 systems or bridging) found on-chain verification valuable enough to cover the fees.

## Additional challenges / open questions

- Enshrining one particular field is far from being insignificant choice:
    What if tomorrow there is another field discovered and potentially new schemes leveraging that offer better efficiency (or better other desirable properties). How do we define when it's worth considering enshrining new cryptographic primitives and when it's not ?
- Not battle-tested yet:
    M31 and Circle STARKs are not battle-tested yet. We need more time to assess their security and full potential.
- Should we consider more flexible modular arithmetic primitives ? i.e giving options to specify a custom field ? What are the tradeoffs in terms of complexity / efficiency / securty ?

---

## Conclusion

Would it be possible / interesting for Bitcoin to add specialized M31 arithmetic opcodes as a soft-fork? Under this line of thought, it seems feasible. Such a design might allow on-chain STARK verification, providing new cryptographic capabilities without the broader security risks and complexity of more general-purpose opcodes. The Mersenne prime $2^{31}-1$ would allow simple and efficient arithmetic, and careful implementation could reduce the risk of consensus errors. While this concept remains a thought experiment, one among many potential upgrades, it might offer a path to powerful zero-knowledge proofs on Bitcoin.

## Resources

- [Circle STARKs paper](https://eprint.iacr.org/2024/278)
- [STWO Circle STARK prover](https://github.com/starkware-libs/stwo)
- [Bitcoin Circle STARK verifier in Bitcoin script - using OP_CAT](https://github.com/Bitcoin-Wildlife-Sanctuary/bitcoin-circle-stark)

---

Fix the money, fix the world. ✌️

Catch me on nostr: `npub1hr6v96g0phtxwys4x0tm3khawuuykz6s28uzwtj5j0zc7lunu99snw2e29`

![Screenshot 2024-08-01 at 13.53.45](https://hackmd.io/_uploads/SkAvwlYYC.png)

![X (formerly Twitter) Follow](https://img.shields.io/twitter/follow/dimahledba)