## `simplicity_gej_ge_add_ex`

- Input and layout: `A=((0,p),1)`, `B=(0,0)`, where `p=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f`; disjoint valid input/output frames.
- Specification result: Ratio `p`.
- C result: Success; ratio `0`.
- Evidence: [`gej_ge_add_ex_public_counterexample`](jet_secp_mixed_ex_counterexample.v)

## `simplicity_output_null_datum` — stand-alone overlapping-buffer call

- Input and layout: Indices `(0,0)`; output script `6a 51` (`OP_RETURN OP_1`); represented null-data environment; shared input/output backing storage; 64-bit words; input read edge `40` bytes and cursor `0`; output write edge `0` and cursor/capacity `261` bits.
- Specification result: Output present, datum present (`OP_1`); tags `1,1`.
- C result: Success; output present, datum absent; tags `1,0`; final output cursor `0`.
- Evidence: [`null_data_overlap_counterexample`](jet_elements_null_overlap_counterexample.v)

## `simplicity_left_pad_low_8_16`

- Input and layout: `0xa5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0x00a5`
- C result: Success; `0x0000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_low_8_32`

- Input and layout: `0xa5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0x000000a5`
- C result: Success; `0x00000000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_low_8_64`

- Input and layout: `0xa5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0x00000000000000a5`
- C result: Success; `0x0000000000000000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_low_16_32`

- Input and layout: `0xa5a5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0x0000a5a5`
- C result: Success; `0x00000000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_low_16_64`

- Input and layout: `0xa5a5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0x000000000000a5a5`
- C result: Success; `0x0000000000000000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_low_32_64`

- Input and layout: `0xa5a5a5a5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0x00000000a5a5a5a5`
- C result: Success; `0x0000000000000000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_8_16`

- Input and layout: `0xa5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0xffa5`
- C result: Success; `0xff00`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_8_32`

- Input and layout: `0xa5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0xffffffa5`
- C result: Success; `0xffffff00`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_8_64`

- Input and layout: `0xa5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0xffffffffffffffa5`
- C result: Success; `0xffffffffffffff00`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_16_32`

- Input and layout: `0xa5a5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0xffffa5a5`
- C result: Success; `0xffff0000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_16_64`

- Input and layout: `0xa5a5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0xffffffffffffa5a5`
- C result: Success; `0xffffffffffff0000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_32_64`

- Input and layout: `0xa5a5a5a5`; 64-bit words; input backing words overlap the output suffix.
- Specification result: `0xffffffffa5a5a5a5`
- C result: Success; `0xffffffff00000000`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_1_8`

- Input and layout: Bit `1`; 64-bit words; input backing word overlaps the output.
- Specification result: `0xff`
- C result: Success; `0xfe`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_1_16`

- Input and layout: Bit `1`; 64-bit words; input backing word overlaps the output.
- Specification result: `0xffff`
- C result: Success; `0xfffe`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_1_32`

- Input and layout: Bit `1`; 64-bit words; input backing word overlaps the output.
- Specification result: `0xffffffff`
- C result: Success; `0xfffffffe`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_left_pad_high_1_64`

- Input and layout: Bit `1`; 64-bit words; input backing word overlaps the output.
- Specification result: `0xffffffffffffffff`
- C result: Success; `0xfffffffffffffffe`; final cursor `0`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)

## `simplicity_copyBits` — helper, not a jet

- Input and layout: Eight bits `0xa5`; 64-bit word; exact-alias input/output bits with separate frame descriptors.
- Specification result: `0xa5`
- C result: `0x00`; final cursor `0`; helper returns `void`.
- Evidence: [Native C](../../proof-work/core-overlap-counterexamples/probe.c)
