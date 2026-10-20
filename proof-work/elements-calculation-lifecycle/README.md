# Actual calculation-jet lifecycle pieces

- `Entry`: the real four-local header and function-entry derivation.
- `Allocation`: shared fresh allocation, ownership and preservation facts.
- `Shape`: the actual statement tree, expression/call/copy proofs and the
  enclosing function composition rule (internal execution/store/free premises).
- `Read`: derives four real allocations, the 16-byte source copy, and the
  eight-word reader call from the initial Word256 frame. Proves the exact
  canonical input registers, updated local cursor, old-memory preservation,
  freshness, distinctness and retained ownership of all locals.
- `Writer`: derives the original static `writeHash` call and output cells,
  cursor, prefix, outside-load framing and permission preservation from a
  canonical register array and writable frame. No zero-output or fixed-cursor
  assumption is added; word-boundary crossings use the existing core writer.

Remaining: combine the input prefix with the canonical calculation helper call
(explicit libc/dispatch premises), derive the returned struct's byte copy and
register preservation, invoke the writer, free all four actual locals, and
discharge the internal composition rule from initial public frames. Only then
state the three concrete public jet contracts. This package adds zero accepted
coverage and does not assert that that end-to-end step is complete.
