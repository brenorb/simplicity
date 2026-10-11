"""Fixtures for anchored retained-text diagnostics, not proof checking."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('review', Path(__file__).with_name('review-contracts.py'))
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
assert review.retained('prefix(...)))', 'prefix(value)))))')
assert review.retained('first(...middle...end)', 'first(long-middle-other-end)')
assert not review.retained('prefix(...)))', 'wrongprefix(value)))))')
assert not review.retained('prefix(...)))', 'prefix(value)))))extra')
assert not review.retained('first(...middle...end)', 'first(end-middle-other)')
assert not review.retained('literal(...spec)', 'numeric(value-spec)')
print('Retained-text fixtures passed: repeated closing suffix handled; prefix/suffix/order/spec changes rejected')
