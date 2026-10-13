"""Read-only evidence corruption fixtures; no proof or snapshot file is edited."""
import argparse
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('nullable_review', Path(__file__).with_name('review.py'))
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)


def reject(candidate, path, corrupt):
    original = Path.read_text
    path = path.resolve()
    text = original(path)
    mutated = corrupt(text)
    if mutated == text:
        raise AssertionError('fixture did not mutate its target')
    def intercepted(self, *args, **kwargs):
        return mutated if self.resolve() == path else original(self, *args, **kwargs)
    Path.read_text = intercepted
    try:
        try:
            review.review(candidate)
        except ValueError:
            pass
        else:
            raise AssertionError('corrupt preparation was accepted')
    finally:
        Path.read_text = original


def main(candidate):
    review.review(candidate)
    coq = candidate / 'Coq'
    reject(candidate, coq / 'C/jet_coverage.tsv',
           lambda s: s.replace('bitcoin_tappath_nullable_raw_local_spec', 'bitcoin_tappath_raw_local_spec', 1))
    reject(candidate, coq / 'C/jet_public_theorems.txt',
           lambda s: s + 'C.jet_bitcoin_tappath_nullable_raw bitcoin_tappath_nullable_raw_local_spec\n')
    reject(candidate, coq / 'C/jet_contract_definitions.txt',
           lambda s: s.replace('C.jet_bitcoin_tappath_nullable bitcoin_tappath_env_rep_nullable',
                               'C.jet_bitcoin_tappath_local bitcoin_tappath_env_rep', 1))
    reject(candidate, coq / 'C/jet_contracts.expected',
           lambda s: s.replace('memcpy_builtin_witness', 'mutated_memcpy_builtin_witness', 1))
    reject(candidate, coq / 'C/jet_assumptions.expected',
           lambda s: s + 'Invented.result : Invented.axiom\n')
    reject(candidate, coq / 'C/jet_assumptions.expected',
           lambda s: s + s.splitlines()[0] + '\n')
    reject(candidate, candidate / 'new_contracts.out',
           lambda s: s.replace('NULLABLE_DEEP_TYPE ', 'MISSING_DEEP_TYPE ', 1))
    reject(candidate, candidate / 'new_contracts.out',
           lambda s: s + '...\n')
    print('nullable admission corruption fixtures passed: 8')


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate', type=Path, required=True)
    main(cli.parse_args().candidate.resolve())
