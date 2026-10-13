"""Read-only snapshot/dependency corruption fixtures for normal integration."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('multiply_normal_review',
    Path(__file__).with_name('review-normal.py'))
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
tests = 0


def rejects(fn):
    global tests
    try:
        fn()
    except ValueError:
        tests += 1
        return
    raise AssertionError('corrupt evidence accepted')


if __name__ == '__main__':
    # Coq prints the full parent declaration when asked to Print a constructor.
    constructor = 'Variant wide_column : Set :=\n    wcolumn : nat -> wide_column.\n'
    inventory = [('C.jet_secp_reduce512_wide', 'wcolumn')]
    review.contract_records(constructor, [], inventory)
    rejects(lambda: review.contract_records(constructor, [], [('C.jet_secp_reduce512_wide', 'other')]))
    rejects(lambda: review.contract_records(constructor.replace('wcolumn :', 'wrong :'), [], inventory))
    rejects(lambda: review.contract_records(constructor.replace('wide_column', 'foreign_type'), [], inventory))
    rejects(lambda: review.contract_records(constructor, inventory, []))
    rejects(lambda: review.contract_records(constructor + constructor, [], inventory))
    rejects(lambda: review.contract_records('unparsed\n' + constructor, [], inventory))
    good = 'JET_ASSUMPTIONS C.foo.bar\nClosed under the global context\n'
    assert review.assumptions(good) == {'C.foo.bar': set()}
    rejects(lambda: review.assumptions(good + good))
    rejects(lambda: review.assumptions('JET_ASSUMPTIONS C.foo.bar\n'))
    rejects(lambda: review.assumptions('JET_ASSUMPTIONS C.foo.bar\nAxioms:\n'))
    rejects(lambda: review.assumptions(good.replace('Closed under the global context',
                                                  'Axioms:\nFabricated.output : Prop')))
    rejects(lambda: review.assumptions('Axioms:\nFabricated.output : Prop\n'))
    assert review.assumptions(good.replace('JET_ASSUMPTIONS', 'PRODUCT_ASSUMPTIONS')) == {'C.foo.bar': set()}
    if len(sys.argv) == 2:
        assert review.review(Path(sys.argv[1]))['exact_per_result_namespace_dependencies']
    elif len(sys.argv) != 1:
        raise SystemExit('usage: test-review.py [ASSEMBLY]')
    print(f'{tests} normal-review corruption fixtures rejected')
