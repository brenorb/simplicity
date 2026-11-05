#!/usr/bin/env python3
"""Identify exact typed Fibonacci STARK sub-DAGs in a measured snapshot.

`probe` emits a scratch Haskell program. It only factors named parts of the
frozen expression into bindings and computes their jetted CMRs. `summarize`
looks those roots up in a complete native profile, where costs are already
measured. Neither command modifies the verifier or the corpus.
"""
import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/JetDiscovery/Corpus/FibonacciStark.hs'


def probe(fields=False):
    source = SOURCE.read_text()
    header, body = source.split('verifier ::', 1)
    _, body = body.split(' where\n  nf=R.traceLog p;', 1)
    body = '  nf=R.traceLog p;' + body.split('\nentries ::', 1)[0]
    body = re.sub(r'\bt\b', 'ProbeTerm', body)
    header = header.replace('module JetDiscovery.Corpus.FibonacciStark (entries, verifier, verifierWithContext) where', '''module Main where

import qualified Simplicity.Bitcoin.Dag as Dag
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Digest (Hash256)
import Simplicity.MerkleRoot (CommitmentRoot,commitmentRoot)''')

    def lift(old, replacement):
        nonlocal body
        if body.count(old) != 1:
            raise ValueError('Missing unique probe anchor: ' + old)
        body = body.replace(old, replacement, 1)

    # Retain the exact opening expression in each lifted binding.
    expression = 'authOpening n(R.siblings(R.traceOpening qp))(take(take(take qi)))(drop pairHash)(take(drop(take(take iden))))'
    lift('&&&'+expression, '&&&traceAuthentication')
    lift('    compositionStep ::', '    traceAuthentication :: ProbeTerm TraceState ()\n    traceAuthentication='+expression+'\n    compositionStep ::')
    expression = 'authOpening n(R.siblings(R.compositionOpening qp))(take(take(take(take qi))))(drop pairHash)(take(take(drop(take(drop iden)))))'
    lift('&&&'+expression, '&&&compositionAuthentication')
    lift('    deep ::', '    compositionAuthentication :: ProbeTerm InitState ()\n    compositionAuthentication='+expression+'\n    deep ::')
    expression = 'authOpening(n-l)(R.siblings(R.friOpenings qp!!l))(take(take(take qi)))(take(drop pairHash))(drop(take iden))'
    lift('&&&'+expression, '&&&layerAuthentication l')
    lift('    nextLayer ::', '    layerAuthentication :: Int->ProbeTerm LayerState ()\n    layerAuthentication l='+expression+'\n    nextLayer ::')
    lift('  query :: Int->R.FriQuery->ProbeTerm E ()\n  query k qp=(iden&&&x0)>>>initial>>>runLayer 0>>>L.foldl\' (\\acc l->acc>>>nextLayer l) iden [1..nf-1]>>>unit', '''  query :: Int->R.FriQuery->[(String,Hash256)]
  query k qp =
    [stage "query_domain_point" x0, stage "trace_merkle_path" traceAuthentication,
     stage "composition_merkle_path" compositionAuthentication] ++
    [stage "deep_quotient" (deep side) | side<-[0,1]] ++
    [stage "fri_merkle_path" (layerAuthentication l) | l<-[0..nf-1]] ++
    [stage "fri_post_opening" (layerArithmetic l) | l<-[0..nf-1]]''')
    lift('>>>(iden&&&witness(toQ(R.friInverses qp!!l)))>>>((checks&&&result)>>>ih)\n     where',
         '''>>>layerArithmetic l
    layerArithmetic :: Int->ProbeTerm LayerState ExpectedState
    layerArithmetic l=(iden&&&witness(toQ(R.friInverses qp!!l)))>>>((checks&&&result)>>>ih)
     where''')
    cmr_probe = '''type ProbeTerm = Dag.JetDag J.JetType

stage :: forall a b. (TyC a,TyC b)=>String->ProbeTerm a b->(String,Hash256)
stage name term=(name,commitmentRoot(J.unwrap(J.jetSubst term)::CommitmentRoot a b))

printStage (name,root)=putStrLn(name++"\\t"++show root)
'''
    if fields:
        return header.replace('(QM31, toQ,', '(QM31, m31Mul, toQ,') + cmr_probe + '''
main :: IO ()
main=mapM_ printStage [stage "m31_mul" m31Mul,stage "qm31_mul" qm31Mul]
'''
    return header + cmr_probe + '''
main :: IO ()
main=mapM_ printStage (stages p pr certs)
 where
  p=R.realistic
  pr=R.prove p
  certs=snd(C.context p pr)

stages :: R.Parameters->R.Proof->C.Certificates->[(String,Hash256)]
stages p pr certs=stage "air_ood" air:concat [query k(R.queries pr!!k)|k<-[0..R.queryCount p-1]]
 where
''' + body


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def summarize(roots, fields, snapshot):
    raw = gzip.decompress(snapshot.read_bytes()) if snapshot.suffix == '.gz' else snapshot.read_bytes()
    text = raw.decode()
    header = re.match(r'Snapshot [23] "([0-9a-f]{64})" "stark-fibonacci-full" '
                      r'\(SM "([0-9a-f]{64})" \[([0-9,]+)\]', text)
    if not header:
        raise ValueError('Expected a complete Fibonacci STARK snapshot')
    fp, program_cmr, measurements = header.groups()
    native, _, _, _, _, node_count, profile_total = map(int, measurements.split(','))
    nodes = defaultdict(list)
    profile_sum = 0
    rows = re.findall(r'SN \d+ \d+ "([0-9a-f]{64})" \d+ "[^"\n]+" '
                      r'[^,]*? (\d+) (\d+) (\d+) \d+(?=[,\]])', text)
    for root, own, inclusive, mult in rows:
        profile_sum += int(own)*int(mult)
        nodes[root].append((int(inclusive), int(mult)))
    if len(rows)!=node_count or profile_sum!=profile_total or profile_sum!=native:
        raise ValueError('Native cost profile count or exclusive-cost sum differs')
    selected = defaultdict(Counter)
    for line in roots.read_text().splitlines():
        label, cmr = line.split('\t')
        selected[label][cmr.removeprefix('0x')] += 1
    query_count = 48
    expected = dict(air_ood=1, query_domain_point=query_count,
                    trace_merkle_path=query_count, composition_merkle_path=query_count,
                    deep_quotient=2*query_count, fri_merkle_path=10*query_count,
                    fri_post_opening=10*query_count)
    if {k: sum(v.values()) for k, v in selected.items()} != expected:
        raise ValueError('Probe did not account for every expected stage')
    stages = {}
    assigned = set()
    for label, by_cmr in selected.items():
        data = []
        for root, intended in by_cmr.items():
            matching = nodes[root]
            costs = {cost for cost,_ in matching}
            # The same CMR can carry different witness values in the full
            # DAG. Group these nodes only if every cost agrees and the
            # selected-path multiplicity exactly matches the source calls.
            if root in assigned or len(costs)!=1 or sum(mult for _,mult in matching)!=intended:
                raise ValueError(f'{label}/{root}: ambiguous root, cost or multiplicity: {matching}, expected {intended}')
            assigned.add(root)
            data.append(dict(cmr=root, native_mwu_each=costs.pop(),
                             selected_occurrences=intended, distinct_dag_nodes=len(matching)))
        stages[label] = dict(native_mwu=sum(r['native_mwu_each']*r['selected_occurrences'] for r in data),
                             roots=data)
    accounted = sum(s['native_mwu'] for s in stages.values())
    if accounted >= native:
        raise ValueError('Extracted regions exceed the complete bound')
    field_roots = dict(line.split('\t') for line in fields.read_text().splitlines())
    if set(field_roots)!={'m31_mul','qm31_mul'}:
        raise ValueError('Expected both base-field and extension-field multiply roots')
    field_costs = {}
    for name, root in field_roots.items():
        root = root.removeprefix('0x')
        matching = nodes[root]
        costs = {cost for cost,_ in matching}
        count = sum(mult for _,mult in matching)
        if len(costs)!=1 or count<=0:
            raise ValueError('Missing or inconsistent field multiply profile for '+name)
        cost = costs.pop()
        field_costs[name] = dict(cmr=root,native_mwu_each=cost,selected_occurrences=count,
                                inclusive_native_mwu=cost*count,distinct_dag_nodes=len(matching))
    print(json.dumps(dict(fingerprint=fp, cmr=program_cmr, full_native_mwu=native,
                          remaining_native_mwu=native-accounted,
                          source_sha256=digest(SOURCE), snapshot_sha256=hashlib.sha256(raw).hexdigest(),
                          stage_roots_sha256=digest(roots), field_roots_sha256=digest(fields),
                          field_multiply_inclusive_overlapping=field_costs, stages=stages), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    generator = sub.add_parser('probe')
    generator.add_argument('--fields', action='store_true', help='generate only the two field multiply roots')
    summary = sub.add_parser('summarize')
    summary.add_argument('roots', type=Path)
    summary.add_argument('fields', type=Path)
    summary.add_argument('snapshot', type=Path)
    args = parser.parse_args()
    if args.mode == 'probe':
        print(probe(args.fields), end='')
    else:
        summarize(args.roots, args.fields, args.snapshot)


if __name__ == '__main__':
    main()
