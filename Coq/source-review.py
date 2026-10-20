"""Shared active-source parsing helpers for the literal correspondence checks.

This module has no stored reference, fingerprint, or acceptance gate.
"""
import importlib.util
import re
from pathlib import Path
from types import SimpleNamespace


def parser(repo):
    spec = importlib.util.spec_from_file_location('active_source_parser',
        Path(repo)/'Coq/check-secp-predicates-specification.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def active(module, path, text):
    return module.read_code(SimpleNamespace(suffix=Path(path).suffix,
        read_text=lambda: text))


def declaration(code, name):
    matches = list(re.finditer(r'\b(?:Definition|Fixpoint)\s+'+re.escape(name)+
        r'\b.*?\.\s*(?:\n|$)', code, re.S))
    if len(matches) != 1:
        raise ValueError('missing or duplicate Coq declaration '+name)
    return matches[0][0]
