"""Bounded replay; keeps original campaign receipts untouched."""
import importlib.util
import itertools
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('sidon_source', root / 'research/sidon_receipts.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def sidon_independent(values):
    sums = [a+b for a,b in itertools.combinations_with_replacement(values,2)]
    return len(values) == len(set(values)) and len(sums) == len(set(sums))

convention = m.convention_agreement_check()
assert convention['tested'] == 4511 and convention['agree']
standard, elapsed = m.greedy_sidon(40, 15)
formal = m.greedy_lean_predicate(30, 15)
assert len(standard) == 40 and len(formal) == 30
assert all(sidon_independent(a[:k]) for a in (standard, formal) for k in range(1,len(a)+1))
# Directly count the finite formal prefix through its last selected value.
for n in range(formal[-1]+1):
    count = sum(1 for x in formal if x <= n)
    assert n <= 3*(count+1)**3
primes = [3,5,7,11,13,17,19,23,29]
finite = []
for p in primes:
    values = m.erdos_turan(p)
    assert len(values) == p and sidon_independent(values)
    # Shift from [0,N] into [1,N+1] to match the formal ceiling's domain.
    shifted = [x+1 for x in values]
    assert sidon_independent(shifted) and p*p <= p+2*max(shifted)+1
    finite.append({'p':p,'size':len(values),'largest_original':max(values)})
print(json.dumps({'result':'PASS','convention_sets':convention['tested'],
    'standard_greedy_terms':standard,'formal_predicate_terms':formal,
    'formal_density_control_max_N':formal[-1],'finite_constructions':finite,
    'scope':'Finite controls only; no fresh Lean compilation or infinite-density conclusion'},indent=2))
