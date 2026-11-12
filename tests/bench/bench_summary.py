#!/usr/bin/env python3
"""Summarize a challenge_bench.sh output directory.

    tests/bench/bench_summary.py OUTDIR [BASELINE_LABEL]

Per instance and build: solved runs, median / min / max final objective.
The verdict column compares every build with the baseline (first build in
config.txt unless given): "better"/"worse" only when the two builds' ranges do
not overlap (or one solves in every run and the other in none), "~" otherwise.
With 3 runs that is a coarse test: it flags clear shifts and treats the rest
as noise.
"""
import csv, os, re, statistics, sys

out = sys.argv[1]
labels = []
for line in open(os.path.join(out, 'config.txt')):
    m = re.match(r'^([^=\s]+)=/', line)
    if m:
        labels.append(m.group(1))
base = sys.argv[2] if len(sys.argv) > 2 else labels[0]

def direction(name):
    with open(os.path.join(out, 'fzn', name + '.fzn')) as f:
        for line in f:
            if line.startswith('solve'):
                return 'max' if 'maximize' in line else 'min' if 'minimize' in line else 'sat'
    return 'sat'

res = {}
order = []
for r in csv.DictReader(open(os.path.join(out, 'results.tsv')), delimiter='\t'):
    key = r['instance']
    if key not in res:
        res[key] = {}
        order.append(key)
    res[key].setdefault(r['build'], []).append(r)

def stats(runs, d):
    vals = [int(r['objective']) for r in runs if r['status'] == 'SOL' and r['objective'] not in ('-', 'sat')]
    nsat = sum(1 for r in runs if r['status'] == 'SOL')
    return nsat, len(runs), vals

def verdict(a, b, d):
    """b relative to a."""
    (na, ta, va), (nb, tb, vb) = a, b
    if d == 'sat' or not va or not vb:
        if nb == tb and na == 0: return 'better'
        if na == ta and nb == 0: return 'worse'
        if d == 'sat' or (not va and not vb): return '~'
        return '~'
    if d == 'min':
        if max(vb) < min(va) and nb >= na: return 'better'
        if min(vb) > max(va) and nb <= na: return 'worse'
    else:
        if min(vb) > max(va) and nb >= na: return 'better'
        if max(vb) < min(va) and nb <= na: return 'worse'
    return '~'

cols = ['instance', 'dir'] + [f'{l} (solved; median [min-max])' for l in labels] + \
       [f'{l} vs {base}' for l in labels if l != base]
print('| ' + ' | '.join(cols) + ' |')
print('|' + '---|' * len(cols))
for name in order:
    d = direction(name)
    st = {l: stats(res[name].get(l, []), d) for l in labels}
    cells = [name, d]
    for l in labels:
        n, t, v = st[l]
        if not v:
            cells.append(f'{n}/{t}' + (' sat' if n and d == 'sat' else ' –'))
        else:
            cells.append(f'{n}/{t}; {statistics.median(v):g} [{min(v)}-{max(v)}]')
    for l in labels:
        if l != base:
            cells.append(verdict(st[base], st[l], d))
    print('| ' + ' | '.join(cells) + ' |')
