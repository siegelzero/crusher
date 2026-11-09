#!/usr/bin/env python3
"""Independent FlatZinc solution checker (soundness debugging aid).

usage: python3 tests/fzncheck.py model.fzn values.dzn

values.dzn holds `name = value;` per scalar variable, as written by
`CRUSHER_DUMP_ALL=values.dzn ./fzcrusher model.fzn`. Defined variables are
recomputed from their defining constraints, then every ORIGINAL constraint is
evaluated, so translation-level unsoundness (dropped or mistranslated
constraints) shows up as violations. Unsupported constraints are listed as
unchecked."""
import os, re, sys
from collections import Counter

def tokenize(s):
    toks = re.findall(r'\.\.|[\[\]\{\}\(\),]|-?\d+|[A-Za-z_][A-Za-z0-9_]*|"[^"]*"|::|\S', s)
    return toks

def parse_expr(toks, i):
    t = toks[i]
    if t == '[':
        i += 1; elems = []
        while toks[i] != ']':
            e, i = parse_expr(toks, i); elems.append(e)
            if toks[i] == ',': i += 1
        return ('arr', elems), i + 1
    if t == '{':
        i += 1; vals = []
        while toks[i] != '}':
            vals.append(int(toks[i])); i += 1
            if toks[i] == ',': i += 1
        return ('set', set(vals)), i + 1
    if re.fullmatch(r'-?\d+', t):
        if i + 1 < len(toks) and toks[i + 1] == '..':
            return ('set', set(range(int(t), int(toks[i + 2]) + 1))), i + 3
        return ('int', int(t)), i + 1
    if t in ('true', 'false'):
        return ('int', 1 if t == 'true' else 0), i + 1
    return ('id', t), i + 1

def main():
    fzn, vals = sys.argv[1], sys.argv[2]
    V = {}
    for line in open(vals):
        m = re.match(r'\s*(\w+)\s*=\s*(-?\d+|true|false)\s*;', line)
        if m:
            v = m.group(2); V[m.group(1)] = 1 if v == 'true' else 0 if v == 'false' else int(v)
    P, A, cons = {}, {}, []
    text = open(fzn).read()
    for stmt in text.split(';'):
        s = stmt.strip()
        if not s or s.startswith('%') or s.startswith('predicate'): continue
        if s.startswith('constraint'):
            body = s[len('constraint'):].strip()
            m = re.match(r'(\w+)\s*\(', body)
            if not m: continue
            name = m.group(1)
            toks = tokenize(body[m.end():]); i = 0; args = []
            while i < len(toks) and toks[i] != ')':
                e, i = parse_expr(toks, i); args.append(e)
                if i < len(toks) and toks[i] == ',': i += 1
            dm = re.search(r'defines_var\((\w+)\)', body[m.end():])
            cons.append((name, args, dm.group(1) if dm else None)); continue
        if s.startswith('solve'): continue
        # declarations: [array [..] of] [var] type: name [:: ann] [= value]
        m = re.match(r'(array\s*\[[^\]]*\]\s*of\s*)?(var\s+)?(.*?):\s*(\w+)\s*(::[^=]*)?(=\s*(.*))?$', s, re.S)
        if not m: continue
        isArr, isVar, name, val = m.group(1), m.group(2), m.group(4), m.group(7)
        if val is None: continue
        e, _ = parse_expr(tokenize(val), 0)
        if isArr: A[name] = e
        elif not isVar: P[name] = e
        else: P[name] = e   # var with fixed value
    def ev(e):
        k = e[0]
        if k == 'int': return e[1]
        if k == 'set': return e[1]
        if k == 'id':
            n = e[1]
            if n in V: return V[n]
            if n in P: return ev(P[n])
            if n in A: return [ev(x) for x in A[n][1]]
            raise KeyError(n)
        if k == 'arr': return [ev(x) for x in e[1]]
    bad = Counter(); unchecked = Counter(); examples = {}
    def check(name, a):
        g = [ev(x) for x in a]
        if name == 'int_lin_eq': return sum(c*x for c, x in zip(g[0], g[1])) == g[2]
        if name == 'int_lin_le': return sum(c*x for c, x in zip(g[0], g[1])) <= g[2]
        if name == 'int_lin_ne': return sum(c*x for c, x in zip(g[0], g[1])) != g[2]
        if name == 'int_lin_eq_reif': return (sum(c*x for c, x in zip(g[0], g[1])) == g[2]) == bool(g[3])
        if name == 'int_lin_le_reif': return (sum(c*x for c, x in zip(g[0], g[1])) <= g[2]) == bool(g[3])
        if name == 'int_lin_ne_reif': return (sum(c*x for c, x in zip(g[0], g[1])) != g[2]) == bool(g[3])
        if name in ('int_eq', 'bool_eq'): return g[0] == g[1]
        if name in ('int_ne', 'bool_ne'): return g[0] != g[1]
        if name in ('int_le', 'bool_le'): return g[0] <= g[1]
        if name in ('int_lt', 'bool_lt'): return g[0] < g[1]
        if name in ('int_eq_reif', 'bool_eq_reif'): return (g[0] == g[1]) == bool(g[2])
        if name in ('int_ne_reif', 'bool_ne_reif'): return (g[0] != g[1]) == bool(g[2])
        if name in ('int_le_reif', 'bool_le_reif'): return (g[0] <= g[1]) == bool(g[2])
        if name in ('int_lt_reif', 'bool_lt_reif'): return (g[0] < g[1]) == bool(g[2])
        if name == 'bool_clause': return any(g[0]) or not all(g[1])
        if name == 'bool_clause_reif': return (any(g[0]) or not all(g[1])) == bool(g[2])
        if name == 'array_bool_and': return all(g[0]) == bool(g[1])
        if name == 'array_bool_or': return any(g[0]) == bool(g[1])
        if name == 'bool2int': return g[0] == g[1]
        if name == 'bool_not': return g[0] != g[1]
        if name == 'bool_xor': return (g[0] != g[1]) == bool(g[2])
        if name == 'int_times': return g[0]*g[1] == g[2]
        if name == 'int_plus': return g[0]+g[1] == g[2]
        if name == 'int_max': return max(g[0], g[1]) == g[2]
        if name == 'int_min': return min(g[0], g[1]) == g[2]
        if name == 'int_abs': return abs(g[0]) == g[1]
        if name == 'int_div': return int(g[0]/g[1]) == g[2] if g[1] else False
        if name == 'int_mod': return (g[0] - g[1]*int(g[0]/g[1])) == g[2] if g[1] else False
        if name in ('array_int_element', 'array_var_int_element', 'array_bool_element', 'array_var_bool_element'):
            return 1 <= g[0] <= len(g[1]) and g[1][g[0]-1] == g[2]
        if name == 'array_int_maximum': return g[0] == max(g[1])
        if name == 'array_int_minimum': return g[0] == min(g[1])
        if name == 'set_in': return g[0] in g[1]
        if name == 'set_in_reif': return (g[0] in g[1]) == bool(g[2])
        if name in ('fzn_all_different_int', 'fzn_alldifferent'): return len(set(g[0])) == len(g[0])
        if name == 'crusher_circuit':
            s = g[0]; n = len(s); off = 0 if 0 in s else 1
            seen = set(); cur = 0
            for _ in range(n):
                if cur in seen: return False
                seen.add(cur); cur = s[cur] - off
                if not (0 <= cur < n): return False
            return cur == 0 and len(seen) == n
        if name == 'fzn_table_int':
            x, t = g[0], g[1]; n = len(x)
            return any(t[i:i+n] == x for i in range(0, len(t), n))
        if name == 'crusher_subcircuit':
            s = g[0]; n = len(s); off = 1 if 0 not in s else 0
            if not all(0 <= v - off < n for v in s): return False
            moved = [i for i in range(n) if s[i] - off != i]
            if not moved: return True
            seen = set(); cur = moved[0]
            while cur not in seen:
                seen.add(cur); cur = s[cur] - off
            return cur == moved[0] and seen == set(moved)
        if name == 'crusher_disjunctive_opt':
            s, o, d = g[0], g[1], g[2]
            iv = [(s[i], s[i] + d[i]) for i in range(len(s)) if o[i] and d[i] > 0]
            for a in range(len(iv)):
                for b in range(a + 1, len(iv)):
                    if iv[a][0] < iv[b][1] and iv[b][0] < iv[a][1]: return False
            return True
        if name == 'fzn_disjunctive_strict':
            s, d = g[0], g[1]
            for i in range(len(s)):
                for j in range(i+1, len(s)):
                    if not (s[i]+d[i] <= s[j] or s[j]+d[j] <= s[i]): return False
            return True
        return None
    # Recompute defined variables from their defining constraints (fixpoint), so
    # values of consumed/eliminated intermediates don't produce false alarms.
    def define(name, a, dv):
        g = lambda k: ev(a[k])
        if name.endswith('_reif'):
            base = name[:-5]
            # evaluate the relation with a dummy result and take truth value
            if base in ('int_lin_eq', 'int_lin_le', 'int_lin_ne'):
                lhs = sum(c*x for c, x in zip(g(0), g(1))); r = g(2)
                return int({'int_lin_eq': lhs == r, 'int_lin_le': lhs <= r, 'int_lin_ne': lhs != r}[base])
            x, y = g(0), g(1)
            ops = {'int_eq': x == y, 'bool_eq': x == y, 'int_ne': x != y, 'bool_ne': x != y,
                   'int_le': x <= y, 'bool_le': x <= y, 'int_lt': x < y, 'bool_lt': x < y}
            if base in ops: return int(ops[base])
            if base == 'set_in': return int(x in y)
            if base == 'bool_clause': return int(any(g(0)) or not all(g(1)))
            return None
        if name == 'array_bool_and': return int(all(g(0)))
        if name == 'array_bool_or': return int(any(g(0)))
        if name == 'bool2int': return g(0)
        if name == 'bool_not': return 1 - g(0) if dv == a[1][1] else 1 - g(1)
        if name == 'int_times': return g(0)*g(1)
        if name == 'int_plus': return g(0)+g(1)
        if name == 'int_max': return max(g(0), g(1))
        if name == 'int_min': return min(g(0), g(1))
        if name == 'int_abs': return abs(g(0))
        if name == 'int_div': return int(g(0)/g(1)) if g(1) else None
        if name == 'int_mod': return (g(0) - g(1)*int(g(0)/g(1))) if g(1) else None
        if name in ('array_int_element', 'array_var_int_element', 'array_bool_element', 'array_var_bool_element'):
            i, arr = g(0), g(1)
            return arr[i-1] if 1 <= i <= len(arr) else None
        if name == 'array_int_maximum': return max(g(1))
        if name == 'array_int_minimum': return min(g(1))
        if name == 'int_lin_eq':
            cs = g(0); xs = a[1][1]; r = g(2)
            k = [j for j, x in enumerate(xs) if x == ('id', dv)]
            if len(k) != 1 or abs(cs[k[0]]) != 1: return None
            rest = sum(cs[j]*ev(xs[j]) for j in range(len(xs)) if j != k[0])
            return (r - rest) * cs[k[0]]
        return None
    for it in range(20):
        changed = 0
        for name, a, dv in cons:
            if dv is None: continue
            try:
                val = define(name, a, dv)
            except (KeyError, TypeError, IndexError, ZeroDivisionError):
                continue
            if val is not None and V.get(dv) != val:
                V[dv] = val; changed += 1
        if changed == 0: break
    for name, a, dv in cons:
        try:
            r = check(name, a)
        except KeyError as ex:
            unchecked[name + ' (missing ' + str(ex) + ')'] += 1; continue
        if r is None: unchecked[name] += 1
        elif not r:
            bad[name] += 1
            if name not in examples: examples[name] = (name, a)
            if os.environ.get('FZNCHECK_ALL'):
                print('VIOLATED', name, [ev(x) if not (x[0] == 'id' and x[1] in A and len(A[x[1]][1]) > 40) else x[1] for x in a])
    print('violated:', dict(bad))
    for n, (name, a) in examples.items():
        print('  e.g.', name, str(a)[:300])
    print('unchecked:', dict(unchecked))

main()
