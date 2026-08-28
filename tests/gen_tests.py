#!/usr/bin/env python3
"""Generate SnakeFight's Lean test suite by running each program under CPython.

Every expectation in SnakeFight/Tests.lean comes from actually executing the
program with the `python3` on PATH, so the suite is a differential test against
CPython rather than a record of whatever SnakeFight currently does.

Usage:  python3 tests/gen_tests.py           # rewrite SnakeFight/Tests.lean
        python3 tests/gen_tests.py --check    # just report CPython's output
"""

import subprocess, sys, textwrap, pathlib

# (name, source) -- programs expected to finish normally.
CASES = [
("arithmetic", """
print(1 + 2 * 3, (1 + 2) * 3, 7 - 2 - 1)
print(7 // 2, -7 // 2, 7 // -2, -7 // -2)
print(7 % 2, -7 % 2, 7 % -2, -7 % -2)
print(2 ** 10, 2 ** 0, (-3) ** 3)
print(2 ** 64)
print(divmod(-7, 2), divmod(7, 2))
print(-(-5), +5, ~5, abs(-9))
print(1 << 10, 1024 >> 3, 12 & 10, 12 | 10, 12 ^ 10)
"""),

("comparisons", """
print(1 == 1, 1 != 2, 1 < 2, 2 <= 2, 3 > 4, 3 >= 3)
print(0 <= 1 < 2, 0 < 1 > 2, 1 == 1 == 1)
print(1 == True, 0 == False, 1 is 1, None is None, None is not 3)
print('a' < 'b', 'abc' < 'abd', 'Z' < 'a')
print((1, 2) < (1, 3), (1, 2) == (1, 2), [1, 2] == [1, 2])
"""),

("truthiness", """
print(bool(0), bool(1), bool(''), bool('x'), bool([]), bool([0]), bool({}), bool(None))
print(not 0, not 'x', not [])
print(1 and 2, 0 and 2, 1 or 2, 0 or 2, '' or 'fallback', [] or 0)
print(None or 'x', 'a' and 'b')
"""),

("strings", """
s = 'Hello, World'
print(s, len(s))
print(s[0], s[-1], s[1:5], s[:5], s[7:], s[-5:])
print(s.upper(), s.lower())
print('  pad  '.strip() + '|')
print(s.split(', '), 'a b  c'.split())
print('-'.join(['a', 'b', 'c']))
print(s.startswith('Hello'), s.endswith('d'), 'World' in s, 'x' in s)
print(s.replace('l', 'L'), s.find('World'), s.find('zzz'))
print('ab' * 3, 3 * 'ab')
print(str(42) + '!', int('42') + 1, int('-17'))
print(ord('A'), chr(66), '7'.isdigit(), 'a7'.isalpha())
print(repr('quoted'), repr("it's"))
"""),

("lists", """
xs = [3, 1, 2]
print(xs, len(xs), xs[0], xs[-1])
xs.append(4)
xs.insert(0, 9)
print(xs)
print(xs.pop(), xs.pop(0), xs)
xs.sort()
print(xs)
xs.reverse()
print(xs)
print(xs + [7, 8], [0] * 3, xs * 2)
print(xs[1:], xs[:1], xs[1:2])
ys = [1, 2, 3]
print(ys.index(2), ys.count(2), 2 in ys, 5 in ys)
ys.remove(2)
print(ys)
ys.extend([8, 9])
print(ys, sum(ys), min(ys), max(ys), sorted([3, 1, 2]))
zs = [[1, 2], [3]]
print(zs, len(zs[0]))
"""),

("aliasing", """
a = [1, 2]
b = a
b.append(3)
print(a, b, a is b, a == b)
c = a + []
c.append(4)
print(a, c, a is c)
def mutate(lst):
    lst.append(99)
def rebind(lst):
    lst = [0]
mutate(a)
rebind(a)
print(a)
d = {'k': [1]}
e = d
e['k'].append(2)
print(d, d is e)
"""),

("dicts", """
d = {'a': 1, 'b': 2}
print(d, len(d), d['a'])
d['c'] = 3
d['a'] = 10
print(d)
print('a' in d, 'z' in d, d.get('z'), d.get('z', 0))
print(sorted(d.keys()), sorted(d.values()))
del d['b']
print(d)
print(d.pop('c'), d)
d.update({'x': 1})
print(d)
counts = {}
for ch in 'hello':
    counts[ch] = counts.get(ch, 0) + 1
print(counts)
for k in sorted(counts.keys()):
    print(k, counts[k])
"""),

("tuples", """
t = (1, 2, 3)
print(t, len(t), t[0], t[-1], t[1:])
a, b = 1, 2
a, b = b, a
print(a, b)
x, y, z = t
print(x + y + z)
print((), (1,), (1, 2) + (3,), (0,) * 2)
pairs = [(1, 'a'), (2, 'b')]
for n, s in pairs:
    print(n, s)
print(tuple([1, 2]), list((1, 2)))
"""),

("control_flow", """
for i in range(3):
    print('i', i)
for i in range(2, 8, 2):
    print('step', i)
for i in range(3, 0, -1):
    print('down', i)
n = 0
while n < 3:
    n += 1
    if n == 2:
        continue
    print('n', n)
total = 0
for i in range(10):
    if i > 4:
        break
    total += i
print('total', total)
for i in range(3):
    for j in range(3):
        if j == 1:
            break
        print(i, j)
if total > 5:
    print('big')
elif total > 100:
    print('unreachable')
else:
    print('small')
print([x for x in range(6) if x % 2 == 0])
print([x * x for x in [1, 2, 3]])
print([(i, c) for i, c in enumerate('ab')])
"""),

("functions", """
def fact(n):
    if n <= 1:
        return 1
    return n * fact(n - 1)
print(fact(10))
def fib(n):
    if n < 2:
        return n
    return fib(n - 1) + fib(n - 2)
print([fib(i) for i in range(12)])
def greet(name, greeting='hi', punct='!'):
    return greeting + ' ' + name + punct
print(greet('bob'), greet('bob', 'yo'), greet('bob', punct='?'))
print(greet(greeting='hey', name='ann'))
def noret():
    pass
print(noret())
def multi(a, b):
    return a + b, a - b
print(multi(5, 3))
def outer():
    x = 10
    def inner(y):
        return x + y
    return inner(5)
print(outer())
f = lambda a, b=2: a * b
print(f(3), f(3, 4))
def apply(g, v):
    return g(v)
print(apply(lambda v: v + 1, 41))
counter = 0
def bump():
    global counter
    counter += 1
bump()
bump()
print(counter)
"""),

("exceptions", """
try:
    x = 1 // 0
except ZeroDivisionError as e:
    print('zde:', e)
try:
    [1][5]
except IndexError:
    print('index')
try:
    {}['k']
except KeyError:
    print('key')
try:
    'a' + 1
except TypeError:
    print('type')
try:
    raise ValueError('boom')
except ValueError as e:
    print('value:', e)
try:
    raise ValueError('sub')
except Exception as e:
    print('base caught:', e)
try:
    print('body')
except ValueError:
    print('skipped')
else:
    print('else runs')
finally:
    print('finally runs')
def f():
    try:
        return 'from try'
    finally:
        print('finally on return')
print(f())
try:
    try:
        raise KeyError('inner')
    except IndexError:
        print('wrong handler')
except KeyError as e:
    print('outer got', e)
try:
    assert 1 == 1
    print('assert ok')
    assert 1 == 2, 'nope'
except AssertionError as e:
    print('assertion:', e)
def risky(n):
    if n < 0:
        raise ValueError('negative')
    return n
for v in [1, -1]:
    try:
        print(risky(v))
    except ValueError as e:
        print('caught', e)
"""),

("builtins", """
print(len('abc'), len([1, 2]), len({'a': 1}), len((1, 2, 3)))
print(sum([1, 2, 3]), sum([1, 2], 10))
print(min([3, 1, 2]), max([3, 1, 2]), min(4, 2), max(4, 2))
print(sorted([3, 1, 2]), sorted(['b', 'a']))
print(list(range(4)), list('abc'), list((1, 2)))
print(list(reversed([1, 2, 3])))
print(list(enumerate(['a', 'b'])))
print(list(zip([1, 2], 'ab')))
print(any([0, 1]), any([]), all([1, 1]), all([1, 0]))
print(isinstance(1, int), isinstance('a', str), isinstance(True, int), isinstance(1, str))
print(type(1), type('a'), type([]), type({}), type(None))
print(str(None), str(True), str([1, 'a']))
print(dict([(1, 'a')]))
"""),

("printing", r"""
print()
print('a', 'b', 'c')
print(1, 2 == 2)
print([1, 'two', True, None])
print({'a': [1, (2,)]})
print((1,), (1, 2))
print([[]], [{}], {1: {}})
print('tab\tnewline-escaped')
print(repr('a\nb'))
"""),

("scoping", """
x = 'global'
def read():
    return x
def shadow():
    x = 'local'
    return x
print(read(), shadow(), x)
def make_adder(n):
    def add(v):
        return v + n
    return add
add2 = make_adder(2)
add10 = make_adder(10)
print(add2(1), add10(1))
def nested():
    a = 1
    def mid():
        b = 2
        def inner():
            return a + b
        return inner()
    return mid()
print(nested())
"""),

("mutation_in_place", """
xs = [1, 2, 3]
xs[0] = 10
xs[-1] = 30
print(xs)
xs[1] += 5
print(xs)
d = {'n': 1}
d['n'] += 1
d['m'] = d.get('m', 0) + 5
print(d)
grid = [[0, 0], [0, 0]]
grid[0][1] = 1
print(grid)
del xs[0]
print(xs)
"""),

("algorithms", """
def bubble(xs):
    ys = xs + []
    n = len(ys)
    for i in range(n):
        for j in range(n - i - 1):
            if ys[j] > ys[j + 1]:
                tmp = ys[j]
                ys[j] = ys[j + 1]
                ys[j + 1] = tmp
    return ys
print(bubble([5, 2, 9, 1, 5, 6]))
def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True
print([n for n in range(30) if is_prime(n)])
def gcd(a, b):
    while b != 0:
        t = b
        b = a % b
        a = t
    return a
print(gcd(48, 18), gcd(17, 5))
def word_count(text):
    counts = {}
    for w in text.split():
        counts[w] = counts.get(w, 0) + 1
    return counts
wc = word_count('the cat the hat')
for k in sorted(wc.keys()):
    print(k, wc[k])
def binary_search(xs, target):
    lo = 0
    hi = len(xs) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if xs[mid] == target:
            return mid
        if xs[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1
sorted_xs = [1, 3, 5, 7, 9]
print(binary_search(sorted_xs, 7), binary_search(sorted_xs, 4))
def fizzbuzz(n):
    out = []
    for i in range(1, n + 1):
        if i % 15 == 0:
            out.append('FizzBuzz')
        elif i % 3 == 0:
            out.append('Fizz')
        elif i % 5 == 0:
            out.append('Buzz')
        else:
            out.append(str(i))
    return out
print(fizzbuzz(15))
"""),

("stack_machine", """
def evaluate(prog):
    stack = []
    for tok in prog.split():
        if tok == '+':
            b = stack.pop()
            a = stack.pop()
            stack.append(a + b)
        elif tok == '*':
            b = stack.pop()
            a = stack.pop()
            stack.append(a * b)
        elif tok == '-':
            b = stack.pop()
            a = stack.pop()
            stack.append(a - b)
        else:
            stack.append(int(tok))
    return stack.pop()
print(evaluate('2 3 +'))
print(evaluate('2 3 + 4 *'))
print(evaluate('10 2 3 * -'))
"""),

("more_strings", r"""
print('a,b,,c'.split(','))
print(''.join([]), '|'.join(['x']))
print('Hello'[0:0], len('Hello'[2:2]))
print('x' * 0, 'x' * -1, '' == "")
print('%s' == "%s")
print(str([]), str({}), str(()))
print('aXbXc'.replace('X', ''), 'aaa'.count('a'), 'aaa'.count('aa'))
print('  a b  '.split())
print('CamelCase'.lower().upper())
"""),

("slices_and_negatives", """
xs = [0, 1, 2, 3, 4]
print(xs[-2:], xs[:-2], xs[1:-1], xs[10:], xs[-10:])
print(xs[3:1], len(xs[3:1]))
s = 'abcdef'
print(s[-3:], s[:-3], s[2:4], s[100:])
t = (1, 2, 3)
print(t[-1], t[:2], t[1:])
"""),

("nested_data", """
grid = [[1, 2], [3, 4]]
print(grid[1][0], len(grid), len(grid[0]))
for row in grid:
    for cell in row:
        print(cell)
d = {'a': {'b': [1, 2]}}
print(d['a']['b'][1])
d['a']['b'].append(3)
print(d)
matrix = [[0] * 2, [0] * 2]
matrix[0][0] = 9
print(matrix)
pairs = {(1, 2): 'x'}
print(pairs[(1, 2)])
"""),

("identity_and_membership", """
a = [1]
b = [1]
print(a == b, a is b, a is not b)
print(None is None, None == None)
print(1 in [1, 2], 3 not in [1, 2], 'a' in {'a': 1}, 'b' not in {'a': 1})
print((1, 2) in [(1, 2)], [1] in [[1]])
print('lo' in 'hello', 'z' not in 'hello')
"""),

("keyword_and_default_args", """
def f(a, b=2, c=3):
    return (a, b, c)
print(f(1), f(1, 9), f(1, 9, 8), f(1, c=7), f(a=1, c=7), f(c=7, a=1))
def g(xs=None):
    if xs is None:
        return 'none'
    return len(xs)
print(g(), g([1, 2]))
def h(n):
    return n * 2
print(h(n=21))
"""),

("mutation_via_calls", """
def add_item(lst, v):
    lst.append(v)
    return lst
xs = []
add_item(xs, 1)
add_item(xs, 2)
print(xs)
def swap_in_dict(d, k1, k2):
    tmp = d[k1]
    d[k1] = d[k2]
    d[k2] = tmp
d = {'a': 1, 'b': 2}
swap_in_dict(d, 'a', 'b')
print(d)
def build(n):
    out = []
    for i in range(n):
        out.append([i] * i)
    return out
print(build(4))
"""),

("del_and_pop", """
xs = [1, 2, 3, 4]
del xs[1]
print(xs)
d = {'a': 1, 'b': 2, 'c': 3}
del d['b']
print(d)
print(d.pop('a'), d)
print(xs.pop(0), xs.pop(), xs)
ys = [1, 2, 3]
ys.clear()
print(ys, len(ys))
"""),

("returns_and_recursion", """
def collatz_len(n):
    steps = 0
    while n != 1:
        if n % 2 == 0:
            n = n // 2
        else:
            n = 3 * n + 1
        steps += 1
    return steps
print([collatz_len(n) for n in range(1, 10)])
def power(base, exp):
    if exp == 0:
        return 1
    half = power(base, exp // 2)
    if exp % 2 == 0:
        return half * half
    return base * half * half
print(power(2, 20), power(3, 5))
def ackermann_ish(m, n):
    if m == 0:
        return n + 1
    if n == 0:
        return ackermann_ish(m - 1, 1)
    return ackermann_ish(m - 1, ackermann_ish(m, n - 1))
print(ackermann_ish(2, 3))
def early(xs):
    for x in xs:
        if x < 0:
            return 'negative'
    return 'all ok'
print(early([1, 2]), early([1, -2]))
"""),

("exception_control", """
def parse_int(s):
    try:
        return int(s)
    except ValueError:
        return None
print(parse_int('12'), parse_int('nope'))
log = []
def risky(n):
    try:
        if n == 0:
            raise ZeroDivisionError('zero')
        log.append('ok ' + str(n))
        return 10 // n
    except ZeroDivisionError as e:
        log.append('err ' + str(e))
        return -1
    finally:
        log.append('done ' + str(n))
print(risky(2), risky(0))
print(log)
def reraise():
    try:
        raise ValueError('inner')
    except ValueError as e:
        raise RuntimeError('wrapped: ' + str(e))
try:
    reraise()
except RuntimeError as e:
    print('got', e)
for v in ['1', 'x', '3']:
    try:
        print(int(v) * 2)
    except ValueError:
        print('bad', v)
"""),
]

# (name, source, expected SnakeFight exception message)
FAILING = [
("uncaught_value_error", "print('before')\nraise ValueError('boom')\n", "ValueError: boom"),
("uncaught_name_error", "print(missing)\n", "NameError: name 'missing' is not defined"),
("uncaught_zero_div", "print(1)\nprint(1 // 0)\n", "ZeroDivisionError: integer division or modulo by zero"),
("uncaught_key_error", "d = {}\nprint(d['k'])\n", "KeyError: 'k'"),
("uncaught_assert", "assert 1 == 2, 'bad'\n", "AssertionError: bad"),
("uncaught_type_error", "print(len(1))\n", "TypeError: object of type 'int' has no len()"),
]


def cpython_out(src):
    r = subprocess.run([sys.executable, "-c", src], capture_output=True, text=True, timeout=30)
    if r.returncode != 0:
        raise SystemExit(f"CPython rejected a test program:\n{src}\n{r.stderr}")
    lines = r.stdout.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def lean_list(xs):
    return "[" + ", ".join(lean_str(x) for x in xs) + "]"


def main():
    entries = []
    for name, src in CASES:
        out = cpython_out(src)
        entries.append((name, src, out, None))
    for name, src, exc in FAILING:
        r = subprocess.run([sys.executable, "-c", src], capture_output=True, text=True, timeout=30)
        lines = r.stdout.split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        entries.append((name, src, lines, exc))

    if "--check" in sys.argv:
        for name, src, out, exc in entries:
            print(name, "->", out, exc or "")
        return

    body = []
    for name, src, out, exc in entries:
        raises = "" if exc is None else f",\n    raises := some {lean_str(exc)}"
        body.append(f"""  {{ name := {lean_str(name)},
    src := {lean_str(src)},
    out := {lean_list(out)}{raises} }}""")

    generated = "/-- The test corpus.  Expectations are CPython's actual output; see\n" \
                "`tests/gen_tests.py`, which produced this list. -/\ndef tests : List TestCase := [\n" \
                + ",\n".join(body) + "\n]\n"

    path = pathlib.Path("SnakeFight/Tests.lean")
    text = path.read_text()
    marker = "-- BEGIN GENERATED TESTS"
    end = "-- END GENERATED TESTS"
    head = text.split(marker)[0]
    tail = text.split(end)[1] if end in text else "\nend SnakeFight\n"
    path.write_text(head + marker + "\n\n" + generated + "\n" + end + tail)
    print(f"wrote {len(entries)} cases to {path}")


main()
