import SnakeFight.Interp

/-!
# Test suite

Each case is a Python program together with the output CPython produces for it.
`snake-fight test` runs them all.  The cases were checked against CPython 3 --
this is a differential test suite, not a description of what SnakeFight happens
to do.
-/

namespace SnakeFight

/-- One test: source, expected printed lines, and optionally the exception it
should die with. -/
structure TestCase where
  /-- Name shown in the report. -/
  name : String
  /-- Python source. -/
  src : String
  /-- Expected lines on stdout. -/
  out : List String
  /-- Expected uncaught exception message, if the program is meant to fail. -/
  raises : Option String := Option.none
  deriving Inhabited

/-- Check one case, returning an error description on failure. -/
def TestCase.check (t : TestCase) : Option String :=
  match parse t.src with
  | .error e => some s!"parse error: {e}"
  | .ok prog =>
    match runOutcome 400000 prog, t.raises with
    | .ok out, Option.none =>
      if out == t.out then Option.none
      else some s!"expected output {repr t.out}, got {repr out}"
    | .ok out, some ex => some s!"expected exception {ex}, but it finished with {repr out}"
    | .error out msg, some ex =>
      if msg == ex then
        if out == t.out then Option.none
        else some s!"right exception, but expected output {repr t.out}, got {repr out}"
      else some s!"expected exception {repr ex}, got {repr msg}"
    | .error _ msg, Option.none => some s!"unexpected exception: {msg}"
    | .timeout out, _ => some s!"ran out of fuel (output so far: {repr out})"

-- BEGIN GENERATED TESTS

/-- The test corpus.  Expectations are CPython's actual output; see
`tests/gen_tests.py`, which produced this list. -/
def tests : List TestCase := [
  { name := "arithmetic",
    src := "\nprint(1 + 2 * 3, (1 + 2) * 3, 7 - 2 - 1)\nprint(7 // 2, -7 // 2, 7 // -2, -7 // -2)\nprint(7 % 2, -7 % 2, 7 % -2, -7 % -2)\nprint(2 ** 10, 2 ** 0, (-3) ** 3)\nprint(2 ** 64)\nprint(divmod(-7, 2), divmod(7, 2))\nprint(-(-5), +5, ~5, abs(-9))\nprint(1 << 10, 1024 >> 3, 12 & 10, 12 | 10, 12 ^ 10)\n",
    out := ["7 9 4", "3 -4 -4 3", "1 1 -1 -1", "1024 1 -27", "18446744073709551616", "(-4, 1) (3, 1)", "5 5 -6 9", "1024 128 8 14 6"] },
  { name := "comparisons",
    src := "\nprint(1 == 1, 1 != 2, 1 < 2, 2 <= 2, 3 > 4, 3 >= 3)\nprint(0 <= 1 < 2, 0 < 1 > 2, 1 == 1 == 1)\nprint(1 == True, 0 == False, 1 is 1, None is None, None is not 3)\nprint('a' < 'b', 'abc' < 'abd', 'Z' < 'a')\nprint((1, 2) < (1, 3), (1, 2) == (1, 2), [1, 2] == [1, 2])\n",
    out := ["True True True True False True", "True False True", "True True True True True", "True True True", "True True True"] },
  { name := "truthiness",
    src := "\nprint(bool(0), bool(1), bool(''), bool('x'), bool([]), bool([0]), bool({}), bool(None))\nprint(not 0, not 'x', not [])\nprint(1 and 2, 0 and 2, 1 or 2, 0 or 2, '' or 'fallback', [] or 0)\nprint(None or 'x', 'a' and 'b')\n",
    out := ["False True False True False True False False", "True False True", "2 0 1 2 fallback 0", "x b"] },
  { name := "strings",
    src := "\ns = 'Hello, World'\nprint(s, len(s))\nprint(s[0], s[-1], s[1:5], s[:5], s[7:], s[-5:])\nprint(s.upper(), s.lower())\nprint('  pad  '.strip() + '|')\nprint(s.split(', '), 'a b  c'.split())\nprint('-'.join(['a', 'b', 'c']))\nprint(s.startswith('Hello'), s.endswith('d'), 'World' in s, 'x' in s)\nprint(s.replace('l', 'L'), s.find('World'), s.find('zzz'))\nprint('ab' * 3, 3 * 'ab')\nprint(str(42) + '!', int('42') + 1, int('-17'))\nprint(ord('A'), chr(66), '7'.isdigit(), 'a7'.isalpha())\nprint(repr('quoted'), repr(\"it's\"))\n",
    out := ["Hello, World 12", "H d ello Hello World World", "HELLO, WORLD hello, world", "pad|", "['Hello', 'World'] ['a', 'b', 'c']", "a-b-c", "True True True False", "HeLLo, WorLd 7 -1", "ababab ababab", "42! 43 -17", "65 B True False", "'quoted' \"it's\""] },
  { name := "lists",
    src := "\nxs = [3, 1, 2]\nprint(xs, len(xs), xs[0], xs[-1])\nxs.append(4)\nxs.insert(0, 9)\nprint(xs)\nprint(xs.pop(), xs.pop(0), xs)\nxs.sort()\nprint(xs)\nxs.reverse()\nprint(xs)\nprint(xs + [7, 8], [0] * 3, xs * 2)\nprint(xs[1:], xs[:1], xs[1:2])\nys = [1, 2, 3]\nprint(ys.index(2), ys.count(2), 2 in ys, 5 in ys)\nys.remove(2)\nprint(ys)\nys.extend([8, 9])\nprint(ys, sum(ys), min(ys), max(ys), sorted([3, 1, 2]))\nzs = [[1, 2], [3]]\nprint(zs, len(zs[0]))\n",
    out := ["[3, 1, 2] 3 3 2", "[9, 3, 1, 2, 4]", "4 9 [3, 1, 2]", "[1, 2, 3]", "[3, 2, 1]", "[3, 2, 1, 7, 8] [0, 0, 0] [3, 2, 1, 3, 2, 1]", "[2, 1] [3] [2]", "1 1 True False", "[1, 3]", "[1, 3, 8, 9] 21 1 9 [1, 2, 3]", "[[1, 2], [3]] 2"] },
  { name := "aliasing",
    src := "\na = [1, 2]\nb = a\nb.append(3)\nprint(a, b, a is b, a == b)\nc = a + []\nc.append(4)\nprint(a, c, a is c)\ndef mutate(lst):\n    lst.append(99)\ndef rebind(lst):\n    lst = [0]\nmutate(a)\nrebind(a)\nprint(a)\nd = {'k': [1]}\ne = d\ne['k'].append(2)\nprint(d, d is e)\n",
    out := ["[1, 2, 3] [1, 2, 3] True True", "[1, 2, 3] [1, 2, 3, 4] False", "[1, 2, 3, 99]", "{'k': [1, 2]} True"] },
  { name := "dicts",
    src := "\nd = {'a': 1, 'b': 2}\nprint(d, len(d), d['a'])\nd['c'] = 3\nd['a'] = 10\nprint(d)\nprint('a' in d, 'z' in d, d.get('z'), d.get('z', 0))\nprint(sorted(d.keys()), sorted(d.values()))\ndel d['b']\nprint(d)\nprint(d.pop('c'), d)\nd.update({'x': 1})\nprint(d)\ncounts = {}\nfor ch in 'hello':\n    counts[ch] = counts.get(ch, 0) + 1\nprint(counts)\nfor k in sorted(counts.keys()):\n    print(k, counts[k])\n",
    out := ["{'a': 1, 'b': 2} 2 1", "{'a': 10, 'b': 2, 'c': 3}", "True False None 0", "['a', 'b', 'c'] [2, 3, 10]", "{'a': 10, 'c': 3}", "3 {'a': 10}", "{'a': 10, 'x': 1}", "{'h': 1, 'e': 1, 'l': 2, 'o': 1}", "e 1", "h 1", "l 2", "o 1"] },
  { name := "tuples",
    src := "\nt = (1, 2, 3)\nprint(t, len(t), t[0], t[-1], t[1:])\na, b = 1, 2\na, b = b, a\nprint(a, b)\nx, y, z = t\nprint(x + y + z)\nprint((), (1,), (1, 2) + (3,), (0,) * 2)\npairs = [(1, 'a'), (2, 'b')]\nfor n, s in pairs:\n    print(n, s)\nprint(tuple([1, 2]), list((1, 2)))\n",
    out := ["(1, 2, 3) 3 1 3 (2, 3)", "2 1", "6", "() (1,) (1, 2, 3) (0, 0)", "1 a", "2 b", "(1, 2) [1, 2]"] },
  { name := "control_flow",
    src := "\nfor i in range(3):\n    print('i', i)\nfor i in range(2, 8, 2):\n    print('step', i)\nfor i in range(3, 0, -1):\n    print('down', i)\nn = 0\nwhile n < 3:\n    n += 1\n    if n == 2:\n        continue\n    print('n', n)\ntotal = 0\nfor i in range(10):\n    if i > 4:\n        break\n    total += i\nprint('total', total)\nfor i in range(3):\n    for j in range(3):\n        if j == 1:\n            break\n        print(i, j)\nif total > 5:\n    print('big')\nelif total > 100:\n    print('unreachable')\nelse:\n    print('small')\nprint([x for x in range(6) if x % 2 == 0])\nprint([x * x for x in [1, 2, 3]])\nprint([(i, c) for i, c in enumerate('ab')])\n",
    out := ["i 0", "i 1", "i 2", "step 2", "step 4", "step 6", "down 3", "down 2", "down 1", "n 1", "n 3", "total 10", "0 0", "1 0", "2 0", "big", "[0, 2, 4]", "[1, 4, 9]", "[(0, 'a'), (1, 'b')]"] },
  { name := "functions",
    src := "\ndef fact(n):\n    if n <= 1:\n        return 1\n    return n * fact(n - 1)\nprint(fact(10))\ndef fib(n):\n    if n < 2:\n        return n\n    return fib(n - 1) + fib(n - 2)\nprint([fib(i) for i in range(12)])\ndef greet(name, greeting='hi', punct='!'):\n    return greeting + ' ' + name + punct\nprint(greet('bob'), greet('bob', 'yo'), greet('bob', punct='?'))\nprint(greet(greeting='hey', name='ann'))\ndef noret():\n    pass\nprint(noret())\ndef multi(a, b):\n    return a + b, a - b\nprint(multi(5, 3))\ndef outer():\n    x = 10\n    def inner(y):\n        return x + y\n    return inner(5)\nprint(outer())\nf = lambda a, b=2: a * b\nprint(f(3), f(3, 4))\ndef apply(g, v):\n    return g(v)\nprint(apply(lambda v: v + 1, 41))\ncounter = 0\ndef bump():\n    global counter\n    counter += 1\nbump()\nbump()\nprint(counter)\n",
    out := ["3628800", "[0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]", "hi bob! yo bob! hi bob?", "hey ann!", "None", "(8, 2)", "15", "6 12", "42", "2"] },
  { name := "exceptions",
    src := "\ntry:\n    x = 1 // 0\nexcept ZeroDivisionError as e:\n    print('zde:', e)\ntry:\n    [1][5]\nexcept IndexError:\n    print('index')\ntry:\n    {}['k']\nexcept KeyError:\n    print('key')\ntry:\n    'a' + 1\nexcept TypeError:\n    print('type')\ntry:\n    raise ValueError('boom')\nexcept ValueError as e:\n    print('value:', e)\ntry:\n    raise ValueError('sub')\nexcept Exception as e:\n    print('base caught:', e)\ntry:\n    print('body')\nexcept ValueError:\n    print('skipped')\nelse:\n    print('else runs')\nfinally:\n    print('finally runs')\ndef f():\n    try:\n        return 'from try'\n    finally:\n        print('finally on return')\nprint(f())\ntry:\n    try:\n        raise KeyError('inner')\n    except IndexError:\n        print('wrong handler')\nexcept KeyError as e:\n    print('outer got', e)\ntry:\n    assert 1 == 1\n    print('assert ok')\n    assert 1 == 2, 'nope'\nexcept AssertionError as e:\n    print('assertion:', e)\ndef risky(n):\n    if n < 0:\n        raise ValueError('negative')\n    return n\nfor v in [1, -1]:\n    try:\n        print(risky(v))\n    except ValueError as e:\n        print('caught', e)\n",
    out := ["zde: integer division or modulo by zero", "index", "key", "type", "value: boom", "base caught: sub", "body", "else runs", "finally runs", "finally on return", "from try", "outer got 'inner'", "assert ok", "assertion: nope", "1", "caught negative"] },
  { name := "builtins",
    src := "\nprint(len('abc'), len([1, 2]), len({'a': 1}), len((1, 2, 3)))\nprint(sum([1, 2, 3]), sum([1, 2], 10))\nprint(min([3, 1, 2]), max([3, 1, 2]), min(4, 2), max(4, 2))\nprint(sorted([3, 1, 2]), sorted(['b', 'a']))\nprint(list(range(4)), list('abc'), list((1, 2)))\nprint(list(reversed([1, 2, 3])))\nprint(list(enumerate(['a', 'b'])))\nprint(list(zip([1, 2], 'ab')))\nprint(any([0, 1]), any([]), all([1, 1]), all([1, 0]))\nprint(isinstance(1, int), isinstance('a', str), isinstance(True, int), isinstance(1, str))\nprint(type(1), type('a'), type([]), type({}), type(None))\nprint(str(None), str(True), str([1, 'a']))\nprint(dict([(1, 'a')]))\n",
    out := ["3 2 1 3", "6 13", "1 3 2 4", "[1, 2, 3] ['a', 'b']", "[0, 1, 2, 3] ['a', 'b', 'c'] [1, 2]", "[3, 2, 1]", "[(0, 'a'), (1, 'b')]", "[(1, 'a'), (2, 'b')]", "True False True False", "True True True False", "<class 'int'> <class 'str'> <class 'list'> <class 'dict'> <class 'NoneType'>", "None True [1, 'a']", "{1: 'a'}"] },
  { name := "printing",
    src := "\nprint()\nprint('a', 'b', 'c')\nprint(1, 2 == 2)\nprint([1, 'two', True, None])\nprint({'a': [1, (2,)]})\nprint((1,), (1, 2))\nprint([[]], [{}], {1: {}})\nprint('tab\\tnewline-escaped')\nprint(repr('a\\nb'))\n",
    out := ["", "a b c", "1 True", "[1, 'two', True, None]", "{'a': [1, (2,)]}", "(1,) (1, 2)", "[[]] [{}] {1: {}}", "tab\tnewline-escaped", "'a\\nb'"] },
  { name := "scoping",
    src := "\nx = 'global'\ndef read():\n    return x\ndef shadow():\n    x = 'local'\n    return x\nprint(read(), shadow(), x)\ndef make_adder(n):\n    def add(v):\n        return v + n\n    return add\nadd2 = make_adder(2)\nadd10 = make_adder(10)\nprint(add2(1), add10(1))\ndef nested():\n    a = 1\n    def mid():\n        b = 2\n        def inner():\n            return a + b\n        return inner()\n    return mid()\nprint(nested())\n",
    out := ["global local global", "3 11", "3"] },
  { name := "mutation_in_place",
    src := "\nxs = [1, 2, 3]\nxs[0] = 10\nxs[-1] = 30\nprint(xs)\nxs[1] += 5\nprint(xs)\nd = {'n': 1}\nd['n'] += 1\nd['m'] = d.get('m', 0) + 5\nprint(d)\ngrid = [[0, 0], [0, 0]]\ngrid[0][1] = 1\nprint(grid)\ndel xs[0]\nprint(xs)\n",
    out := ["[10, 2, 30]", "[10, 7, 30]", "{'n': 2, 'm': 5}", "[[0, 1], [0, 0]]", "[7, 30]"] },
  { name := "algorithms",
    src := "\ndef bubble(xs):\n    ys = xs + []\n    n = len(ys)\n    for i in range(n):\n        for j in range(n - i - 1):\n            if ys[j] > ys[j + 1]:\n                tmp = ys[j]\n                ys[j] = ys[j + 1]\n                ys[j + 1] = tmp\n    return ys\nprint(bubble([5, 2, 9, 1, 5, 6]))\ndef is_prime(n):\n    if n < 2:\n        return False\n    d = 2\n    while d * d <= n:\n        if n % d == 0:\n            return False\n        d += 1\n    return True\nprint([n for n in range(30) if is_prime(n)])\ndef gcd(a, b):\n    while b != 0:\n        t = b\n        b = a % b\n        a = t\n    return a\nprint(gcd(48, 18), gcd(17, 5))\ndef word_count(text):\n    counts = {}\n    for w in text.split():\n        counts[w] = counts.get(w, 0) + 1\n    return counts\nwc = word_count('the cat the hat')\nfor k in sorted(wc.keys()):\n    print(k, wc[k])\ndef binary_search(xs, target):\n    lo = 0\n    hi = len(xs) - 1\n    while lo <= hi:\n        mid = (lo + hi) // 2\n        if xs[mid] == target:\n            return mid\n        if xs[mid] < target:\n            lo = mid + 1\n        else:\n            hi = mid - 1\n    return -1\nsorted_xs = [1, 3, 5, 7, 9]\nprint(binary_search(sorted_xs, 7), binary_search(sorted_xs, 4))\ndef fizzbuzz(n):\n    out = []\n    for i in range(1, n + 1):\n        if i % 15 == 0:\n            out.append('FizzBuzz')\n        elif i % 3 == 0:\n            out.append('Fizz')\n        elif i % 5 == 0:\n            out.append('Buzz')\n        else:\n            out.append(str(i))\n    return out\nprint(fizzbuzz(15))\n",
    out := ["[1, 2, 5, 5, 6, 9]", "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]", "6 1", "cat 1", "hat 1", "the 2", "3 -1", "['1', '2', 'Fizz', '4', 'Buzz', 'Fizz', '7', '8', 'Fizz', 'Buzz', '11', 'Fizz', '13', '14', 'FizzBuzz']"] },
  { name := "stack_machine",
    src := "\ndef evaluate(prog):\n    stack = []\n    for tok in prog.split():\n        if tok == '+':\n            b = stack.pop()\n            a = stack.pop()\n            stack.append(a + b)\n        elif tok == '*':\n            b = stack.pop()\n            a = stack.pop()\n            stack.append(a * b)\n        elif tok == '-':\n            b = stack.pop()\n            a = stack.pop()\n            stack.append(a - b)\n        else:\n            stack.append(int(tok))\n    return stack.pop()\nprint(evaluate('2 3 +'))\nprint(evaluate('2 3 + 4 *'))\nprint(evaluate('10 2 3 * -'))\n",
    out := ["5", "20", "4"] },
  { name := "more_strings",
    src := "\nprint('a,b,,c'.split(','))\nprint(''.join([]), '|'.join(['x']))\nprint('Hello'[0:0], len('Hello'[2:2]))\nprint('x' * 0, 'x' * -1, '' == \"\")\nprint('%s' == \"%s\")\nprint(str([]), str({}), str(()))\nprint('aXbXc'.replace('X', ''), 'aaa'.count('a'), 'aaa'.count('aa'))\nprint('  a b  '.split())\nprint('CamelCase'.lower().upper())\n",
    out := ["['a', 'b', '', 'c']", " x", " 0", "  True", "True", "[] {} ()", "abc 3 1", "['a', 'b']", "CAMELCASE"] },
  { name := "slices_and_negatives",
    src := "\nxs = [0, 1, 2, 3, 4]\nprint(xs[-2:], xs[:-2], xs[1:-1], xs[10:], xs[-10:])\nprint(xs[3:1], len(xs[3:1]))\ns = 'abcdef'\nprint(s[-3:], s[:-3], s[2:4], s[100:])\nt = (1, 2, 3)\nprint(t[-1], t[:2], t[1:])\n",
    out := ["[3, 4] [0, 1, 2] [1, 2, 3] [] [0, 1, 2, 3, 4]", "[] 0", "def abc cd ", "3 (1, 2) (2, 3)"] },
  { name := "nested_data",
    src := "\ngrid = [[1, 2], [3, 4]]\nprint(grid[1][0], len(grid), len(grid[0]))\nfor row in grid:\n    for cell in row:\n        print(cell)\nd = {'a': {'b': [1, 2]}}\nprint(d['a']['b'][1])\nd['a']['b'].append(3)\nprint(d)\nmatrix = [[0] * 2, [0] * 2]\nmatrix[0][0] = 9\nprint(matrix)\npairs = {(1, 2): 'x'}\nprint(pairs[(1, 2)])\n",
    out := ["3 2 2", "1", "2", "3", "4", "2", "{'a': {'b': [1, 2, 3]}}", "[[9, 0], [0, 0]]", "x"] },
  { name := "identity_and_membership",
    src := "\na = [1]\nb = [1]\nprint(a == b, a is b, a is not b)\nprint(None is None, None == None)\nprint(1 in [1, 2], 3 not in [1, 2], 'a' in {'a': 1}, 'b' not in {'a': 1})\nprint((1, 2) in [(1, 2)], [1] in [[1]])\nprint('lo' in 'hello', 'z' not in 'hello')\n",
    out := ["True False True", "True True", "True True True True", "True True", "True True"] },
  { name := "keyword_and_default_args",
    src := "\ndef f(a, b=2, c=3):\n    return (a, b, c)\nprint(f(1), f(1, 9), f(1, 9, 8), f(1, c=7), f(a=1, c=7), f(c=7, a=1))\ndef g(xs=None):\n    if xs is None:\n        return 'none'\n    return len(xs)\nprint(g(), g([1, 2]))\ndef h(n):\n    return n * 2\nprint(h(n=21))\n",
    out := ["(1, 2, 3) (1, 9, 3) (1, 9, 8) (1, 2, 7) (1, 2, 7) (1, 2, 7)", "none 2", "42"] },
  { name := "mutation_via_calls",
    src := "\ndef add_item(lst, v):\n    lst.append(v)\n    return lst\nxs = []\nadd_item(xs, 1)\nadd_item(xs, 2)\nprint(xs)\ndef swap_in_dict(d, k1, k2):\n    tmp = d[k1]\n    d[k1] = d[k2]\n    d[k2] = tmp\nd = {'a': 1, 'b': 2}\nswap_in_dict(d, 'a', 'b')\nprint(d)\ndef build(n):\n    out = []\n    for i in range(n):\n        out.append([i] * i)\n    return out\nprint(build(4))\n",
    out := ["[1, 2]", "{'a': 2, 'b': 1}", "[[], [1], [2, 2], [3, 3, 3]]"] },
  { name := "del_and_pop",
    src := "\nxs = [1, 2, 3, 4]\ndel xs[1]\nprint(xs)\nd = {'a': 1, 'b': 2, 'c': 3}\ndel d['b']\nprint(d)\nprint(d.pop('a'), d)\nprint(xs.pop(0), xs.pop(), xs)\nys = [1, 2, 3]\nys.clear()\nprint(ys, len(ys))\n",
    out := ["[1, 3, 4]", "{'a': 1, 'c': 3}", "1 {'c': 3}", "1 4 [3]", "[] 0"] },
  { name := "returns_and_recursion",
    src := "\ndef collatz_len(n):\n    steps = 0\n    while n != 1:\n        if n % 2 == 0:\n            n = n // 2\n        else:\n            n = 3 * n + 1\n        steps += 1\n    return steps\nprint([collatz_len(n) for n in range(1, 10)])\ndef power(base, exp):\n    if exp == 0:\n        return 1\n    half = power(base, exp // 2)\n    if exp % 2 == 0:\n        return half * half\n    return base * half * half\nprint(power(2, 20), power(3, 5))\ndef ackermann_ish(m, n):\n    if m == 0:\n        return n + 1\n    if n == 0:\n        return ackermann_ish(m - 1, 1)\n    return ackermann_ish(m - 1, ackermann_ish(m, n - 1))\nprint(ackermann_ish(2, 3))\ndef early(xs):\n    for x in xs:\n        if x < 0:\n            return 'negative'\n    return 'all ok'\nprint(early([1, 2]), early([1, -2]))\n",
    out := ["[0, 1, 7, 2, 5, 8, 16, 3, 19]", "1048576 243", "9", "all ok negative"] },
  { name := "exception_control",
    src := "\ndef parse_int(s):\n    try:\n        return int(s)\n    except ValueError:\n        return None\nprint(parse_int('12'), parse_int('nope'))\nlog = []\ndef risky(n):\n    try:\n        if n == 0:\n            raise ZeroDivisionError('zero')\n        log.append('ok ' + str(n))\n        return 10 // n\n    except ZeroDivisionError as e:\n        log.append('err ' + str(e))\n        return -1\n    finally:\n        log.append('done ' + str(n))\nprint(risky(2), risky(0))\nprint(log)\ndef reraise():\n    try:\n        raise ValueError('inner')\n    except ValueError as e:\n        raise RuntimeError('wrapped: ' + str(e))\ntry:\n    reraise()\nexcept RuntimeError as e:\n    print('got', e)\nfor v in ['1', 'x', '3']:\n    try:\n        print(int(v) * 2)\n    except ValueError:\n        print('bad', v)\n",
    out := ["12 None", "5 -1", "['ok 2', 'done 2', 'err zero', 'done 0']", "got wrapped: inner", "2", "bad x", "6"] },
  { name := "uncaught_value_error",
    src := "print('before')\nraise ValueError('boom')\n",
    out := ["before"],
    raises := some "ValueError: boom" },
  { name := "uncaught_name_error",
    src := "print(missing)\n",
    out := [],
    raises := some "NameError: name 'missing' is not defined" },
  { name := "uncaught_zero_div",
    src := "print(1)\nprint(1 // 0)\n",
    out := ["1"],
    raises := some "ZeroDivisionError: integer division or modulo by zero" },
  { name := "uncaught_key_error",
    src := "d = {}\nprint(d['k'])\n",
    out := [],
    raises := some "KeyError: 'k'" },
  { name := "uncaught_assert",
    src := "assert 1 == 2, 'bad'\n",
    out := [],
    raises := some "AssertionError: bad" },
  { name := "uncaught_type_error",
    src := "print(len(1))\n",
    out := [],
    raises := some "TypeError: object of type 'int' has no len()" }
]

-- END GENERATED TESTS

/-- Run every test, printing one line per failure. -/
def runTests : IO UInt32 := do
  let mut failures := 0
  for t in tests do
    match t.check with
    | Option.none => IO.println s!"ok    {t.name}"
    | some why => do
      failures := failures + 1
      IO.println s!"FAIL  {t.name}: {why}"
  IO.println s!"\n{tests.length - failures}/{tests.length} passed"
  pure (if failures == 0 then 0 else 1)

end SnakeFight
