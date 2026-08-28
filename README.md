# snake-fight

A Python interpreter written in Lean 4 — plus a program logic, proved sound
against that interpreter, for reasoning about the Python programs it runs.

It is a proof of concept: it implements a substantial subset of Python (see
below), not the whole language. The interesting part is that the interpreter is
an ordinary *total* Lean function, so a program's behaviour is a mathematical
object you can compute with and prove theorems about.

```console
$ cat quicksort.py
def quicksort(xs):
    if len(xs) <= 1:
        return xs
    pivot = xs[0]
    rest = xs[1:]
    return quicksort([x for x in rest if x < pivot]) + [pivot] \
         + quicksort([x for x in rest if x >= pivot])

print(quicksort([5, 3, 8, 1, 9, 2, 7]))

$ snake-fight quicksort.py
[1, 2, 3, 5, 7, 8, 9]
```

## Quick start

```console
$ lake build                       # build the library and the CLI
$ ./.lake/build/bin/snake-fight test    # run the test suite (32 programs)
$ ./.lake/build/bin/snake-fight prog.py
$ ./.lake/build/bin/snake-fight -c 'print(sum(range(10)))'
$ ./.lake/build/bin/snake-fight --ast prog.py       # dump the parsed AST
$ ./.lake/build/bin/snake-fight --fuel 50000 prog.py
```

No dependencies beyond Lean 4 itself (v4.33.1); in particular, not Mathlib, so
builds take seconds.

## What's in the box

| module | lines | what it does |
| --- | --- | --- |
| `SnakeFight/Ast.lean` | 137 | expressions, targets, statements |
| `SnakeFight/Lexer.lean` | 241 | tokenizer, including INDENT/DEDENT synthesis |
| `SnakeFight/Parser.lean` | 780 | recursive descent with precedence climbing |
| `SnakeFight/Value.lean` | 343 | values, the object heap, machine state, the interpreter monad |
| `SnakeFight/Kernel.lean` | 432 | the *pure* semantic kernel: truthiness, equality, ordering, arithmetic, indexing, `repr` |
| `SnakeFight/Builtins.lean` | 504 | builtin functions and the methods on `str`, `list`, `dict` |
| `SnakeFight/Interp.lean` | 699 | the interpreter proper |
| `SnakeFight/Pure.lean` | 541 | a specification-level evaluator, and the theorem that the interpreter agrees with it |
| `SnakeFight/Hoare.lean` | 436 | a Hoare logic, proved sound against the interpreter |
| `SnakeFight/Reason.lean` | 124 | reasoning helpers for the integer fragment |
| `SnakeFight/Examples.lean` | 275 | worked examples: concrete runs and two verified programs |
| `SnakeFight/Tests.lean` | 168 | the test suite (expectations generated from CPython) |

## The Python subset

**Supported.** Arbitrary-precision `int`, `str`, `bool`, `None`, `tuple`,
`list`, `dict`, functions and `lambda`.

* operators: `+ - * // % ** << >> & | ^ ~`, comparisons including *chained*
  comparisons (`0 <= i < n`), `and`/`or`/`not` with Python's short-circuit
  value-returning semantics, `in`/`not in`, `is`/`is not`, `x if c else y`
* statements: assignment (including `a = b = e` and tuple unpacking), augmented
  assignment, `if`/`elif`/`else`, `while`, `for`, `break`, `continue`, `pass`,
  `def` (defaults, keyword arguments, nested functions, closures), `return`,
  `global`, `raise`, `try`/`except`/`else`/`finally`, `assert`, `del d[k]`
* indexing and slicing (`a[i]`, `a[i:j]`, negative indices), list
  comprehensions with an optional `if`
* mutable objects live in a heap, so aliasing behaves like Python's:
  `a = [1,2]; b = a; b.append(3)` leaves `a == [1, 2, 3]`
* exceptions are real values with a class hierarchy, so `except LookupError`
  catches a `KeyError`
* builtins: `print len range str repr int bool abs min max sum sorted list
  tuple dict reversed enumerate zip isinstance type ord chr divmod any all id`
* methods: `str.{upper,lower,strip,split,join,startswith,endswith,replace,find,
  count,isdigit,isalpha}`, `list.{append,extend,insert,pop,remove,index,count,
  clear,reverse,sort,copy}`, `dict.{keys,values,items,get,pop,setdefault,update,
  clear,copy}`

**Not supported**, and diagnosed with an explicit error rather than
misinterpreted: `class`, `import`, `with`, `yield`/generators, `async`,
`nonlocal`, f-strings and other string prefixes, floats (so `/` raises — use
`//`), sets, `a[i:j:k]` step slices, `*args`/`**kwargs`, decorators, `match`,
walrus, `%`-formatting and `str.format`.

Also unsupported: `for`/`while` … `else` clauses.

### Known divergence

Inside a function, a nested `def` captures the enclosing locals **by value at
`def` time**, where CPython captures the variable itself:

```python
def counter():
    n = 0
    def get():
        return n
    n = 5
    return get()
print(counter())      # CPython: 5      snake-fight: 0
```

At module level there is no divergence (closures see globals late, as in
CPython). Fixing it properly means giving frames identity — putting them in the
heap and having closures capture a frame address — which is a worthwhile next
step rather than a hard problem. The other deliberate approximation is that
`range` is materialized as a list rather than being lazy. Both are noted at
their definitions in the source.

## Reasoning about Python programs

There are three layers, and they are trusted differently. Being able to say
precisely *what* is checked by *what* is most of the point of the exercise.

### 1. A run is a value

`print` appends to the state instead of doing `IO`, and the interpreter is a
total function of its fuel budget, so "this program prints this" is an equation
between Lean values:

```lean
example : outputOf "print(-7 // 2, -7 % 2, 2 ** 70)"
    = some ["-4 1 1180591620717411303424"] := by native_decide
```

`native_decide` compiles and runs it, which adds `Lean.ofReduceBool` to the
theorem's axioms. Lean's kernel can evaluate these too, but it is far too slow
on the front end to be practical, so end-to-end examples use `native_decide`.

### 2. A specification-level evaluator, tied to the interpreter by a theorem

To state a loop invariant you need to talk about the value of an expression in a
state — without fuel, without a state transformer, and without allocation.
`SnakeFight.Pure.evalP : State → Expr → Option Value` is that: it models the
effect-free fragment of Python and answers `none` for anything else (a call, a
list display, a slice) or for anything that would raise.

```lean
theorem evalP_agrees (hp : evalP s e = some v) (hr : evalExpr f e s = .ok v' s') :
    v' = v ∧ s' = s
```

If the specification commits to a value, the interpreter must agree, and must
not touch the state. Note the direction: `evalP` is allowed to give up, but it
is never allowed to be wrong. The two share the same kernel operations
(`binOpK`, `cmpK`, `indexK`, …), so the proof is a structural induction on fuel
with no semantic gap to bridge.

### 3. A Hoare logic

`SnakeFight.Hoare` gives the imperative core a program logic — assignment, `if`,
`while`, `assert`, sequencing, consequence — with assertions as plain Lean
predicates on states, and proves it sound against `execBlock` itself:

```lean
theorem H.sound (d : H P b Q) : ∀ f s, P s → Ok Q (execBlock f b s)
```

`Ok Q` says a verified block may finish normally (establishing `Q`), return,
raise, or run out of fuel — and may *not* `break` or `continue` out of itself.
That last clause is what makes the usual `while` rule sound: a `break` would
otherwise let control leave the loop in a state where the negated guard does not
hold. Since no rule derives `break`, it holds automatically.

Two features of the logic are worth calling out because they are consequences of
verifying *Python* rather than a toy imperative language:

* **Type obligations are explicit.** `i < n` may raise `TypeError` instead of
  producing a bool, so every rule that inspects an expression carries a
  `Defined` side condition: the precondition must imply that `evalP` commits to
  a value. In practice invariants have to say "`i` and `n` are ints" — exactly
  the information a Python reader supplies mentally.
* **The heap is in the state.** Assertions can talk about `xs[i]` because
  indexing is a pure read, so it is part of the kernel.

Here is the payoff, from `SnakeFight/Examples.lean` — multiplication by repeated
addition, verified for all `m` and all `n ≥ 0`:

```python
r = 0
i = 0
while i < n:
    r = r + m
    i = i + 1
```

```lean
theorem mulProg_spec (m n : Int) : H (MulPre m n) mulProg (MulPost m n)

theorem mulProg_correct (m n : Int) (fuel : Nat) (s s' : State)
    (hpre : MulPre m n s) (hrun : execBlock fuel mulProg s = .ok .normal s') :
    s'.lookupName "r" = some (.int (m * n))
```

Both are checked by the kernel with no extra axioms (`propext`,
`Classical.choice`, `Quot.sound` only). The invariant is `0 ≤ i ≤ n ∧ r = m * i`,
and the exit condition plus the invariant give `i = n`, hence `r = m * n`.

The theorems are stated about the AST. A `#guard` next to each example checks at
build time that the parser really does turn the displayed Python source into
that AST; that link is checked by evaluation, not by the kernel, because the
AST types do not have derivable `DecidableEq` instances.

## Is it actually Python?

The test suite is differential. `tests/gen_tests.py` holds 32 programs, runs
each one under the `python3` on your machine, and generates `SnakeFight/Tests.lean`
with CPython's actual output as the expectation:

```console
$ python3 tests/gen_tests.py    # regenerate expectations from CPython
$ ./.lake/build/bin/snake-fight test
...
32/32 passed
```

CI regenerates the expectations and fails if they have drifted, then runs the
suite. The programs cover arithmetic and integer edge cases (`-7 // 2 == -4`),
aliasing, dict insertion order, closures, keyword arguments, the exception
hierarchy, `finally` on `return`, slicing, and a handful of small algorithms
(quicksort, sieve-ish prime test, binary search, FizzBuzz, an RPN evaluator).
Writing them found real bugs — reversed dict display order, and an inverted
check on where default arguments may appear.

## Design notes

**Fuel.** Every interpreter function takes a step budget and matches on
`fuel + 1`, so recursion is structurally obvious and the interpreter is total —
no `partial`, so it can be unfolded inside a proof. Running out of fuel is its
own outcome, distinct from raising, and is not catchable from inside the
language. Fuel counts steps (AST nodes visited, loop iterations, calls), so
budgets are generous by default (2,000,000).

**Loops are written in explicit state-passing style** rather than with `do`.
That makes the recursive call a real tail call — `while True: i += 1` runs 2M
iterations in 0.3s and reports running out of fuel rather than overflowing the
stack — and it means unfolding one iteration in a proof needs no reasoning about
`bind`.

**One kernel, two consumers.** The pure fragment of Python's semantics lives in
`Kernel.lean` and returns `Option KRes`: "produces this value", "raises this",
or "not my department". The interpreter calls it first and only falls back to
effectful code when it declines; the specification-level evaluator calls the
same functions. Neither can drift from the other.

## Limitations and obvious next steps

* No classes. This is the biggest gap in the language subset.
* The Hoare logic covers assignment to simple names, `if`, `while`, `assert`,
  sequencing and consequence. `for`, function calls, `try`, and assignment to
  subscripts are executed but not yet reasoned about. Adding `break`/`continue`
  means giving blocks a second postcondition for abrupt exits; adding calls
  means a procedure-call rule over a specification environment.
* No termination reasoning: the logic proves partial correctness only. Given the
  fuel-indexed semantics, a total-correctness variant would need a measure that
  bounds the fuel.
* The parser is a total function but its output is checked against source only
  by evaluation (see above). Hand-written `DecidableEq` instances for the AST
  would upgrade those `#guard`s to theorems.
* `range` is eager, floats are absent, and closures inside functions capture by
  value (see "Known divergence" above). All three are visible in the code as
  explicit approximations rather than accidents.
