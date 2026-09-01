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
| `SnakeFight/Lexer.lean` | 246 | tokenizer, including INDENT/DEDENT synthesis |
| `SnakeFight/Parser.lean` | 797 | recursive descent with precedence climbing |
| `SnakeFight/Value.lean` | 429 | values, the object heap, machine state, the interpreter monad |
| `SnakeFight/Kernel.lean` | 427 | the *pure* semantic kernel: truthiness, equality, ordering, arithmetic, indexing, `repr` |
| `SnakeFight/Builtins.lean` | 504 | builtin functions and the methods on `str`, `list`, `dict` |
| `SnakeFight/Interp.lean` | 728 | the interpreter proper |
| `SnakeFight/Pure.lean` | 541 | a specification-level evaluator, and the theorem that the interpreter agrees with it |
| `SnakeFight/Hoare.lean` | 1096 | a Hoare logic, including a procedure-call rule, proved sound against the interpreter |
| `SnakeFight/Reason.lean` | 182 | reasoning helpers for the integer fragment |
| `SnakeFight/Examples.lean` | 1104 | worked examples: concrete runs and three verified programs |
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

The procedure rule below is the one part of the reasoning layer that this would
disturb. It works with frames as they are — snapshot values without identity —
and says what a call may not touch with an assertion, `InFrame`, about the
globals, the heap and the output. Give frames heap identity and `InFrame` is what
changes: it would have to talk about frame addresses, and possibly about aliasing
between them.

## Reasoning about Python programs

There are four layers, and they are trusted differently. Being able to say
precisely *what* is checked by *what* is most of the point of the exercise.

### 1. A run is a value

`print` appends to the state instead of doing `IO`, and the interpreter is a
total function of its fuel budget, so "this program prints this" is an equation
between Lean values:

```lean
def divProg : Program :=
  [ .expr (.call (.name "print")
      [ .binop .floordiv (.unop .neg (.int 7)) (.int 2),
        .binop .mod (.unop .neg (.int 7)) (.int 2),
        .binop .pow (.int 2) (.int 70) ] []) ]

theorem divSrc_parses : parse divSrc = .ok divProg := by
  unfold parse; rw [divSrc_lexes]; rfl

theorem divProg_prints :
    outputOfProg divProg = some ["-4 1 1180591620717411303424"] := by decide

theorem divSrc_prints :
    outputOf divSrc = some ["-4 1 1180591620717411303424"] :=
  (outputOf_of_parse divSrc_parses).trans divProg_prints
```

The kernel proves all of that, with no axioms beyond Lean's own three.
`native_decide` is not used anywhere in this project, so `Lean.ofReduceBool` —
and with it the Lean compiler and runtime — is not part of what you have to
believe. The last theorem is about a `String` of Python, so a concrete run is
checked end to end: lexer, parser and interpreter, all inside the kernel.

The two middle theorems are about the *AST*: one says what the program prints,
the other that the parser turns the displayed Python into that AST. Both are
proved by the kernel, so nothing about a concrete run is delegated to the
compiled parser, and `outputOf_of_parse` combines them into the source-level
statement. That combination reduces nothing — asking the kernel to reduce
`outputOf divSrc` in one step would fuse the parser with the interpreter and
never finish.

Writing the AST out by hand is what gives that second theorem something to
check against. A generated AST could not catch a parser bug — the theorem would
silently become a true statement about whatever program the parser had in mind.
Nor does the output alone catch it: mis-recording `a is b` as `a == b` leaves
the printed output unchanged, so the run theorem still goes through and only the
parse theorem fails.

The parse theorem takes two steps rather than one, because `parse src` cannot be
reduced in a single `rfl`. `PState` is a token array plus a `Nat` cursor, so
every step of the parser reads `st.toks[st.pos]?`; reduction zeta-expands the
`let` that binds the array, so inside `parse src` that array is the *unreduced*
`tokenize src` term and each of those reads re-derives the token list from the
source. Reducing it in one go reruns the lexer once per cursor read and never
finishes, even though the lexer and the parser each reduce in well under a
second. Naming the token list — `SnakeFight.ExampleToks`, generated by
`tests/gen_toks.lean` — breaks the fusion:

```lean
theorem divSrc_lexes : tokenize divSrc = .ok divToks := by rfl
```

Two things had to be fixed to get there, and neither was in the parser, which
reduces fine. The lexer read integer literals with `String.toNat!`, which the
kernel cannot reduce at all (`example : "12".toNat! = 12 := by rfl` fails in
plain Lean); it now folds over the digit list structurally. And the parse
theorems are stated as propositional equations rather than with `==`, because
`Expr` and `Stmt` are nested inductives whose derived `BEq` instances are
compiled as `partial` — opaque constants with no value, which the kernel cannot
reduce at any fuel, for any input. Being opaque rather than axioms, they never
showed up in the axiom audit.

Three plausible culprits were ruled out along the way and stay ruled out: the
fuel budget (`pAtom` reduces as fast at fuel 544 as at fuel 4), the size of the
mutual block (the parser's and the interpreter's are both 21 functions), and the
token list (the lexer reduces, token payloads included, in well under a second).
The interpreter reduces at a fuel budget of 2,000,000; what set the parser apart
was re-deriving a shared subterm, not the size of anything.

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
`while`, `assert`, `return`, `def`, procedure calls, sequencing, consequence —
with assertions as plain Lean predicates on states, and proves it sound against
`execBlock` itself:

```lean
theorem H.sound (d : H P b Q Rt) : ∀ f s, P s → Ok Q Rt (execBlock f b s)
```

`Ok Q Rt` says a verified block may finish normally (establishing `Q`), finish by
returning a value `v` (establishing `Rt v`), raise, or run out of fuel — and may
*not* `break` or `continue` out of itself. That last clause is what makes the
usual `while` rule sound: a `break` would otherwise let control leave the loop in
a state where the negated guard does not hold. Since no rule derives `break`, it
holds automatically.

Three features of the logic are worth calling out because they are consequences
of verifying *Python* rather than a toy imperative language:

* **Type obligations are explicit.** `i < n` may raise `TypeError` instead of
  producing a bool, so every rule whose conclusion mentions the value of an
  expression carries a `Defined` side condition: the precondition must imply that
  `evalP` commits to a value. In practice invariants have to say "`i` and `n` are
  ints" — exactly the information a Python reader supplies mentally.
* **The heap is in the state.** Assertions can talk about `xs[i]` because
  indexing is a pure read, so it is part of the kernel.
* **Names resolve late.** A contract for a function that calls other functions
  has to say what it assumes about the globals it will be called under — right
  down to "and `abs` is still the builtin". `CallSpec` carries that assumption
  explicitly rather than pretending Python has static linking.

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
theorem mulNonnegProg_spec (m n : Int) :
    H (fun s => Args m n s ∧ 0 ≤ n) mulNonnegProg
      (fun s => s.lookupName "r" = some (.int (m * n))) Rt

theorem mulNonnegProg_correct (m n : Int) (fuel : Nat) (s s' : State)
    (hpre : Args m n s ∧ 0 ≤ n)
    (hrun : execBlock fuel mulNonnegProg s = .ok .normal s') :
    s'.lookupName "r" = some (.int (m * n))
```

Both are checked by the kernel with no extra axioms (`propext`,
`Classical.choice`, `Quot.sound` only). The invariant is `0 ≤ i ≤ n ∧ r = m * i`,
and the exit condition plus the invariant give `i = n`, hence `r = m * n`.

That claim is itself checked: the end of `SnakeFight/Examples.lean` pins the
axiom list of every theorem in the file, runs and specifications alike, with
`#guard_msgs in #print axioms`, so the build breaks if anything ever sneaks a
compiler-trusting step into a proof.

These theorems are stated about the AST for the same reason the concrete runs
are, and with the same parse theorem linking the displayed source to it.

### 4. A procedure-call rule

The `0 ≤ n` above is the loop's limitation rather than multiplication's. Lifting
it the way a Python programmer would means writing three functions and composing
them:

```python
def sign(n):
    if n < 0:
        return -1
    elif n > 0:
        return 1
    else:
        return 0

def mulNonneg(m, n):
    r = 0
    i = 0
    while i < n:
        r = r + m
        i = i + 1
    return r

def mul(m, n):
    return mulNonneg(m * sign(n), abs(n))

r = mul(m, n)
```

```lean
theorem mulProg_spec (m n : Int) :
    H (ModuleArgs m n) mulProg
      (fun s => s.lookupName "r" = some (.int (m * n))) Rt
```

for *every* `m` and *every* `n`, negative and zero included — the identity being
`m * n = (m * Int.sign n) * |n|`, which is where `Int.sign 0 = 0` earns its keep.
Four pieces make that provable.

**A judgement for expressions that call.** `evalP` declines every call, on
purpose: it is the effect-free fragment, and that is what makes the `Defined`
obligations mean something. So the rules that merely *consume* the value of an
expression take a semantic premise instead:

```lean
def EvalTo (P : Assn) (e : Expr) (R : State → Value → Prop) : Prop :=
  ∀ f s s' v, P s → evalExpr f e s = .ok v s' → R s v ∧ s' = s
```

"However this expression evaluates, it leaves the state alone and its value
satisfies `R`." `EvalTo.of_evalP` covers the pure fragment, `EvalTo.callName`
covers a call, and `EvalTo.binop` glues them together — which is what lets
`sign(n)` sit inside the argument `m * sign(n)` rather than having to be assigned
to a temporary first.

**A contract, and a specification environment.** A `Contract` is a precondition
on a call's arguments and a postcondition relating them to its result, and
`CallSpec G fv c` says `fv` meets `c`: called from a state whose globals satisfy
`G`, with arguments satisfying `c.pre`, it either fails to return or returns a
value satisfying `c.post` and leaves the state exactly as it was. `Holds Γ G`
says every name in a list of name/contract pairs resolves, under `G`, to a value
meeting its contract. `mul` is verified against
`mulEnv = [sign, mulNonneg, abs]`; the three `def`s at the top of the program are
what discharge it, through a `funcDef` rule whose postcondition mentions the very
function value the interpreter builds.

**`return`, as a second postcondition.** `H` gained an index: `Rt v s` is what
must hold when a block finishes by returning `v`. Every return-free rule is
polymorphic in it, so the existing proofs carried over unchanged apart from the
extra index, and `while` propagates it — a `return` inside a loop body leaves the
loop and the enclosing block together.

**A rule of constancy.** Every rule of the logic changes the state in exactly one
way: by assigning to a simple variable. So

```lean
theorem H.frame (d : H P b Q Rt) (hA : ∀ s x v, A s → A (s.setVar x v)) :
    H (fun s => P s ∧ A s) b (fun s => Q s ∧ A s) (fun v s => Rt v s ∧ A s)
```

carries any assignment-stable assertion across a block that was verified without
knowing about it. The assertion the call rule needs is `InFrame s₀` — "still
inside the callee's frame, and the caller's globals, heap and output are
untouched" — which is what a `CallSpec` has to establish and what a body verified
on its own says nothing about. `H.append` sequences blocks; `H.frame` frames
around them.

The point of all four is that nothing about the loop is rewritten.
`mulNonneg`'s body *is* `mulNonnegProg` followed by `return r`, and its
`CallSpec` invokes `mulNonnegProg_spec` as it stands, framed by `H.frame` and
sequenced by `H.append`. The one visible concession is that `Args` asks for a
"plain scope" — module level, or a frame with no `global` declaration in force —
rather than for no frame at all, which is what lets one verified block serve both
as a program and as a function body.

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
  `return`, module-level `def`, calls to named functions and to `abs`, sequencing
  and consequence. `for`, `try`, method calls, keyword and default arguments, and
  assignment to subscripts are executed but not yet reasoned about. Adding
  `break`/`continue` means giving blocks a third postcondition for abrupt exits.
* The procedure rule handles a `def` with plain positional parameters and no
  defaults, and a call written `f(e₁, …, eₙ)`. A `CallSpec` says the call leaves
  the caller's state exactly as it was, so it covers functions that compute and
  return; a callee that prints, allocates, or writes a `global` needs a weaker
  notion in place of `InFrame`, and the call rule would then have to thread a
  changed state through the argument list. Recursion is not covered either: a
  recursive function's `CallSpec` would have to assume itself, which needs the
  rule stated over an environment the derivation may draw on — the same shape,
  but with a fixpoint in it.
* No termination reasoning: the logic proves partial correctness only. Given the
  fuel-indexed semantics, a total-correctness variant would need a measure that
  bounds the fuel.
* Reducing a call makes the resulting state an unreduced term, and every read of
  it inside the next call re-derives it, so nested concrete calls cost
  multiplicatively — four `mul(a, b)` in one program reduce in seconds, six in
  tens. The composed program's concrete runs are split in two for that reason.
  It is the same shared-subterm effect that stops `parse src` from reducing in
  one step, here in the interpreter rather than the parser.
* The parse theorems cover the worked examples only, and rely on token lists
  generated into `SnakeFight/ExampleToks.lean` by `tests/gen_toks.lean`; the
  CPython differential suite in `Tests.lean` runs the compiled pipeline, by
  design. The lexer also has to stay on `List Char`: core `String` functions
  that iterate by `String.Pos` are not kernel-reducible.
* `range` is eager, floats are absent, and closures inside functions capture by
  value (see "Known divergence" above). All three are visible in the code as
  explicit approximations rather than accidents.
