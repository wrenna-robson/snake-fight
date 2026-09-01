import SnakeFight.Reason
import SnakeFight.Interp
import SnakeFight.ExampleToks

/-!
# Worked examples

Two kinds of statement about Python programs, both machine-checked.

## 1. Concrete runs

`outputOfProg p` is an ordinary Lean function, so "this program prints this" is
an equation between values, and the kernel proves it.  Each run below is a
theorem, checked with no axioms beyond Lean's own three -- in particular
without `Lean.ofReduceBool`, so the Lean compiler is not part of what you have
to believe.

The theorems are stated about the AST, and each is paired with a theorem saying
that the parser turns the displayed Python into that AST.  So the source-to-AST
step is checked by the kernel as well, and no part of a concrete run is left to
the compiled parser.

Those two combine into a statement about the source text itself -- `addSrc_prints
: outputOf addSrc = some ["3"]`, a theorem about a `String` of Python -- via
`outputOf_of_parse`.  The combination reduces nothing: the run is proved about
the AST, where the interpreter reduces in milliseconds, and transported across.
Asking the kernel to reduce `outputOf addSrc` directly would fuse the parser
with the interpreter and never finish.

That pairing takes two steps rather than one.  `parse` fuses the lexer and the
parser, and reduction zeta-expands the `let` that binds the token array, so the
array inside `parse src` is the *unreduced* `tokenize src` term and the parser
re-derives it at every cursor read; reduced in one go it never finishes.
Naming the token list -- `SnakeFight.ExampleToks` -- breaks the fusion, and
then each half reduces in well under a second.

Writing the AST out by hand is what gives the parse theorem something to check
against.  If the parser ever disagreed, the build would fail -- which it could
not do if the AST were generated from the source by the same parser it is meant
to check.

These are propositional equations rather than `==`.  `Expr` and `Stmt` are
nested inductives, so their derived `BEq` instances are compiled as `partial`:
opaque constants with no value.  `==` on an AST therefore cannot be reduced by
the kernel at all, at any fuel and for any input.

## 2. Symbolic correctness

`mulNonnegProg_spec`, `absProg_spec` and `mulProg_spec` are proofs *for all
inputs*, using the Hoare logic of `SnakeFight.Hoare`, rather than statements
about one run.  They are stated about the AST and paired with a parse theorem for
the same reasons as above.  The last of the three is about a program built out of
three Python functions, and goes through the procedure rule.
-/

namespace SnakeFight

/-! ## Concrete runs -/

-- The parse theorems below reduce a whole token list at once, which nests
-- deeper than the elaborator's default recursion limit.
set_option maxRecDepth 4000

/-! ### Arithmetic -/

def addSrc : String := "print(1 + 2)\n"

def addProg : Program :=
  [ .expr (.call (.name "print") [.binop .add (.int 1) (.int 2)] []) ]

theorem addSrc_lexes : tokenize addSrc = .ok addToks := by rfl

theorem addSrc_parses : parse addSrc = .ok addProg := by
  unfold parse; rw [addSrc_lexes]; rfl

theorem addProg_prints : outputOfProg addProg = some ["3"] := rfl

/-- The same run, stated about the source text. -/
theorem addSrc_prints : outputOf addSrc = some ["3"] :=
  (outputOf_of_parse addSrc_parses).trans addProg_prints

/-! ### String concatenation -/

def concatSrc : String := "print('hello ' + 'world')\n"

def concatProg : Program :=
  [ .expr (.call (.name "print") [.binop .add (.str "hello ") (.str "world")] []) ]

theorem concatSrc_lexes : tokenize concatSrc = .ok concatToks := by rfl

theorem concatSrc_parses : parse concatSrc = .ok concatProg := by
  unfold parse; rw [concatSrc_lexes]; rfl

theorem concatProg_prints : outputOfProg concatProg = some ["hello world"] :=
  rfl

/-- The same run, stated about the source text. -/
theorem concatSrc_prints : outputOf concatSrc = some ["hello world"] :=
  (outputOf_of_parse concatSrc_parses).trans concatProg_prints

/-! ### Aliasing

Aliasing behaves like Python's, not like a value semantics: `b` and `a` are the
same list, so appending through `b` is visible through `a`, and `a is b`. -/

def aliasSrc : String :=
"a = [1, 2]
b = a
b.append(3)
print(a, a is b)
"

def aliasProg : Program :=
  [ .assign [.name "a"] (.listE [.int 1, .int 2]),
    .assign [.name "b"] (.name "a"),
    .expr (.call (.attr (.name "b") "append") [.int 3] []),
    .expr (.call (.name "print")
      [.name "a", .compare (.name "a") [(.is, .name "b")]] []) ]

theorem aliasSrc_lexes : tokenize aliasSrc = .ok aliasToks := by rfl

theorem aliasSrc_parses : parse aliasSrc = .ok aliasProg := by
  unfold parse; rw [aliasSrc_lexes]; rfl

theorem aliasProg_prints : outputOfProg aliasProg = some ["[1, 2, 3] True"] :=
  rfl

/-- The same run, stated about the source text. -/
theorem aliasSrc_prints : outputOf aliasSrc = some ["[1, 2, 3] True"] :=
  (outputOf_of_parse aliasSrc_parses).trans aliasProg_prints

/-! ### Closures and comprehensions

Recursion, closures and comprehensions all work together. -/

def adderSrc : String :=
"def make_adder(n):
    def add(v):
        return v + n
    return add
add3 = make_adder(3)
print([add3(i) for i in range(5)])
"

def adderProg : Program :=
  [ .funcDef "make_adder" [("n", Option.none)]
      [ .funcDef "add" [("v", Option.none)]
          [ .ret (some (.binop .add (.name "v") (.name "n"))) ],
        .ret (some (.name "add")) ],
    .assign [.name "add3"] (.call (.name "make_adder") [.int 3] []),
    .expr (.call (.name "print")
      [ .listComp (.call (.name "add3") [.name "i"] [])
          (.name "i") (.call (.name "range") [.int 5] []) Option.none ] []) ]

theorem adderSrc_lexes : tokenize adderSrc = .ok adderToks := by rfl

theorem adderSrc_parses : parse adderSrc = .ok adderProg := by
  unfold parse; rw [adderSrc_lexes]; rfl

theorem adderProg_prints : outputOfProg adderProg = some ["[3, 4, 5, 6, 7]"] :=
  rfl

/-- The same run, stated about the source text. -/
theorem adderSrc_prints : outputOf adderSrc = some ["[3, 4, 5, 6, 7]"] :=
  (outputOf_of_parse adderSrc_parses).trans adderProg_prints

/-! ### Exceptions

The class hierarchy and `finally` both behave: a `KeyError` is caught by an
`except LookupError`, and the `finally` block runs either way. -/

def excSrc : String :=
"try:
    raise KeyError('k')
except LookupError as e:
    print('caught', e)
finally:
    print('cleanup')
"

def excProg : Program :=
  [ .tryS
      [ .raiseS (some (.call (.name "KeyError") [.str "k"] [])) ]
      [ (some (.name "LookupError"), some "e",
          [ .expr (.call (.name "print") [.str "caught", .name "e"] []) ]) ]
      []
      [ .expr (.call (.name "print") [.str "cleanup"] []) ] ]

theorem excSrc_lexes : tokenize excSrc = .ok excToks := by rfl

theorem excSrc_parses : parse excSrc = .ok excProg := by
  unfold parse; rw [excSrc_lexes]; rfl

theorem excProg_prints : outputOfProg excProg = some ["caught 'k'", "cleanup"] :=
  rfl

/-- The same run, stated about the source text. -/
theorem excSrc_prints : outputOf excSrc = some ["caught 'k'", "cleanup"] :=
  (outputOf_of_parse excSrc_parses).trans excProg_prints

/-! ### Division, modulus and big integers

Integer division and modulus follow Python, not C, and `int` is unbounded. -/

def divSrc : String := "print(-7 // 2, -7 % 2, 2 ** 70)\n"

def divProg : Program :=
  [ .expr (.call (.name "print")
      [ .binop .floordiv (.unop .neg (.int 7)) (.int 2),
        .binop .mod (.unop .neg (.int 7)) (.int 2),
        .binop .pow (.int 2) (.int 70) ] []) ]

theorem divSrc_lexes : tokenize divSrc = .ok divToks := by rfl

theorem divSrc_parses : parse divSrc = .ok divProg := by
  unfold parse; rw [divSrc_lexes]; rfl

theorem divProg_prints :
    outputOfProg divProg = some ["-4 1 1180591620717411303424"] := rfl

/-- The same run, stated about the source text. -/
theorem divSrc_prints : outputOf divSrc = some ["-4 1 1180591620717411303424"] :=
  (outputOf_of_parse divSrc_parses).trans divProg_prints

/-! ## A verified loop

```python
r = 0
i = 0
while i < n:
    r = r + m
    i = i + 1
```

Multiplication by repeated addition.  We prove that on termination `r` holds
`m * n`, for every `m` and every `n ≥ 0`.
-/

/-- The Python source of the program verified below. -/
def mulNonnegSrc : String :=
"r = 0
i = 0
while i < n:
    r = r + m
    i = i + 1
"

/-- The loop guard `i < n`. -/
def mulNonnegGuard : Expr := .compare (.name "i") [(.lt, .name "n")]

/-- The loop body: `r = r + m` then `i = i + 1`. -/
def mulNonnegStep : Block :=
  [ .assign [.name "r"] (.binop .add (.name "r") (.name "m")),
    .assign [.name "i"] (.binop .add (.name "i") (.int 1)) ]

/-- The AST of `mulNonnegSrc`. -/
def mulNonnegProg : Program :=
  [ .assign [.name "r"] (.int 0),
    .assign [.name "i"] (.int 0),
    .whileS mulNonnegGuard mulNonnegStep ]

theorem mulNonnegSrc_lexes : tokenize mulNonnegSrc = .ok mulNonnegToks := by rfl

theorem mulNonnegSrc_parses : parse mulNonnegSrc = .ok mulNonnegProg := by
  unfold parse; rw [mulNonnegSrc_lexes]; rfl

/-- State in which `m` and `n` are bound to the given integers, and assignment
is a plain local update.

`plainScope` rather than `s.frame = none` is what lets this block be verified
once and then used *both* at module level and as the body of a Python function
(see `mulNonnegFn_spec`). -/
def Args (m n : Int) (s : State) : Prop :=
  s.plainScope ∧ s.lookupName "m" = some (.int m) ∧ s.lookupName "n" = some (.int n)

/-- After the first assignment, `r` is `0`. -/
private def MulMid (m n : Int) (s : State) : Prop :=
  Args m n s ∧ 0 ≤ n ∧ s.lookupName "r" = some (.int 0)

/-- The loop invariant: `r = m * i` and `i` has not passed `n`. -/
private def MulInv (m n : Int) (s : State) : Prop :=
  Args m n s ∧ ∃ i r : Int,
    s.lookupName "i" = some (.int i) ∧ s.lookupName "r" = some (.int r) ∧
    0 ≤ i ∧ i ≤ n ∧ r = m * i

/-- Halfway through the loop body: `r` has been updated but `i` has not. -/
private def MulStep (m n : Int) (s : State) : Prop :=
  Args m n s ∧ ∃ i r : Int,
    s.lookupName "i" = some (.int i) ∧ s.lookupName "r" = some (.int r) ∧
    0 ≤ i ∧ i < n ∧ r = m * (i + 1)

/-- Assigning to one variable leaves the others, and the scope, alone. -/
private theorem args_setVar {m n : Int} {s : State} (h : Args m n s) {x : String}
    (hm : x ≠ "m") (hn : x ≠ "n") (v : Value) : Args m n (s.setVar x v) := by
  obtain ⟨hf, hmv, hnv⟩ := h
  refine ⟨State.plainScope_setVar hf x v, ?_, ?_⟩
  · rwa [lookup_set_other hf hm]
  · rwa [lookup_set_other hf hn]

/-- **The loop computes the product.** -/
theorem mulNonnegProg_spec (m n : Int) {Rt : Value → Assn} :
    H (fun s => Args m n s ∧ 0 ≤ n) mulNonnegProg
      (fun s => s.lookupName "r" = some (.int (m * n))) Rt := by
  -- r = 0
  have step1 : H (fun s => Args m n s ∧ 0 ≤ n)
      [.assign [.name "r"] (.int 0)] (MulMid m n) Rt := by
    refine H.assignP "r" (.int 0) ?_
    intro s hP
    obtain ⟨hargs, hn⟩ := hP
    refine ⟨.int 0, by simp, ?_, hn, ?_⟩
    · exact args_setVar hargs (by decide) (by decide) _
    · exact lookup_set_self hargs.1 "r" (.int 0)
  -- i = 0
  have step2 : H (MulMid m n) [.assign [.name "i"] (.int 0)] (MulInv m n) Rt := by
    refine H.assignP "i" (.int 0) ?_
    intro s hP
    obtain ⟨hargs, hn, hr⟩ := hP
    refine ⟨.int 0, by simp, args_setVar hargs (by decide) (by decide) _, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
    · exact lookup_set_self hargs.1 "i" (.int 0)
    · rw [lookup_set_other hargs.1 (by decide), hr]
    · omega
    · exact hn
    · simp
  -- r = r + m
  have body1 : H (fun s => MulInv m n s ∧ Truthy mulNonnegGuard s)
      [.assign [.name "r"] (.binop .add (.name "r") (.name "m"))] (MulStep m n) Rt := by
    refine H.assignP "r" _ ?_
    intro s hP
    obtain ⟨⟨hargs, i, r, hi, hr, hi0, hin, hri⟩, htruthy⟩ := hP
    -- The guard is true, so `i < n`.
    have hlt : i < n := (Truthy_lt (by simpa using hi) (by simpa using hargs.2.2)).mp htruthy
    refine ⟨.int (r + m), evalP_add (by simpa using hr) (by simpa using hargs.2.1), ?_⟩
    refine ⟨args_setVar hargs (by decide) (by decide) _, i, r + m, ?_, ?_, hi0, hlt, ?_⟩
    · rw [lookup_set_other hargs.1 (by decide), hi]
    · exact lookup_set_self hargs.1 "r" _
    · rw [hri, Int.mul_add, Int.mul_one]
  -- i = i + 1
  have body2 : H (MulStep m n) [.assign [.name "i"] (.binop .add (.name "i") (.int 1))]
      (MulInv m n) Rt := by
    refine H.assignP "i" _ ?_
    intro s hP
    obtain ⟨hargs, i, r, hi, hr, hi0, hin, hri⟩ := hP
    refine ⟨.int (i + 1), evalP_add (by simpa using hi) (by simp), ?_⟩
    refine ⟨args_setVar hargs (by decide) (by decide) _, i + 1, r, ?_, ?_, by omega, by omega, hri⟩
    · exact lookup_set_self hargs.1 "i" _
    · rw [lookup_set_other hargs.1 (by decide), hr]
  -- the loop
  have loop : H (MulInv m n) [.whileS mulNonnegGuard mulNonnegStep]
      (fun s => MulInv m n s ∧ Falsy mulNonnegGuard s) Rt := by
    refine H.whileS (MulInv m n) mulNonnegGuard mulNonnegStep ?_ (H.cons body1 (H.cons body2 H.nil))
    intro s hI
    obtain ⟨hargs, i, r, hi, hr, _, _, _⟩ := hI
    exact ⟨.bool (decide (i < n)), evalP_lt (by simpa using hi) (by simpa using hargs.2.2)⟩
  -- and the loop exits with i = n
  have finish : ∀ s, (MulInv m n s ∧ Falsy mulNonnegGuard s) →
      s.lookupName "r" = some (.int (m * n)) := by
    intro s ⟨hI, hf⟩
    obtain ⟨hargs, i, r, hi, hr, hi0, hin, hri⟩ := hI
    have hnlt : ¬ i < n := (Falsy_lt (by simpa using hi) (by simpa using hargs.2.2)).mp hf
    have : i = n := by omega
    rw [this] at hri
    rw [hri] at hr
    exact hr
  exact H.cons step1 (H.cons step2 (H.cons (H.post loop finish) H.nil))

/-! ### A concrete run of the verified loop

The same `mulNonnegProg`, wrapped in bindings for `m` and `n` and a `print`, so
the run and the specification are demonstrably about one program rather than two
that happen to look alike. -/

def mul67Src : String :=
"m = 6
n = 7
r = 0
i = 0
while i < n:
    r = r + m
    i = i + 1
print(r)
"

def mul67Prog : Program :=
  [ .assign [.name "m"] (.int 6),
    .assign [.name "n"] (.int 7) ] ++ mulNonnegProg ++
  [ .expr (.call (.name "print") [.name "r"] []) ]

theorem mul67Src_lexes : tokenize mul67Src = .ok mul67Toks := by rfl

theorem mul67Src_parses : parse mul67Src = .ok mul67Prog := by
  unfold parse; rw [mul67Src_lexes]; rfl

theorem mul67Prog_prints : outputOfProg mul67Prog = some ["42"] := rfl

/-- The same run, stated about the source text. -/
theorem mul67Src_prints : outputOf mul67Src = some ["42"] :=
  (outputOf_of_parse mul67Src_parses).trans mul67Prog_prints

/-! ## A verified conditional

```python
if x < 0:
    y = 0 - x
else:
    y = x
```
-/

/-- The Python source of the program verified below. -/
def absSrc : String :=
"if x < 0:
    y = 0 - x
else:
    y = x
"

/-- The AST of `absSrc`. -/
def absProg : Program :=
  [ .ifS (.compare (.name "x") [(.lt, .int 0)])
      [ .assign [.name "y"] (.binop .sub (.int 0) (.name "x")) ]
      [ .assign [.name "y"] (.name "x") ] ]

theorem absSrc_lexes : tokenize absSrc = .ok absToks := by rfl

theorem absSrc_parses : parse absSrc = .ok absProg := by
  unfold parse; rw [absSrc_lexes]; rfl

/-- **The conditional computes an absolute value** -- `Int.natAbs`, stated as an
integer. -/
theorem absProg_spec (a : Int) {Rt : Value → Assn} :
    H (fun s => s.plainScope ∧ s.lookupName "x" = some (.int a))
      absProg
      (fun s => s.lookupName "y" = some (.int (a.natAbs : Int))) Rt := by
  refine H.cons (H.ifS _ _ _ ?_ ?_ ?_) H.nil
  · -- the guard is well defined: `x` is an int
    intro s ⟨_, hx⟩
    exact ⟨.bool (decide (a < 0)), evalP_lt (by simpa using hx) (by simp)⟩
  · -- then branch: x < 0, so y = -x
    refine H.cons (H.assignP "y" _ ?_) H.nil
    intro s ⟨⟨hf, hx⟩, ht⟩
    have hlt : a < 0 := (Truthy_lt (by simpa using hx) (by simp)).mp ht
    refine ⟨.int (0 - a), evalP_sub (by simp) (by simpa using hx), ?_⟩
    rw [lookup_set_self hf "y" _]
    simp only [Option.some.injEq, Value.int.injEq]
    omega
  · -- else branch: 0 ≤ x, so y = x
    refine H.cons (H.assignP "y" _ ?_) H.nil
    intro s ⟨⟨hf, hx⟩, hfalse⟩
    have hnlt : ¬ a < 0 := (Falsy_lt (by simpa using hx) (by simp)).mp hfalse
    refine ⟨.int a, by simpa using hx, ?_⟩
    rw [lookup_set_self hf "y" _]
    simp only [Option.some.injEq, Value.int.injEq]
    omega

/-! ## A verified composition of Python functions

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

`mulNonneg` computes `m * n` only for `n ≥ 0`, because the loop counts up to
`n`.  `mul` lifts that with the identity `m * n = (m * Int.sign n) * |n|`, which
is where `Int.sign 0 = 0` earns its keep: at `n = 0` both factors are `0` and the
product is `0 = m * 0`.

Nothing here is a rewriting of the loop.  `mulNonneg`'s body *is*
`mulNonnegProg` followed by `return r`, and `mulNonnegFn_spec` invokes
`mulNonnegProg_spec` as it stands -- sequenced onto the `return` by `H.append`,
and framed by `H.frame` with the assertion `InFrame s`, which is what discharges
"the callee did not touch the caller's state".

`mul` is verified against a **specification environment**, `mulEnv`: it assumes
`sign`, `mulNonneg` and `abs` meet their contracts and concludes that it meets
its own.  The three `def`s at the top of `mulProg` are what discharge that
assumption, via `H.funcDef`, which puts the very function value the interpreter
builds into the postcondition.
-/

/-- Scaling one factor by the sign of `n` and the other to `|n|` leaves the
product alone.  This is the whole reason `mul` works. -/
theorem mul_sign_natAbs (m n : Int) : m * Int.sign n * (n.natAbs : Int) = m * n := by
  rw [Int.mul_assoc, Int.sign_mul_natAbs]

/-! ### The program -/

/-- The three `def`s, as Python.  Shared by the specification and the concrete
run below, so that both are about one program. -/
def mulDefsSrc : String :=
"def sign(n):
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

"

/-- The Python source of the program verified below. -/
def mulSrc : String := mulDefsSrc ++ "r = mul(m, n)\n"

/-- The body of `sign`.  `elif` is desugared by the parser into a nested `if` in
the else-branch. -/
def signBody : Block :=
  [ .ifS (.compare (.name "n") [(.lt, .int 0)])
      [ .ret (some (.unop .neg (.int 1))) ]
      [ .ifS (.compare (.name "n") [(.gt, .int 0)])
          [ .ret (some (.int 1)) ]
          [ .ret (some (.int 0)) ] ] ]

/-- The body of `mulNonneg`: the verified loop, then `return r`. -/
def mulNonnegBody : Block := mulNonnegProg ++ [ .ret (some (.name "r")) ]

/-- The body of `mul`: one `return`, with two calls nested inside its
argument. -/
def mulBody : Block :=
  [ .ret (some (.call (.name "mulNonneg")
      [ .binop .mul (.name "m") (.call (.name "sign") [.name "n"] []),
        .call (.name "abs") [.name "n"] [] ] [])) ]

/-- The AST of `mulDefsSrc`. -/
def mulDefs : Block :=
  [ .funcDef "sign" [("n", Option.none)] signBody,
    .funcDef "mulNonneg" [("m", Option.none), ("n", Option.none)] mulNonnegBody,
    .funcDef "mul" [("m", Option.none), ("n", Option.none)] mulBody ]

/-- The AST of `mulSrc`. -/
def mulProg : Program :=
  mulDefs ++ [ .assign [.name "r"] (.call (.name "mul") [.name "m", .name "n"] []) ]

theorem mulSrc_lexes : tokenize mulSrc = .ok mulToks := by rfl

theorem mulSrc_parses : parse mulSrc = .ok mulProg := by
  unfold parse; rw [mulSrc_lexes]; rfl

/-! ### The function values and their contracts -/

/-- The value `def sign` binds at module level, where nothing is captured. -/
def signFn : Value := .func "sign" ["n"] [] signBody []

/-- The value `def mulNonneg` binds at module level. -/
def mulNonnegFn : Value := .func "mulNonneg" ["m", "n"] [] mulNonnegBody []

/-- The value `def mul` binds at module level. -/
def mulFn : Value := .func "mul" ["m", "n"] [] mulBody []

/-- `sign(a)` is `Int.sign a`, `sign(0) = 0` included. -/
def signC : Contract where
  pre := fun args => ∃ a : Int, args = [.int a]
  post := fun args v => ∀ a : Int, args = [.int a] → v = .int (Int.sign a)

/-- `mulNonneg(a, b)` is `a * b`, for `b ≥ 0`. -/
def mulNonnegC : Contract where
  pre := fun args => ∃ a b : Int, args = [.int a, .int b] ∧ 0 ≤ b
  post := fun args v => ∀ a b : Int, args = [.int a, .int b] → v = .int (a * b)

/-- `mul(a, b)` is `a * b`, for every `a` and every `b`. -/
def mulC : Contract where
  pre := fun args => ∃ a b : Int, args = [.int a, .int b]
  post := fun args v => ∀ a b : Int, args = [.int a, .int b] → v = .int (a * b)

/-- What `mul`'s body needs of the globals it is called under: the two functions
it calls bound to the values `def` builds for them, and `abs` still the builtin.

The last conjunct is the price of calling a builtin by name.  Python resolves
`abs` late, so a program that had rebound it would compute something else, and
the specification has to say so. -/
def MulDefs (gl : List (String × Value)) : Prop :=
  resolveGlobal gl "sign" = some signFn ∧
  resolveGlobal gl "mulNonneg" = some mulNonnegFn ∧
  resolveGlobal gl "abs" = some (.builtin "abs")

/-- The specification environment `mul`'s body is verified against. -/
def mulEnv : SpecEnv := [("sign", signC), ("mulNonneg", mulNonnegC), ("abs", absContract)]

/-! ### Reading argument lists back

The contracts are stated over `List Value`, so consuming one means undoing a
list-of-values equation.  These two do that. -/

private theorem int_arg1 {a b : Int} (h : [Value.int a] = [Value.int b]) : a = b := by
  simpa using h

private theorem int_arg2 {a b c d : Int}
    (h : [Value.int a, Value.int b] = [Value.int c, Value.int d]) : a = c ∧ b = d := by
  simpa using h

/-! ### `sign` -/

theorem signFn_spec (G : List (String × Value) → Prop) :
    CallSpec G signFn signC := by
  refine CallSpec.ofBody ?_
  intro args s _ hpre
  obtain ⟨a, rfl⟩ := hpre
  refine ⟨[("n", Value.int a)], by simp [bindParams, bindParams.go, aset], ?_⟩
  have hn : (s.enterFrame (callFrame [("n", Value.int a)] [])).lookupName "n" = some (.int a) := by
    simp [State.lookupName, State.enterFrame, callFrame, alook]
  have hu : Untouched s (s.enterFrame (callFrame [("n", Value.int a)] [])) :=
    (inFrame_enterFrame s _ []).2
  refine H.ifS _ _ _ ?_ ?_ ?_
  · intro t ht; subst ht
    exact ⟨.bool (decide (a < 0)), evalP_lt (by simpa using hn) (by simp)⟩
  · -- n < 0, so sign n = -1
    refine H.retP (.unop .neg (.int 1)) ?_
    intro t ⟨ht, htr⟩; subst ht
    have hlt : a < 0 := (Truthy_lt (by simpa using hn) (by simp)).mp htr
    refine ⟨.int (-1), evalP_neg (by simp), ?_, hu⟩
    intro b hb
    rw [← int_arg1 hb, Int.sign_eq_neg_one_of_neg hlt]
  · refine H.ifS _ _ _ ?_ ?_ ?_
    · intro t ⟨ht, _⟩; subst ht
      exact ⟨.bool (decide (0 < a)), evalP_gt (by simpa using hn) (by simp)⟩
    · -- n > 0, so sign n = 1
      refine H.retP (.int 1) ?_
      intro t ⟨⟨ht, _⟩, htr⟩; subst ht
      have hgt : 0 < a := (Truthy_gt (by simpa using hn) (by simp)).mp htr
      refine ⟨.int 1, by simp, ?_, hu⟩
      intro b hb
      rw [← int_arg1 hb, Int.sign_eq_one_of_pos hgt]
    · -- neither, so n = 0 and sign n = 0
      refine H.retP (.int 0) ?_
      intro t ⟨⟨ht, hf1⟩, hf2⟩; subst ht
      have hnlt : ¬ a < 0 := (Falsy_lt (by simpa using hn) (by simp)).mp hf1
      have hngt : ¬ 0 < a := (Falsy_gt (by simpa using hn) (by simp)).mp hf2
      have ha0 : a = 0 := by omega
      refine ⟨.int 0, by simp, ?_, hu⟩
      intro b hb
      rw [← int_arg1 hb, ha0]
      rfl

/-! ### `mulNonneg`

The loop proof is reused exactly as it stands.  `H.frame` conjoins `InFrame s` --
"still in the callee's frame, and the caller's state untouched" -- onto the
invariants of a derivation that knows nothing about it, and `H.append` sequences
the `return` onto the end. -/

theorem mulNonnegFn_spec (G : List (String × Value) → Prop) :
    CallSpec G mulNonnegFn mulNonnegC := by
  refine CallSpec.ofBody ?_
  intro args s _ hpre
  obtain ⟨a, b, rfl, hb⟩ := hpre
  refine ⟨[("m", Value.int a), ("n", Value.int b)],
    by simp [bindParams, bindParams.go, aset], ?_⟩
  have hin : InFrame s (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])) :=
    inFrame_enterFrame s _ []
  have hm : (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])).lookupName "m"
      = some (.int a) := by
    simp [State.lookupName, State.enterFrame, callFrame, alook]
  have hn : (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])).lookupName "n"
      = some (.int b) := by
    simp [State.lookupName, State.enterFrame, callFrame, alook]
  refine H.append (b₁ := mulNonnegProg) (b₂ := [.ret (some (.name "r"))])
      (H.conseq ?_
        ((mulNonnegProg_spec a b).frame (A := InFrame s) (fun _ x v hA => hA.setVar x v))
        (fun _ h => h) (fun _ _ h => h.1)) ?_
  · intro t ht; subst ht
    exact ⟨⟨⟨hin.plainScope, hm, hn⟩, hb⟩, hin⟩
  · refine H.retP (.name "r") ?_
    intro t ⟨hr, hif⟩
    refine ⟨.int (a * b), by simpa using hr, ?_, hif.untouched⟩
    intro c d hcd
    obtain ⟨hac, hbd⟩ := int_arg2 hcd
    rw [← hac, ← hbd]

/-! ### `mul`

The only rule that mentions calls is `EvalTo.callName`, and it is the only thing
this proof does three times.  `EvalTo.binop` is what lets `sign(n)` sit inside
`m * sign(n)`: an argument expression is described by the same judgement as any
other expression, so a call may be nested arbitrarily deep inside one. -/

/-- The three contracts `mul` assumes really are met, under `MulDefs`. -/
theorem mulEnv_holds : Holds mulEnv MulDefs := by
  intro nm c hmem gl hG
  simp only [mulEnv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨signFn, hG.1, signFn_spec MulDefs⟩
  · exact ⟨mulNonnegFn, hG.2.1, mulNonnegFn_spec MulDefs⟩
  · exact ⟨.builtin "abs", hG.2.2, absContract_spec MulDefs⟩

theorem mulFn_spec : CallSpec MulDefs mulFn mulC := by
  refine CallSpec.ofBody ?_
  intro args s hG hpre
  obtain ⟨a, b, rfl⟩ := hpre
  refine ⟨[("m", Value.int a), ("n", Value.int b)],
    by simp [bindParams, bindParams.go, aset], ?_⟩
  -- The frame the call builds, and what can be read in it.
  have hu : Untouched s (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])) :=
    (inFrame_enterFrame s _ []).2
  have hm : (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])).lookupName "m"
      = some (.int a) := by
    simp [State.lookupName, State.enterFrame, callFrame, alook]
  have hn : (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])).lookupName "n"
      = some (.int b) := by
    simp [State.lookupName, State.enterFrame, callFrame, alook]
  -- A name the frame does not shadow still resolves through the globals: this is
  -- how a contract stated about the globals survives entering the frame.
  have hres : ∀ nm : String, alook [("m", Value.int a), ("n", Value.int b)] nm = Option.none →
      (s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] [])).lookupName nm
        = resolveGlobal s.globals nm := by
    intro nm h
    exact State.lookupName_eq_resolveGlobal_of_frame (fr := callFrame _ []) rfl
      (by simpa using h) (by simp)
  have hgl : ∀ t : State,
      t = s.enterFrame (callFrame [("m", Value.int a), ("n", Value.int b)] []) →
      MulDefs t.globals := by
    intro t ht; subst ht; exact hG
  refine H.ret _ ?_
  refine EvalTo.callName (G := MulDefs) "mulNonneg" mulNonnegC hgl ?_ ?_
  · intro t ht; subst ht
    obtain ⟨fv, hfv, hspec⟩ := mulEnv_holds "mulNonneg" mulNonnegC (by simp [mulEnv]) _ hG
    exact ⟨fv, (hres "mulNonneg" (by simp [alook])).trans hfv, hspec⟩
  refine EvalsTo.cons (A := fun _ v => v = Value.int (a * Int.sign b)) ?_
    (B := fun _ vs => vs = [Value.int (b.natAbs : Int)]) ?_ ?_
  -- `m * sign(n)`
  · refine EvalTo.binop (A := fun _ v => v = Value.int a)
      (B := fun _ v => v = Value.int (Int.sign b)) (EvalTo.name "m" ?_) ?_ ?_
    · intro t ht; subst ht; exact ⟨_, hm, rfl⟩
    · refine EvalTo.callName (G := MulDefs) "sign" signC hgl ?_ ?_
      · intro t ht; subst ht
        obtain ⟨fv, hfv, hspec⟩ := mulEnv_holds "sign" signC (by simp [mulEnv]) _ hG
        exact ⟨fv, (hres "sign" (by simp [alook])).trans hfv, hspec⟩
      · refine EvalsTo.cons (A := fun _ v => v = Value.int b) (EvalTo.name "n" ?_)
          (B := fun _ vs => vs = []) (EvalsTo.nil (fun _ _ => rfl)) ?_
        · intro t ht; subst ht; exact ⟨_, hn, rfl⟩
        · intro t v vs _ hv hvs
          subst hv; subst hvs
          exact ⟨⟨b, rfl⟩, fun w hw => hw b rfl⟩
    · intro t x y _ hx hy
      subst hx; subst hy
      exact ⟨.int (a * Int.sign b), by simp [binOpK, asInt, intBinOpK], rfl⟩
  -- `abs(n)`
  · refine EvalsTo.cons (A := fun _ v => v = Value.int (b.natAbs : Int)) ?_
      (B := fun _ vs => vs = []) (EvalsTo.nil (fun _ _ => rfl)) ?_
    · refine EvalTo.callName (G := MulDefs) "abs" absContract hgl ?_ ?_
      · intro t ht; subst ht
        obtain ⟨fv, hfv, hspec⟩ := mulEnv_holds "abs" absContract (by simp [mulEnv]) _ hG
        exact ⟨fv, (hres "abs" (by simp [alook])).trans hfv, hspec⟩
      · refine EvalsTo.cons (A := fun _ v => v = Value.int b) (EvalTo.name "n" ?_)
          (B := fun _ vs => vs = []) (EvalsTo.nil (fun _ _ => rfl)) ?_
        · intro t ht; subst ht; exact ⟨_, hn, rfl⟩
        · intro t v vs _ hv hvs
          subst hv; subst hvs
          exact ⟨⟨b, rfl⟩, fun w hw => hw b rfl⟩
    · intro t v vs _ hv hvs
      subst hv; subst hvs; rfl
  -- and the two of them are exactly what `mulNonneg` wants
  · intro t v vs ht hv hvs
    subst hv; subst hvs; subst ht
    refine ⟨⟨a * Int.sign b, (b.natAbs : Int), rfl, by omega⟩, ?_⟩
    intro w hw
    have hval := hw (a * Int.sign b) (b.natAbs : Int) rfl
    refine ⟨?_, hu⟩
    intro c d hcd
    obtain ⟨hac, hbd⟩ := int_arg2 hcd
    rw [hval, ← hac, ← hbd, mul_sign_natAbs]

/-! ### The whole program -/

/-- Module-level state for the composed program: no function frame, `m` and `n`
bound to the given integers, and `abs` still the builtin.  At the initial state
the last conjunct is free, since `default`'s globals are empty. -/
def ModuleArgs (m n : Int) (s : State) : Prop :=
  s.frame = Option.none ∧
  s.lookupName "m" = some (.int m) ∧ s.lookupName "n" = some (.int n) ∧
  resolveGlobal s.globals "abs" = some (.builtin "abs")

/-- A module-level `def` adds one name to the globals and disturbs nothing
else. -/
private theorem moduleArgs_setVar {m n : Int} {s : State} (h : ModuleArgs m n s)
    {x : String} (hm : x ≠ "m") (hn : x ≠ "n") (ha : x ≠ "abs") (v : Value) :
    ModuleArgs m n (s.setVar x v) := by
  obtain ⟨hf, hmv, hnv, hab⟩ := h
  have hps := State.plainScope_of_frame_none hf
  refine ⟨by simp [hf], ?_, ?_, ?_⟩
  · rwa [lookup_set_other hps hm]
  · rwa [lookup_set_other hps hn]
  · rw [State.setVar_globals_of_frame_none hf, resolveGlobal_aset_of_ne _ ha]
    exact hab

/-- **The composed program computes the product, for every `m` and every `n`.**

The three `def`s establish the specification environment; the final assignment
calls `mul` through `EvalTo.callName`. -/
theorem mulProg_spec (m n : Int) {Rt : Value → Assn} :
    H (ModuleArgs m n) mulProg
      (fun s => s.lookupName "r" = some (.int (m * n))) Rt := by
  -- After each `def`, one more name resolves to the value `def` built.
  let Q1 : Assn := fun s => ModuleArgs m n s ∧ resolveGlobal s.globals "sign" = some signFn
  let Q2 : Assn := fun s => Q1 s ∧ resolveGlobal s.globals "mulNonneg" = some mulNonnegFn
  let Q3 : Assn := fun s => Q2 s ∧ resolveGlobal s.globals "mul" = some mulFn
  have d1 : H (ModuleArgs m n) [.funcDef "sign" [("n", Option.none)] signBody] Q1 Rt := by
    refine H.funcDef _ _ _ (by simp) ?_
    intro s hs
    refine ⟨moduleArgs_setVar hs (by decide) (by decide) (by decide) _, ?_⟩
    rw [State.setVar_globals_of_frame_none hs.1, resolveGlobal_aset_self]
    simp [signFn, hs.1]
  have d2 : H Q1 [.funcDef "mulNonneg" [("m", Option.none), ("n", Option.none)] mulNonnegBody]
      Q2 Rt := by
    refine H.funcDef _ _ _ (by simp) ?_
    intro s ⟨hs, hsign⟩
    refine ⟨⟨moduleArgs_setVar hs (by decide) (by decide) (by decide) _, ?_⟩, ?_⟩
    · rw [State.setVar_globals_of_frame_none hs.1, resolveGlobal_aset_of_ne _ (by decide)]
      exact hsign
    · rw [State.setVar_globals_of_frame_none hs.1, resolveGlobal_aset_self]
      simp [mulNonnegFn, hs.1]
  have d3 : H Q2 [.funcDef "mul" [("m", Option.none), ("n", Option.none)] mulBody] Q3 Rt := by
    refine H.funcDef _ _ _ (by simp) ?_
    intro s ⟨⟨hs, hsign⟩, hmn⟩
    refine ⟨⟨⟨moduleArgs_setVar hs (by decide) (by decide) (by decide) _, ?_⟩, ?_⟩, ?_⟩
    · rw [State.setVar_globals_of_frame_none hs.1, resolveGlobal_aset_of_ne _ (by decide)]
      exact hsign
    · rw [State.setVar_globals_of_frame_none hs.1, resolveGlobal_aset_of_ne _ (by decide)]
      exact hmn
    · rw [State.setVar_globals_of_frame_none hs.1, resolveGlobal_aset_self]
      simp [mulFn, hs.1]
  have d4 : H Q3 [.assign [.name "r"] (.call (.name "mul") [.name "m", .name "n"] [])]
      (fun s => s.lookupName "r" = some (.int (m * n))) Rt := by
    refine H.assign "r" _ ?_
    refine EvalTo.callName (G := MulDefs) "mul" mulC ?_ ?_ ?_
    · intro s hs
      exact ⟨hs.1.1.2, hs.1.2, hs.1.1.1.2.2.2⟩
    · intro s hs
      refine ⟨mulFn, ?_, mulFn_spec⟩
      rw [State.lookupName_eq_resolveGlobal_of_frame_none hs.1.1.1.1]
      exact hs.2
    · refine EvalsTo.cons (A := fun _ v => v = Value.int m) (EvalTo.name "m" ?_)
        (B := fun _ vs => vs = [Value.int n]) ?_ ?_
      · intro s hs; exact ⟨_, hs.1.1.1.2.1, rfl⟩
      · refine EvalsTo.cons (A := fun _ v => v = Value.int n) (EvalTo.name "n" ?_)
          (B := fun _ vs => vs = []) (EvalsTo.nil (fun _ _ => rfl)) ?_
        · intro s hs; exact ⟨_, hs.1.1.1.2.2.1, rfl⟩
        · intro s v vs _ hv hvs; subst hv; subst hvs; rfl
      · intro s v vs hs hv hvs
        subst hv; subst hvs
        refine ⟨⟨m, n, rfl⟩, ?_⟩
        intro w hw
        rw [lookup_set_self (State.plainScope_of_frame_none hs.1.1.1.1) "r" w,
          hw m n rfl]
  exact H.append (H.cons d1 (H.cons d2 (H.cons d3 H.nil))) d4

/-! ### Concrete runs of the composed program

The same three `def`s, with a `print` instead of the assignment: all four sign
combinations, and then the two zero cases -- the ones a `sign 0 = 1` convention
would get wrong.

They are two programs rather than one because reducing a call is what makes the
resulting *state* an unreduced term, and every read of that state inside the next
call re-derives it.  Nested calls therefore cost multiplicatively: four in one
program reduce in a couple of seconds, six in tens.  It is the same
shared-subterm effect that stops `parse src` from reducing in one step (see the
note in `SnakeFight.ExampleToks`), here in the interpreter rather than the
parser. -/

def mulRunSrc : String :=
  mulDefsSrc ++ "print(mul(6, 7), mul(6, -7), mul(-6, 7), mul(-6, -7))\n"

def mulRunProg : Program :=
  mulDefs ++
  [ .expr (.call (.name "print")
      [ .call (.name "mul") [.int 6, .int 7] [],
        .call (.name "mul") [.int 6, .unop .neg (.int 7)] [],
        .call (.name "mul") [.unop .neg (.int 6), .int 7] [],
        .call (.name "mul") [.unop .neg (.int 6), .unop .neg (.int 7)] [] ] []) ]

theorem mulRunSrc_lexes : tokenize mulRunSrc = .ok mulRunToks := by rfl

theorem mulRunSrc_parses : parse mulRunSrc = .ok mulRunProg := by
  unfold parse; rw [mulRunSrc_lexes]; rfl

set_option maxHeartbeats 1000000 in
theorem mulRunProg_prints : outputOfProg mulRunProg = some ["42 -42 -42 42"] := rfl

/-- The same run, stated about the source text. -/
theorem mulRunSrc_prints : outputOf mulRunSrc = some ["42 -42 -42 42"] :=
  (outputOf_of_parse mulRunSrc_parses).trans mulRunProg_prints

def mulZeroSrc : String := mulDefsSrc ++ "print(mul(5, 0), mul(0, -3))\n"

def mulZeroProg : Program :=
  mulDefs ++
  [ .expr (.call (.name "print")
      [ .call (.name "mul") [.int 5, .int 0] [],
        .call (.name "mul") [.int 0, .unop .neg (.int 3)] [] ] []) ]

theorem mulZeroSrc_lexes : tokenize mulZeroSrc = .ok mulZeroToks := by rfl

theorem mulZeroSrc_parses : parse mulZeroSrc = .ok mulZeroProg := by
  unfold parse; rw [mulZeroSrc_lexes]; rfl

theorem mulZeroProg_prints : outputOfProg mulZeroProg = some ["0 0"] := rfl

/-- The same run, stated about the source text. -/
theorem mulZeroSrc_prints : outputOf mulZeroSrc = some ["0 0"] :=
  (outputOf_of_parse mulZeroSrc_parses).trans mulZeroProg_prints

/-! ## What the specifications buy us

`H.correct` turns a derivation into a statement about the interpreter that the
CLI actually runs: for *any* fuel budget, if the program finishes normally then
the postcondition holds. -/

/-- For every `m` and every non-negative `n`, and for every fuel budget: if
`mulNonnegProg` finishes normally, then `r` is `m * n`. -/
theorem mulNonnegProg_correct (m n : Int) (fuel : Nat) (s s' : State)
    (hpre : Args m n s ∧ 0 ≤ n) (hrun : execBlock fuel mulNonnegProg s = .ok .normal s') :
    s'.lookupName "r" = some (.int (m * n)) :=
  (mulNonnegProg_spec m n (Rt := fun _ _ => True)).correct hpre hrun

/-- For every `a` and every fuel budget: if `absProg` finishes normally, then
`y` is the absolute value of `a`. -/
theorem absProg_correct (a : Int) (fuel : Nat) (s s' : State)
    (hpre : s.plainScope ∧ s.lookupName "x" = some (.int a))
    (hrun : execBlock fuel absProg s = .ok .normal s') :
    s'.lookupName "y" = some (.int (a.natAbs : Int)) :=
  (absProg_spec a (Rt := fun _ _ => True)).correct hpre hrun

/-- For every `m`, every `n` -- negative included -- and every fuel budget: if
`mulProg` finishes normally, then `r` is `m * n`. -/
theorem mulProg_correct (m n : Int) (fuel : Nat) (s s' : State)
    (hpre : ModuleArgs m n s) (hrun : execBlock fuel mulProg s = .ok .normal s') :
    s'.lookupName "r" = some (.int (m * n)) :=
  (mulProg_spec m n (Rt := fun _ _ => True)).correct hpre hrun

/-! ## Axiom audit

Everything proved in this file -- the concrete runs as well as the
specifications -- rests on nothing but Lean's own three axioms.  In particular
`Lean.ofReduceBool` does not appear, so no part of any proof here is delegated
to the compiler.  These are `#guard_msgs`, so the build fails if that ever
stops being true.
-/

/-- info: 'SnakeFight.addProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addProg_prints

/-- info: 'SnakeFight.addSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addSrc_prints

/-- info: 'SnakeFight.concatProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concatProg_prints

/-- info: 'SnakeFight.concatSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concatSrc_prints

/-- info: 'SnakeFight.aliasProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms aliasProg_prints

/-- info: 'SnakeFight.aliasSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms aliasSrc_prints

/-- info: 'SnakeFight.adderProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adderProg_prints

/-- info: 'SnakeFight.adderSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adderSrc_prints

/-- info: 'SnakeFight.excProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms excProg_prints

/-- info: 'SnakeFight.excSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms excSrc_prints

/-- info: 'SnakeFight.divProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms divProg_prints

/-- info: 'SnakeFight.divSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms divSrc_prints

/-- info: 'SnakeFight.mul67Prog_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mul67Prog_prints

/-- info: 'SnakeFight.mul67Src_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mul67Src_prints

/-- info: 'SnakeFight.mulRunProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulRunProg_prints

/-- info: 'SnakeFight.mulRunSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulRunSrc_prints

/-- info: 'SnakeFight.mulZeroProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulZeroProg_prints

/-- info: 'SnakeFight.mulZeroSrc_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulZeroSrc_prints

/-- info: 'SnakeFight.addSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addSrc_parses

/-- info: 'SnakeFight.concatSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concatSrc_parses

/-- info: 'SnakeFight.aliasSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms aliasSrc_parses

/-- info: 'SnakeFight.adderSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adderSrc_parses

/-- info: 'SnakeFight.excSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms excSrc_parses

/-- info: 'SnakeFight.divSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms divSrc_parses

/-- info: 'SnakeFight.mulNonnegSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulNonnegSrc_parses

/-- info: 'SnakeFight.mul67Src_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mul67Src_parses

/-- info: 'SnakeFight.absSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absSrc_parses

/-- info: 'SnakeFight.mulSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulSrc_parses

/-- info: 'SnakeFight.mulRunSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulRunSrc_parses

/-- info: 'SnakeFight.mulZeroSrc_parses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulZeroSrc_parses

/-- info: 'SnakeFight.H.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms H.sound

/-- info: 'SnakeFight.H.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms H.frame

/-- info: 'SnakeFight.CallSpec.ofBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CallSpec.ofBody

/-- info: 'SnakeFight.EvalTo.callName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms EvalTo.callName

/-- info: 'SnakeFight.evalP_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalP_agrees

/--
info: 'SnakeFight.mulNonnegProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms mulNonnegProg_spec

/--
info: 'SnakeFight.mulNonnegProg_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms mulNonnegProg_correct

/-- info: 'SnakeFight.absProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absProg_spec

/-- info: 'SnakeFight.absProg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absProg_correct

/-- info: 'SnakeFight.signFn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signFn_spec

/--
info: 'SnakeFight.mulNonnegFn_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms mulNonnegFn_spec

/-- info: 'SnakeFight.mulFn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulFn_spec

/-- info: 'SnakeFight.mulProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulProg_spec

/-- info: 'SnakeFight.mulProg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulProg_correct

end SnakeFight
