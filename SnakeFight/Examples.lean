import SnakeFight.Reason
import SnakeFight.Interp

/-!
# Worked examples

Two kinds of statement about Python programs, both machine-checked.

## 1. Concrete runs

`outputOfProg p` is an ordinary Lean function, so "this program prints this" is
an equation between values, and the kernel proves it.  Each run below is a
theorem, checked with no axioms beyond Lean's own three -- in particular
without `Lean.ofReduceBool`, so the Lean compiler is not part of what you have
to believe.

The theorems are stated about the AST, with a `#guard` checking that the parser
turns the displayed Python into that AST.  That split is forced.  The
interpreter reduces in the kernel in milliseconds, but the parser does not
reduce there at all: evaluating `parse` on even a one-token program runs for
minutes and then exhausts memory, at every fuel budget we tried.  So the
source-to-AST step is checked by running the compiled parser instead.

Writing the AST out by hand is what gives that check something to check
against.  If the parser ever disagreed, the `#guard` would fail the build --
which it could not do if the AST were generated from the source by the same
parser it is meant to check.

## 2. Symbolic correctness

`mulProg_spec` and `absProg_spec` are proofs *for all inputs*, using the Hoare
logic of `SnakeFight.Hoare`, rather than statements about one run.  They are
stated about the AST and paired with a `#guard` for the same reasons as above.
-/

namespace SnakeFight

/-! ## Concrete runs -/

/-- The parser agrees that `src` is `prog`.  Every concrete run below pairs its
theorem with one of these. -/
def parsesAs (src : String) (prog : Program) : Bool :=
  match parse src with
  | .ok p => p == prog
  | .error _ => false

/-! ### Arithmetic -/

def addSrc : String := "print(1 + 2)\n"

def addProg : Program :=
  [ .expr (.call (.name "print") [.binop .add (.int 1) (.int 2)] []) ]

#guard parsesAs addSrc addProg

theorem addProg_prints : outputOfProg addProg = some ["3"] := by decide

/-! ### String concatenation -/

def concatSrc : String := "print('hello ' + 'world')\n"

def concatProg : Program :=
  [ .expr (.call (.name "print") [.binop .add (.str "hello ") (.str "world")] []) ]

#guard parsesAs concatSrc concatProg

theorem concatProg_prints : outputOfProg concatProg = some ["hello world"] := by
  decide

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

#guard parsesAs aliasSrc aliasProg

theorem aliasProg_prints : outputOfProg aliasProg = some ["[1, 2, 3] True"] := by
  decide

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

#guard parsesAs adderSrc adderProg

theorem adderProg_prints : outputOfProg adderProg = some ["[3, 4, 5, 6, 7]"] := by
  decide

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

#guard parsesAs excSrc excProg

theorem excProg_prints : outputOfProg excProg = some ["caught 'k'", "cleanup"] := by
  decide

/-! ### Division, modulus and big integers

Integer division and modulus follow Python, not C, and `int` is unbounded. -/

def divSrc : String := "print(-7 // 2, -7 % 2, 2 ** 70)\n"

def divProg : Program :=
  [ .expr (.call (.name "print")
      [ .binop .floordiv (.unop .neg (.int 7)) (.int 2),
        .binop .mod (.unop .neg (.int 7)) (.int 2),
        .binop .pow (.int 2) (.int 70) ] []) ]

#guard parsesAs divSrc divProg

theorem divProg_prints :
    outputOfProg divProg = some ["-4 1 1180591620717411303424"] := by decide

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
def mulSrc : String :=
"r = 0
i = 0
while i < n:
    r = r + m
    i = i + 1
"

/-- The loop guard `i < n`. -/
def mulGuard : Expr := .compare (.name "i") [(.lt, .name "n")]

/-- The loop body: `r = r + m` then `i = i + 1`. -/
def mulBody : Block :=
  [ .assign [.name "r"] (.binop .add (.name "r") (.name "m")),
    .assign [.name "i"] (.binop .add (.name "i") (.int 1)) ]

/-- The AST of `mulSrc`. -/
def mulProg : Program :=
  [ .assign [.name "r"] (.int 0),
    .assign [.name "i"] (.int 0),
    .whileS mulGuard mulBody ]

-- Build-time check that the parser agrees that `mulSrc` is `mulProg`.
#guard parsesAs mulSrc mulProg

/-- Module-level state in which `m` and `n` are bound to the given integers. -/
def Args (m n : Int) (s : State) : Prop :=
  s.frame = Option.none ∧ s.lookupName "m" = some (.int m) ∧ s.lookupName "n" = some (.int n)

/-- Precondition: `m` and `n` are integers and `n` is not negative. -/
def MulPre (m n : Int) (s : State) : Prop := Args m n s ∧ 0 ≤ n

/-- After the first assignment, `r` is `0`. -/
def MulMid (m n : Int) (s : State) : Prop :=
  Args m n s ∧ 0 ≤ n ∧ s.lookupName "r" = some (.int 0)

/-- The loop invariant: `r = m * i` and `i` has not passed `n`. -/
def MulInv (m n : Int) (s : State) : Prop :=
  Args m n s ∧ ∃ i r : Int,
    s.lookupName "i" = some (.int i) ∧ s.lookupName "r" = some (.int r) ∧
    0 ≤ i ∧ i ≤ n ∧ r = m * i

/-- Halfway through the loop body: `r` has been updated but `i` has not. -/
def MulBody (m n : Int) (s : State) : Prop :=
  Args m n s ∧ ∃ i r : Int,
    s.lookupName "i" = some (.int i) ∧ s.lookupName "r" = some (.int r) ∧
    0 ≤ i ∧ i < n ∧ r = m * (i + 1)

/-- Postcondition: `r` holds the product. -/
def MulPost (m n : Int) (s : State) : Prop := s.lookupName "r" = some (.int (m * n))

/-- Assigning to one global leaves the other globals, and the frame, alone. -/
private theorem args_setVar {m n : Int} {s : State} (h : Args m n s) {x : String}
    (hm : x ≠ "m") (hn : x ≠ "n") (v : Value) : Args m n (s.setVar x v) := by
  obtain ⟨hf, hmv, hnv⟩ := h
  refine ⟨by simp [State.setVar, hf], ?_, ?_⟩
  · rw [lookup_set_other hf hm, hmv]
  · rw [lookup_set_other hf hn, hnv]

/-- **The loop computes the product.** -/
theorem mulProg_spec (m n : Int) : H (MulPre m n) mulProg (MulPost m n) := by
  -- r = 0
  have step1 : H (MulPre m n) [.assign [.name "r"] (.int 0)] (MulMid m n) := by
    refine H.assign "r" (.int 0) ?_
    intro s hP
    obtain ⟨hargs, hn⟩ := hP
    refine ⟨.int 0, by simp, ?_, hn, ?_⟩
    · exact args_setVar hargs (by decide) (by decide) _
    · exact lookup_set_self hargs.1 "r" (.int 0)
  -- i = 0
  have step2 : H (MulMid m n) [.assign [.name "i"] (.int 0)] (MulInv m n) := by
    refine H.assign "i" (.int 0) ?_
    intro s hP
    obtain ⟨hargs, hn, hr⟩ := hP
    refine ⟨.int 0, by simp, args_setVar hargs (by decide) (by decide) _, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
    · exact lookup_set_self hargs.1 "i" (.int 0)
    · rw [lookup_set_other hargs.1 (by decide), hr]
    · omega
    · exact hn
    · simp
  -- r = r + m
  have body1 : H (fun s => MulInv m n s ∧ Truthy mulGuard s)
      [.assign [.name "r"] (.binop .add (.name "r") (.name "m"))] (MulBody m n) := by
    refine H.assign "r" _ ?_
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
  have body2 : H (MulBody m n) [.assign [.name "i"] (.binop .add (.name "i") (.int 1))]
      (MulInv m n) := by
    refine H.assign "i" _ ?_
    intro s hP
    obtain ⟨hargs, i, r, hi, hr, hi0, hin, hri⟩ := hP
    refine ⟨.int (i + 1), evalP_add (by simpa using hi) (by simp), ?_⟩
    refine ⟨args_setVar hargs (by decide) (by decide) _, i + 1, r, ?_, ?_, by omega, by omega, hri⟩
    · exact lookup_set_self hargs.1 "i" _
    · rw [lookup_set_other hargs.1 (by decide), hr]
  -- the loop
  have loop : H (MulInv m n) [.whileS mulGuard mulBody]
      (fun s => MulInv m n s ∧ Falsy mulGuard s) := by
    refine H.whileS (MulInv m n) mulGuard mulBody ?_ (H.cons body1 (H.cons body2 H.nil))
    intro s hI
    obtain ⟨hargs, i, r, hi, hr, _, _, _⟩ := hI
    exact ⟨.bool (decide (i < n)), evalP_lt (by simpa using hi) (by simpa using hargs.2.2)⟩
  -- and the loop exits with i = n
  have finish : ∀ s, (MulInv m n s ∧ Falsy mulGuard s) → MulPost m n s := by
    intro s ⟨hI, hf⟩
    obtain ⟨hargs, i, r, hi, hr, hi0, hin, hri⟩ := hI
    have hnlt : ¬ i < n := (Falsy_lt (by simpa using hi) (by simpa using hargs.2.2)).mp hf
    have : i = n := by omega
    rw [this] at hri
    rw [hri] at hr
    exact hr
  exact H.cons step1 (H.cons step2 (H.cons (H.conseq (fun _ h => h) loop finish) H.nil))

/-! ### A concrete run of the verified program

The same `mulProg`, wrapped in bindings for `m` and `n` and a `print`, so the
run and the specification are demonstrably about one program rather than two
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
    .assign [.name "n"] (.int 7) ] ++ mulProg ++
  [ .expr (.call (.name "print") [.name "r"] []) ]

#guard parsesAs mul67Src mul67Prog

theorem mul67Prog_prints : outputOfProg mul67Prog = some ["42"] := by decide

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

-- Build-time check that the parser agrees that `absSrc` is `absProg`.
#guard parsesAs absSrc absProg

/-- **The conditional computes an absolute value.** -/
theorem absProg_spec (a : Int) :
    H (fun s => s.frame = Option.none ∧ s.lookupName "x" = some (.int a))
      absProg
      (fun s => s.lookupName "y" = some (.int (if a < 0 then -a else a))) := by
  refine H.cons (H.ifS _ _ _ ?_ ?_ ?_) H.nil
  · -- the guard is well defined: `x` is an int
    intro s ⟨_, hx⟩
    exact ⟨.bool (decide (a < 0)), evalP_lt (by simpa using hx) (by simp)⟩
  · -- then branch: x < 0, so y = -x
    refine H.cons (H.assign "y" _ ?_) H.nil
    intro s ⟨⟨hf, hx⟩, ht⟩
    have hlt : a < 0 := (Truthy_lt (by simpa using hx) (by simp)).mp ht
    refine ⟨.int (0 - a), evalP_sub (by simp) (by simpa using hx), ?_⟩
    rw [lookup_set_self hf "y" _]
    simp [hlt]
  · -- else branch: 0 ≤ x, so y = x
    refine H.cons (H.assign "y" _ ?_) H.nil
    intro s ⟨⟨hf, hx⟩, hfalse⟩
    have hnlt : ¬ a < 0 := (Falsy_lt (by simpa using hx) (by simp)).mp hfalse
    refine ⟨.int a, by simpa using hx, ?_⟩
    rw [lookup_set_self hf "y" _]
    simp [hnlt]

/-! ## What the specifications buy us

`H.correct` turns a derivation into a statement about the interpreter that the
CLI actually runs: for *any* fuel budget, if the program finishes normally then
the postcondition holds. -/

/-- For every `m` and every non-negative `n`, and for every fuel budget: if
`mulProg` finishes normally, then `r` is `m * n`. -/
theorem mulProg_correct (m n : Int) (fuel : Nat) (s s' : State)
    (hpre : MulPre m n s) (hrun : execBlock fuel mulProg s = .ok .normal s') :
    s'.lookupName "r" = some (.int (m * n)) :=
  (mulProg_spec m n).correct hpre hrun

/-! ## Axiom audit

Everything proved in this file -- the concrete runs as well as the
specifications -- rests on nothing but Lean's own three axioms.  In particular
`Lean.ofReduceBool` does not appear, so no part of any proof here is delegated
to the compiler.  These are `#guard_msgs`, so the build fails if that ever
stops being true.
-/

/-- info: 'SnakeFight.addProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addProg_prints

/-- info: 'SnakeFight.concatProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concatProg_prints

/-- info: 'SnakeFight.aliasProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms aliasProg_prints

/-- info: 'SnakeFight.adderProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adderProg_prints

/-- info: 'SnakeFight.excProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms excProg_prints

/-- info: 'SnakeFight.divProg_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms divProg_prints

/-- info: 'SnakeFight.mul67Prog_prints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mul67Prog_prints

/-- info: 'SnakeFight.H.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms H.sound

/-- info: 'SnakeFight.evalP_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalP_agrees

/-- info: 'SnakeFight.mulProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulProg_spec

/-- info: 'SnakeFight.mulProg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mulProg_correct

/-- info: 'SnakeFight.absProg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absProg_spec

end SnakeFight
