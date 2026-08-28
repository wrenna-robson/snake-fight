import SnakeFight.Reason
import SnakeFight.Interp

/-!
# Worked examples

Two kinds of statement about Python programs, both machine-checked.

## 1. Concrete runs

`outputOf src` is an ordinary Lean function, so "this program prints this" is an
equation between values.  These are discharged by `native_decide`, i.e. by
compiling and running the interpreter and trusting the result (it adds
`Lean.ofReduceBool` to the proof's axioms).  The kernel can also do it, but the
front end is far too slow to reduce inside the kernel, so `native_decide` is the
practical choice.

## 2. Symbolic correctness

`mulProg_spec` and `absProg_spec` are proofs *for all inputs*, using the Hoare
logic of `SnakeFight.Hoare`, and they are checked by the kernel with no extra
axioms.  They are stated about the AST; the `#guard` line above each one checks,
at build time, that the parser really does turn the displayed Python source into
that AST.
-/

namespace SnakeFight

/-! ## Concrete runs -/

example : outputOf "print(1 + 2)" = some ["3"] := by native_decide

example : outputOf "print('hello ' + 'world')" = some ["hello world"] := by native_decide

/-- Aliasing behaves like Python's, not like a value semantics. -/
example :
    outputOf "a = [1, 2]
b = a
b.append(3)
print(a, a is b)" = some ["[1, 2, 3] True"] := by native_decide

/-- Recursion, closures and comprehensions all work together. -/
example :
    outputOf "def make_adder(n):
    def add(v):
        return v + n
    return add
add3 = make_adder(3)
print([add3(i) for i in range(5)])" = some ["[3, 4, 5, 6, 7]"] := by native_decide

/-- Exceptions, including the class hierarchy and `finally`. -/
example :
    outputOf "try:
    raise KeyError('k')
except LookupError as e:
    print('caught', e)
finally:
    print('cleanup')" = some ["caught 'k'", "cleanup"] := by native_decide

/-- Integer division and modulus follow Python, not C. -/
example : outputOf "print(-7 // 2, -7 % 2, 2 ** 70)"
    = some ["-4 1 1180591620717411303424"] := by native_decide

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
#guard (match parse mulSrc with | .ok p => p == mulProg | .error _ => false)

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

/-- A concrete run of the same program, for `m = 6`, `n = 7`. -/
example :
    outputOf "m = 6
n = 7
r = 0
i = 0
while i < n:
    r = r + m
    i = i + 1
print(r)" = some ["42"] := by native_decide

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
#guard (match parse absSrc with | .ok p => p == absProg | .error _ => false)

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

end SnakeFight
