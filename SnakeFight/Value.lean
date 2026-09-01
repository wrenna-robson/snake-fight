import SnakeFight.Ast

/-!
# Runtime values, the object heap, and the interpreter monad

Two design decisions here shape everything else.

**Mutable objects live in a heap.**  Lists and dicts are `Value.ref` handles
into `State.heap`, so aliasing behaves the way it does in Python:

```python
a = [1, 2]; b = a; b.append(3); print(a)   # [1, 2, 3]
```

Ints, strings, `None` and tuples are immutable and are represented directly.

**Everything is pure.**  `print` appends to `State.out` instead of doing `IO`,
and the interpreter is a total function from state to result.  A program run is
therefore an ordinary Lean expression that we can compute with and prove things
about (see `SnakeFight.Hoare`).
-/

namespace SnakeFight

/-- Address of a mutable object in the heap. -/
abbrev Addr := Nat

/-- A runtime Python value. -/
inductive Value where
  | none
  | bool (b : Bool)
  | int (i : Int)
  | str (s : String)
  /-- Tuples are immutable, so they are values rather than heap objects. -/
  | tuple (vs : List Value)
  /-- A handle on a mutable heap object (list or dict). -/
  | ref (a : Addr)
  /-- A user function together with the environment captured at `def` time.
  `defaults` supplies values for the *last* `defaults.length` parameters. -/
  | func (name : String) (params : List String) (defaults : List Value)
      (body : Block) (env : List (String × Value))
  /-- A builtin function such as `len`. -/
  | builtin (name : String)
  /-- A bound method such as `xs.append`. -/
  | method (recv : Value) (name : String)
  /-- An exception class such as `ValueError`, which is callable. -/
  | excClass (name : String)
  /-- An exception instance. -/
  | exc (name : String) (args : List Value)
  deriving Repr, Inhabited, BEq

/-- A mutable heap object. -/
inductive Obj where
  /-- A `list`. -/
  | list (items : List Value)
  /-- A `dict`, in insertion order. -/
  | dict (entries : List (Value × Value))
  deriving Repr, Inhabited, BEq

/-! ## Association lists

Environments and dicts are association lists.  Insertion order is preserved
because Python dicts are ordered, and because it makes output deterministic. -/

/-- Look up a key. -/
def alook (l : List (String × Value)) (k : String) : Option Value :=
  match l with
  | [] => Option.none
  | (k', v) :: rest => if k' == k then some v else alook rest k

/-- Update a key in place, or append it if it is new. -/
def aset (l : List (String × Value)) (k : String) (v : Value) : List (String × Value) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: aset rest k v

/-- Remove a key. -/
def adel (l : List (String × Value)) (k : String) : List (String × Value) :=
  match l with
  | [] => []
  | (k', v') :: rest => if k' == k then rest else (k', v') :: adel rest k

@[simp] theorem alook_nil (k : String) : alook [] k = Option.none := rfl

@[simp] theorem alook_aset_self (l : List (String × Value)) (k : String) (v : Value) :
    alook (aset l k v) k = some v := by
  induction l with
  | nil => simp [alook, aset]
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases h : k' = k
    · subst h; simp [alook, aset]
    · simp [alook, aset, h, ih]

@[simp] theorem alook_aset_of_ne (l : List (String × Value)) {k j : String} (h : k ≠ j)
    (v : Value) : alook (aset l k v) j = alook l j := by
  induction l with
  | nil => simp [alook, aset, h]
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases h1 : k' = k
    · subst h1; simp [alook, aset, h]
    · simp [alook, aset, h1, ih]

/-! ## Machine state -/

/-- The activation record of a running function. -/
structure Frame where
  /-- Local variables. -/
  locals : List (String × Value) := []
  /-- Variables captured from the enclosing `def`. -/
  captured : List (String × Value) := []
  /-- Names declared `global` in this function body. -/
  globalDecls : List String := []
  deriving Repr, Inhabited, BEq

/-- The whole state of a running program. -/
structure State where
  /-- Module-level variables. -/
  globals : List (String × Value) := []
  /-- The current function frame; `none` at module level. -/
  frame : Option Frame := Option.none
  /-- Mutable objects, addressed by their index. -/
  heap : Array Obj := #[]
  /-- Lines written by `print`, most recent first. -/
  out : List String := []
  deriving Repr, Inhabited, BEq

/-- The lines printed so far, in order. -/
def State.stdout (s : State) : List String := s.out.reverse

/-- Names that resolve to builtin functions. -/
def builtinNames : List String :=
  ["print", "len", "range", "str", "int", "bool", "abs", "min", "max", "sum",
   "sorted", "list", "tuple", "dict", "reversed", "enumerate", "zip", "isinstance",
   "type", "ord", "chr", "divmod", "repr", "any", "all", "id"]

/-- Exception classes, paired with their base class.  Used both for name
resolution and for matching `except` clauses. -/
def excBases : List (String × String) :=
  [("Exception", "BaseException"),
   ("ArithmeticError", "Exception"),
   ("ZeroDivisionError", "ArithmeticError"),
   ("LookupError", "Exception"),
   ("IndexError", "LookupError"),
   ("KeyError", "LookupError"),
   ("NameError", "Exception"),
   ("TypeError", "Exception"),
   ("ValueError", "Exception"),
   ("AttributeError", "Exception"),
   ("AssertionError", "Exception"),
   ("StopIteration", "Exception"),
   ("RuntimeError", "Exception"),
   ("NotImplementedError", "RuntimeError")]

/-- Is `name` an exception class? -/
def isExcName (name : String) : Bool :=
  name == "BaseException" || excBases.any (fun p => p.1 == name)

/-- Is `sub` the same class as `base`, or one of its subclasses? -/
def excIsSubclass (sub base : String) : Bool :=
  go 32 sub
where
  go : Nat → String → Bool
    | 0, _ => false
    | n + 1, s =>
      if s == base then true
      else match excBases.find? (fun p => p.1 == s) with
        | some (_, b) => go n b
        | Option.none => false

/-- Resolve a name that is not bound in any environment: builtins and exception
classes live in a notional builtins module. -/
def builtinValue (x : String) : Option Value :=
  if builtinNames.contains x then some (.builtin x)
  else if isExcName x then some (.excClass x)
  else Option.none

/-- Look up a variable in the environment: locals, then captured variables,
then globals, then builtins.  Both the interpreter and the specification-level
evaluator of `SnakeFight.Pure` go through this function, so they cannot
disagree about scoping. -/
def State.lookupName (s : State) (x : String) : Option Value :=
  match s.frame with
  | Option.none => match alook s.globals x with
    | some v => some v
    | Option.none => builtinValue x
  | some fr =>
    match alook fr.locals x with
    | some v => some v
    | Option.none => match alook fr.captured x with
      | some v => some v
      | Option.none => match alook s.globals x with
        | some v => some v
        | Option.none => builtinValue x

/-- Assign to a variable, respecting `global` declarations. -/
def State.setVar (s : State) (x : String) (v : Value) : State :=
  match s.frame with
  | Option.none => { s with globals := aset s.globals x v }
  | some fr =>
    if fr.globalDecls.contains x then { s with globals := aset s.globals x v }
    else { s with frame := some { fr with locals := aset fr.locals x v } }

/-- Assignment is a plain local update: either we are at module level, or in a
frame with no `global` declaration in force.  Every frame the interpreter builds
for a call starts out this way, and only a `global` statement changes it.

This is the scope hypothesis the reasoning lemmas below take.  It is weaker than
`s.frame = none`, which is what lets one verified block be reused both at module
level and inside a function body. -/
def State.plainScope (s : State) : Prop :=
  ∀ fr, s.frame = some fr → fr.globalDecls = []

theorem State.plainScope_of_frame_none {s : State} (h : s.frame = Option.none) :
    s.plainScope := by
  intro fr hfr; rw [h] at hfr; exact absurd hfr (by simp)

@[simp] theorem State.setVar_heap (s : State) (x : String) (v : Value) :
    (s.setVar x v).heap = s.heap := by
  cases hf : s.frame <;> simp [State.setVar, hf] <;> split <;> rfl

@[simp] theorem State.setVar_out (s : State) (x : String) (v : Value) :
    (s.setVar x v).out = s.out := by
  cases hf : s.frame <;> simp [State.setVar, hf] <;> split <;> rfl

@[simp] theorem State.setVar_frame_none (s : State) (x : String) (v : Value)
    (h : s.frame = Option.none) : (s.setVar x v).frame = Option.none := by
  simp [State.setVar, h]

/-- Assigning to a variable keeps the scope plain. -/
theorem State.plainScope_setVar {s : State} (h : s.plainScope) (x : String) (v : Value) :
    (s.setVar x v).plainScope := by
  cases hf : s.frame with
  | none => intro fr hfr; simp [State.setVar, hf] at hfr
  | some g =>
    have hg : g.globalDecls = [] := h g hf
    intro fr hfr
    simp [State.setVar, hf, hg] at hfr
    subst hfr
    rfl

/-- Inside a plain scope, an assignment stays inside the current frame: the
globals are untouched unless there is no frame at all. -/
theorem State.setVar_globals_of_frame {s : State} {fr : Frame} (hf : s.frame = some fr)
    (hg : fr.globalDecls = []) (x : String) (v : Value) :
    (s.setVar x v).globals = s.globals := by
  simp [State.setVar, hf, hg]

@[simp] theorem State.lookupName_setVar_self (s : State) (x : String) (v : Value)
    (h : s.plainScope) : (s.setVar x v).lookupName x = some v := by
  cases hf : s.frame with
  | none => simp [State.setVar, State.lookupName, hf]
  | some g => simp [State.setVar, State.lookupName, hf, h g hf]

theorem State.lookupName_setVar_of_ne (s : State) {x y : String} (hxy : x ≠ y)
    (v : Value) (h : s.plainScope) :
    (s.setVar x v).lookupName y = s.lookupName y := by
  cases hf : s.frame with
  | none => simp [State.setVar, State.lookupName, hf, alook_aset_of_ne _ hxy]
  | some g =>
    simp [State.setVar, State.lookupName, hf, h g hf, alook_aset_of_ne _ hxy]

/-- The environment a `def` or `lambda` captures in state `s`: the current
locals, then whatever the enclosing function captured.  See `currentEnv`, which
is this in the monad. -/
def State.defEnv (s : State) : List (String × Value) :=
  match s.frame with
  | Option.none => []
  | some fr => fr.locals ++ fr.captured

/-- Name resolution as it looks from inside a frame that does not shadow `nm`:
the globals, then the builtins.

A call rule needs this because a contract has to survive entering the callee's
frame.  The fresh frame shadows its own parameters and nothing else, so a
contract stated about the globals is still true one frame down. -/
def resolveGlobal (gl : List (String × Value)) (nm : String) : Option Value :=
  match alook gl nm with
  | some v => some v
  | Option.none => builtinValue nm

theorem resolveGlobal_aset_self (gl : List (String × Value)) (k : String) (v : Value) :
    resolveGlobal (aset gl k v) k = some v := by
  simp [resolveGlobal]

theorem resolveGlobal_aset_of_ne (gl : List (String × Value)) {k nm : String} (h : k ≠ nm)
    (v : Value) : resolveGlobal (aset gl k v) nm = resolveGlobal gl nm := by
  simp [resolveGlobal, alook_aset_of_ne _ h]

/-- At module level every name resolves through the globals. -/
theorem State.lookupName_eq_resolveGlobal_of_frame_none {s : State}
    (h : s.frame = Option.none) (nm : String) :
    s.lookupName nm = resolveGlobal s.globals nm := by
  simp [State.lookupName, resolveGlobal, h]

/-- And so does a name a frame does not shadow. -/
theorem State.lookupName_eq_resolveGlobal_of_frame {s : State} {fr : Frame}
    (h : s.frame = some fr) {nm : String}
    (hl : alook fr.locals nm = Option.none) (hc : alook fr.captured nm = Option.none) :
    s.lookupName nm = resolveGlobal s.globals nm := by
  simp [State.lookupName, resolveGlobal, h, hl, hc]

@[simp] theorem State.defEnv_of_frame_none {s : State} (h : s.frame = Option.none) :
    s.defEnv = [] := by
  simp [State.defEnv, h]

theorem State.setVar_globals_of_frame_none {s : State} (h : s.frame = Option.none)
    (x : String) (v : Value) : (s.setVar x v).globals = aset s.globals x v := by
  simp [State.setVar, h]

/-- Read a heap object. -/
def State.get (s : State) (a : Addr) : Option Obj := s.heap[a]?

/-- Overwrite a heap object.  Out-of-range writes are ignored; the interpreter
never produces a dangling reference. -/
def State.setObj (s : State) (a : Addr) (o : Obj) : State :=
  if h : a < s.heap.size then { s with heap := s.heap.set a o h } else s

/-- Allocate a fresh heap object, returning its address. -/
def State.alloc (s : State) (o : Obj) : Addr × State :=
  (s.heap.size, { s with heap := s.heap.push o })

/-! ## The interpreter monad

`M` threads the state, propagates in-flight Python exceptions, and can report
that the fuel ran out.  Exceptions are values so that `except` clauses can
inspect them; `timeout` is not observable from inside the language. -/

/-- The result of running a computation. -/
inductive Res (α : Type) where
  /-- Normal completion. -/
  | ok (a : α) (s : State)
  /-- A Python exception is propagating. -/
  | exn (e : Value) (s : State)
  /-- Out of fuel: the program did not terminate within the given budget.  The
  state is kept so that a caller can still show whatever was printed. -/
  | timeout (s : State)
  deriving Repr, Inhabited, BEq

/-- The interpreter monad: state, plus exceptions, plus running out of fuel. -/
def M (α : Type) : Type := State → Res α

namespace M

/-- `pure`. -/
protected def pure {α} (a : α) : M α := fun s => .ok a s

/-- `bind`, propagating exceptions and timeouts. -/
protected def bind {α β} (m : M α) (f : α → M β) : M β := fun s =>
  match m s with
  | .ok a s' => f a s'
  | .exn e s' => .exn e s'
  | .timeout s' => .timeout s'

instance : Monad M where
  pure := M.pure
  bind := M.bind

@[simp] theorem run_pure {α} (a : α) (s : State) : (Pure.pure a : M α) s = .ok a s := rfl

@[simp] theorem run_bind {α β} (m : M α) (f : α → M β) (s : State) :
    (m >>= f) s = (match m s with
      | .ok a s' => f a s'
      | .exn e s' => .exn e s'
      | .timeout s' => .timeout s') := rfl

/-- The current state. -/
def get : M State := fun s => .ok s s

/-- Replace the state. -/
def set (s' : State) : M Unit := fun _ => .ok () s'

/-- Transform the state. -/
def modify (f : State → State) : M Unit := fun s => .ok () (f s)

/-- Give up: not enough fuel. -/
def timeout {α} : M α := fun s => .timeout s

/-- Raise an already-built exception value. -/
def throwValue {α} (e : Value) : M α := fun s => .exn e s

/-- Raise `ty(msg)`, e.g. `raisePy "TypeError" "unsupported operand"`. -/
def raisePy {α} (ty msg : String) : M α := fun s => .exn (.exc ty [.str msg]) s

/-- Run `m`; if it raises, hand the exception to `h`.  Timeouts are not
catchable. -/
def catchExn {α} (m : M α) (h : Value → M α) : M α := fun s =>
  match m s with
  | .ok a s' => .ok a s'
  | .exn e s' => h e s'
  | .timeout s' => .timeout s'

/-- Run `m` and reify a raised exception as an `Except`, so that `try` can
inspect it.  Timeouts stay unrecoverable. -/
def attempt {α} (m : M α) : M (Except Value α) := fun s =>
  match m s with
  | .ok a s' => .ok (.ok a) s'
  | .exn e s' => .ok (.error e) s'
  | .timeout s' => .timeout s'

/-- Allocate a heap object and return a reference to it. -/
def allocRef (o : Obj) : M Value := fun s =>
  let (a, s') := s.alloc o
  .ok (.ref a) s'

@[simp] theorem run_get (s : State) : get s = .ok s s := rfl
@[simp] theorem run_modify (f : State → State) (s : State) : modify f s = .ok () (f s) := rfl
@[simp] theorem run_timeout {α} (s : State) : (timeout : M α) s = .timeout s := rfl
@[simp] theorem run_throwValue {α} (e : Value) (s : State) :
    (throwValue e : M α) s = .exn e s := rfl
@[simp] theorem run_raisePy {α} (ty msg : String) (s : State) :
    (raisePy ty msg : M α) s = .exn (.exc ty [.str msg]) s := rfl

end M

/-- What a statement does to control flow. -/
inductive Signal where
  /-- Fall through to the next statement. -/
  | normal
  /-- `break`. -/
  | brk
  /-- `continue`. -/
  | cont
  /-- `return v`. -/
  | ret (v : Value)
  deriving Repr, Inhabited, BEq

end SnakeFight
