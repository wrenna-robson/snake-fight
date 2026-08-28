import SnakeFight.Value

/-!
# The pure semantic kernel

The functions in this file implement the parts of Python's semantics that are
*pure*: they read the state (they need the heap to know whether `[]` is falsy,
or what `xs[0]` is) but they never allocate, mutate or print.

Every kernel operation returns `Option KRes`:

* `some (.val v)` -- definitely evaluates to `v`, with no effect on the state;
* `some (.err ty msg)` -- definitely raises `ty(msg)`;
* `none` -- outside the kernel, so the interpreter has to handle it (list
  concatenation allocates, `/` needs floats, a dict key may be unhashable, ...).

`SnakeFight.Interp` calls the kernel first and only falls back to effectful code
when it answers `none`; `SnakeFight.Pure` uses the same functions to give a
state-transformer-free specification of expression evaluation.  Because both
sides share this code, `SnakeFight.Pure.evalP_agrees` -- the theorem that ties
the specification to the interpreter -- goes through by structural induction
with no semantic gap to bridge.
-/

namespace SnakeFight

/-- The outcome of a kernel operation. -/
inductive KRes where
  /-- Produces this value, with no side effect. -/
  | val (v : Value)
  /-- Raises `ty(msg)`. -/
  | err (ty : String) (msg : String)
  /-- Raises `ty(*args)`, for exceptions whose argument is a value rather than
  a message -- `KeyError` carries the key itself. -/
  | errV (ty : String) (args : List Value)
  deriving Repr, Inhabited, BEq

/-! ## Types and truth -/

/-- `bool` coerces to `int` in arithmetic, as in Python. -/
def asInt : Value → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

/-- The name reported by `type(v)`. -/
def Value.typeName (h : Array Obj) : Value → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "str"
  | .tuple _ => "tuple"
  | .func .. => "function"
  | .builtin _ => "builtin_function_or_method"
  | .method .. => "method"
  | .excClass _ => "type"
  | .exc n _ => n
  | .ref a => match h[a]? with
    | some (.list _) => "list"
    | some (.dict _) => "dict"
    | Option.none => "object"

/-- Truth value, as used by `if`, `while`, `and`, `or` and `not`. -/
def Value.truthy (h : Array Obj) : Value → Bool
  | .none => false
  | .bool b => b
  | .int i => i != 0
  | .str s => !s.isEmpty
  | .tuple vs => !vs.isEmpty
  | .ref a => match h[a]? with
    | some (.list xs) => !xs.isEmpty
    | some (.dict kvs) => !kvs.isEmpty
    | Option.none => true
  | _ => true

/-! ## Equality and ordering on immutable values -/

mutual

/-- Is this an immutable value the kernel fully models? -/
def isSimple : Value → Bool
  | .none | .bool _ | .int _ | .str _ => true
  | .tuple vs => isSimpleList vs
  | _ => false

/-- `isSimple` on every element. -/
def isSimpleList : List Value → Bool
  | [] => true
  | v :: vs => isSimple v && isSimpleList vs

end

mutual

/-- Python `==` restricted to immutable values.  Note `1 == True`. -/
def eqCore : Value → Value → Bool
  | .none, .none => true
  | .int x, .int y => x == y
  | .bool x, .bool y => x == y
  | .int x, .bool y => x == (if y then 1 else 0)
  | .bool x, .int y => (if x then 1 else 0) == y
  | .str x, .str y => x == y
  | .tuple xs, .tuple ys => eqCoreList xs ys
  | _, _ => false

/-- Elementwise `eqCore`; tuples of different lengths are unequal. -/
def eqCoreList : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqCore x y && eqCoreList xs ys
  | _, _ => false

end

/-- Lexicographic comparison of strings, by code point, as in Python. -/
def strCmp (x y : String) : Ordering :=
  if x == y then .eq else if x < y then .lt else .gt

mutual

/-- Python `<` and friends, restricted to immutable values.  `none` means the
values are not comparable (Python raises `TypeError`). -/
def cmpCore : Value → Value → Option Ordering
  | .str x, .str y => some (strCmp x y)
  | .tuple xs, .tuple ys => cmpCoreList xs ys
  | a, b => match asInt a, asInt b with
    -- Spelled out rather than via `compare` so that proofs about integer
    -- comparisons reduce with `simp`/`omega` (see `SnakeFight.Reason`).
    | some x, some y => some (if x < y then .lt else if x == y then .eq else .gt)
    | _, _ => Option.none

/-- Lexicographic comparison of tuples. -/
def cmpCoreList : List Value → List Value → Option Ordering
  | [], [] => some .eq
  | [], _ :: _ => some .lt
  | _ :: _, [] => some .gt
  | x :: xs, y :: ys => match cmpCore x y with
    | some .eq => cmpCoreList xs ys
    | some o => some o
    | Option.none => Option.none

end

/-! ## String helpers -/

/-- Is `needle` a prefix of `hay`? -/
def listStartsWith : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => c == d && listStartsWith cs ds

/-- Is `needle` a contiguous sublist of the second argument? -/
def listContainsSub (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | h :: t => listStartsWith needle (h :: t) || listContainsSub needle t

/-- Python's `needle in hay` for strings. -/
def strContains (hay needle : String) : Bool :=
  listContainsSub needle.toList hay.toList

/-- Python's `s * n`. -/
def strRepeat (s : String) (n : Int) : String :=
  if n ≤ 0 then "" else String.join (List.replicate n.toNat s)

/-! ## Arithmetic -/

/-- Bitwise operations are modelled for non-negative operands only. -/
def natBitOp (op : BinOp) (x y : Int) : Option KRes :=
  if x < 0 || y < 0 then Option.none
  else
    let a := x.toNat
    let b := y.toNat
    match op with
    | .band => some (.val (.int (Nat.land a b)))
    | .bor => some (.val (.int (Nat.lor a b)))
    | .bxor => some (.val (.int (Nat.xor a b)))
    | _ => Option.none

/-- `int op int`.  Uses floor division and floor modulus, matching Python:
`-7 // 2 == -4` and `-7 % 2 == 1`. -/
def intBinOpK (op : BinOp) (x y : Int) : Option KRes :=
  match op with
  | .add => some (.val (.int (x + y)))
  | .sub => some (.val (.int (x - y)))
  | .mul => some (.val (.int (x * y)))
  | .floordiv =>
    if y == 0 then some (.err "ZeroDivisionError" "integer division or modulo by zero")
    else some (.val (.int (Int.fdiv x y)))
  | .mod =>
    if y == 0 then some (.err "ZeroDivisionError" "integer division or modulo by zero")
    else some (.val (.int (Int.fmod x y)))
  | .pow =>
    -- A negative exponent produces a float, which SnakeFight does not have.
    if y < 0 then Option.none else some (.val (.int (x ^ y.toNat)))
  | .lshift =>
    if y < 0 then some (.err "ValueError" "negative shift count")
    else some (.val (.int (x * 2 ^ y.toNat)))
  | .rshift =>
    if y < 0 then some (.err "ValueError" "negative shift count")
    else some (.val (.int (Int.fdiv x (2 ^ y.toNat))))
  | .band | .bor | .bxor => natBitOp op x y
  -- True division always yields a float in Python 3.
  | .div => Option.none

/-- The kernel's binary operators. -/
def binOpK (op : BinOp) (a b : Value) : Option KRes :=
  match asInt a, asInt b with
  | some x, some y => intBinOpK op x y
  | _, _ =>
    match op, a, b with
    | .add, .str x, .str y => some (.val (.str (x ++ y)))
    | .add, .tuple x, .tuple y => some (.val (.tuple (x ++ y)))
    | .mul, .str x, v => (asInt v).map fun n => .val (.str (strRepeat x n))
    | .mul, v, .str x => (asInt v).map fun n => .val (.str (strRepeat x n))
    | .mul, .tuple x, v =>
      (asInt v).map fun n =>
        .val (.tuple (List.flatten (List.replicate (if n ≤ 0 then 0 else n.toNat) x)))
    | .mul, v, .tuple x =>
      (asInt v).map fun n =>
        .val (.tuple (List.flatten (List.replicate (if n ≤ 0 then 0 else n.toNat) x)))
    | _, _, _ => Option.none

/-- The kernel's unary operators. -/
def unOpK (h : Array Obj) (op : UnOp) (v : Value) : Option KRes :=
  match op with
  | .not => some (.val (.bool (!v.truthy h)))
  | .neg => (asInt v).map fun x => .val (.int (-x))
  | .pos => (asInt v).map fun x => .val (.int x)
  | .invert => (asInt v).map fun x => .val (.int (-x - 1))

/-- Are these the *same object*?  Modelled only where CPython's answer is
guaranteed: `None` is a singleton, `True`/`False` are singletons, and two
references are identical exactly when they point at the same object.  For ints
and strings CPython's answer depends on interning, so the kernel declines. -/
def isK : Value → Value → Option Bool
  | .none, .none => some true
  | .none, .bool _ | .none, .int _ | .none, .str _ | .none, .tuple _ | .none, .ref _ => some false
  | .bool _, .none | .int _, .none | .str _, .none | .tuple _, .none | .ref _, .none => some false
  | .bool x, .bool y => some (x == y)
  | .ref x, .ref y => some (x == y)
  | .bool _, .ref _ | .ref _, .bool _ => some false
  | _, _ => Option.none

/-- `x in vs` for a tuple, when everything involved is immutable. -/
def memTupleK (x : Value) (vs : List Value) : Option Bool :=
  if isSimple x && isSimpleList vs then some (vs.any (eqCore x)) else Option.none

/-- The kernel's comparisons. -/
def cmpK (op : CmpOp) (a b : Value) : Option KRes :=
  match op with
  | .eq =>
    if isSimple a && isSimple b then some (.val (.bool (eqCore a b)))
    else match a, b with
      | .ref x, .ref y => if x == y then some (.val (.bool true)) else Option.none
      | _, _ => Option.none
  | .ne =>
    if isSimple a && isSimple b then some (.val (.bool (!eqCore a b)))
    else match a, b with
      | .ref x, .ref y => if x == y then some (.val (.bool false)) else Option.none
      | _, _ => Option.none
  | .lt => (cmpCore a b).map fun o => .val (.bool (o == .lt))
  | .le => (cmpCore a b).map fun o => .val (.bool (o != .gt))
  | .gt => (cmpCore a b).map fun o => .val (.bool (o == .gt))
  | .ge => (cmpCore a b).map fun o => .val (.bool (o != .lt))
  | .is => (isK a b).map fun r => .val (.bool r)
  | .isNot => (isK a b).map fun r => .val (.bool (!r))
  | .isIn =>
    match b with
    | .str s => match a with
      | .str n => some (.val (.bool (strContains s n)))
      | _ => Option.none
    | .tuple vs => (memTupleK a vs).map fun r => .val (.bool r)
    | _ => Option.none
  | .notIn =>
    match b with
    | .str s => match a with
      | .str n => some (.val (.bool (!strContains s n)))
      | _ => Option.none
    | .tuple vs => (memTupleK a vs).map fun r => .val (.bool (!r))
    | _ => Option.none

/-! ## Indexing -/

/-- Resolve a possibly-negative index against a sequence of length `n`. -/
def normIndex (i : Int) (n : Nat) : Option Nat :=
  let j := if i < 0 then i + n else i
  if j < 0 || j ≥ (n : Int) then Option.none else some j.toNat

/-- Look up a key in a dict's entry list. -/
def dictLook (entries : List (Value × Value)) (k : Value) : Option Value :=
  match entries with
  | [] => Option.none
  | (k', v) :: rest => if eqCore k k' then some v else dictLook rest k

/-- Insert or overwrite a dict entry, preserving insertion order. -/
def dictSet (entries : List (Value × Value)) (k v : Value) : List (Value × Value) :=
  match entries with
  | [] => [(k, v)]
  | (k', v') :: rest => if eqCore k k' then (k, v) :: rest else (k', v') :: dictSet rest k v

/-- Delete a dict entry. -/
def dictDel (entries : List (Value × Value)) (k : Value) : List (Value × Value) :=
  match entries with
  | [] => []
  | (k', v') :: rest => if eqCore k k' then rest else (k', v') :: dictDel rest k

/-- `obj[idx]` for reads.  Indexing is pure -- it only reads the heap -- so the
kernel models it, which is what lets loop invariants talk about `xs[i]`. -/
def indexK (h : Array Obj) (obj idx : Value) : Option KRes :=
  match obj with
  | .str s =>
    match asInt idx with
    | some i => match normIndex i s.toList.length with
      | some j => match s.toList[j]? with
        | some c => some (.val (.str (String.singleton c)))
        | Option.none => some (.err "IndexError" "string index out of range")
      | Option.none => some (.err "IndexError" "string index out of range")
    | Option.none => Option.none
  | .tuple vs =>
    match asInt idx with
    | some i => match normIndex i vs.length with
      | some j => match vs[j]? with
        | some v => some (.val v)
        | Option.none => some (.err "IndexError" "tuple index out of range")
      | Option.none => some (.err "IndexError" "tuple index out of range")
    | Option.none => Option.none
  | .ref a =>
    match h[a]? with
    | some (.list xs) =>
      match asInt idx with
      | some i => match normIndex i xs.length with
        | some j => match xs[j]? with
          | some v => some (.val v)
          | Option.none => some (.err "IndexError" "list index out of range")
        | Option.none => some (.err "IndexError" "list index out of range")
      | Option.none => Option.none
    | some (.dict kvs) =>
      if isSimple idx then
        match dictLook kvs idx with
        | some v => some (.val v)
        | Option.none => some (.errV "KeyError" [idx])
      else Option.none
    | Option.none => Option.none
  | _ => Option.none

/-! ## Printing

`repr` and `str` recurse through the heap, which can be cyclic
(`a = []; a.append(a)`), so they are fuelled. -/

/-- Escape a string the way Python's `repr` does, including its choice of quote
character: single quotes normally, double quotes if the string contains a single
quote but no double quote. -/
def escapeStr (s : String) : String :=
  let cs := s.toList
  let q : Char := if cs.contains '\'' && !cs.contains '"' then '"' else '\''
  let esc : Char → String := fun c =>
    if c == '\\' then "\\\\"
    else if c == q then String.ofList ['\\', c]
    else if c == '\n' then "\\n"
    else if c == '\t' then "\\t"
    else if c == '\r' then "\\r"
    else String.singleton c
  String.singleton q ++ String.join (cs.map esc) ++ String.singleton q

mutual

/-- Python's `repr`. -/
def pyRepr (fuel : Nat) (h : Array Obj) (v : Value) : String :=
  match fuel with
  | 0 => "..."
  | fuel + 1 =>
    match v with
    | .none => "None"
    | .bool b => if b then "True" else "False"
    | .int i => toString i
    | .str s => escapeStr s
    | .tuple vs =>
      match vs with
      | [] => "()"
      | [x] => "(" ++ pyRepr fuel h x ++ ",)"
      | _ => "(" ++ String.intercalate ", " (pyReprList fuel h vs) ++ ")"
    | .func n .. => "<function " ++ n ++ ">"
    | .builtin n => "<built-in function " ++ n ++ ">"
    | .method _ n => "<bound method " ++ n ++ ">"
    | .excClass n => "<class '" ++ n ++ "'>"
    | .exc n args =>
      match args with
      | [] => n ++ "()"
      | _ => n ++ "(" ++ String.intercalate ", " (pyReprList fuel h args) ++ ")"
    | .ref a =>
      match h[a]? with
      | some (.list xs) => "[" ++ String.intercalate ", " (pyReprList fuel h xs) ++ "]"
      | some (.dict kvs) => "{" ++ String.intercalate ", " (pyReprPairs fuel h kvs) ++ "}"
      | Option.none => "<object>"

/-- `pyRepr` over a list. -/
def pyReprList (fuel : Nat) (h : Array Obj) : List Value → List String
  | [] => []
  | v :: vs => pyRepr fuel h v :: pyReprList fuel h vs

/-- `pyRepr` over dict entries. -/
def pyReprPairs (fuel : Nat) (h : Array Obj) : List (Value × Value) → List String
  | [] => []
  | (k, v) :: rest => (pyRepr fuel h k ++ ": " ++ pyRepr fuel h v) :: pyReprPairs fuel h rest

end

/-- Python's `str`: like `repr`, except that strings print themselves and an
exception prints its message. -/
def pyStr (fuel : Nat) (h : Array Obj) (v : Value) : String :=
  match v with
  | .str s => s
  -- CPython's `KeyError.__str__` is the *repr* of the key, so `str(KeyError('k'))`
  -- is `'k'` rather than `k`.
  | .exc "KeyError" [a] => pyRepr fuel h a
  | .exc _ args =>
    match args with
    | [] => ""
    | [a] => pyStr fuel h a
    | _ => "(" ++ String.intercalate ", " (pyReprList fuel h args) ++ ")"
  | _ => pyRepr fuel h v

/-- How an uncaught exception is reported. -/
def excMessage (fuel : Nat) (h : Array Obj) (v : Value) : String :=
  match v with
  | .exc n args =>
    match args with
    | [] => n
    | _ => n ++ ": " ++ pyStr fuel h v
  | _ => pyStr fuel h v

end SnakeFight
