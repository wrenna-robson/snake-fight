import SnakeFight.Kernel

/-!
# Builtin functions and methods

Builtins never call back into user code -- `sorted` takes no `key=`, and there
is no `map`/`filter` -- so this module does not have to be mutually recursive
with the interpreter.  That keeps `SnakeFight.Interp` small enough to reason
about.
-/

namespace SnakeFight

/-- Depth limit for `repr`/`str`.  Heap structures can be cyclic
(`a = []; a.append(a)`), so printing has to be bounded. -/
def reprFuel : Nat := 64

/-- Depth limit for deep equality and ordering. -/
def cmpFuel : Nat := 64

/-- ASCII whitespace. -/
def isWSChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- `str.strip()`. -/
def strTrim (s : String) : String :=
  String.ofList ((s.toList.dropWhile isWSChar).reverse.dropWhile isWSChar).reverse

/-- Fetch a heap object. -/
def getObj (a : Addr) : M Obj := fun s =>
  match s.get a with
  | some o => .ok o s
  | Option.none => .exn (.exc "RuntimeError" [.str "dangling reference"]) s

/-- The current heap. -/
def getHeap : M (Array Obj) := fun s => .ok s.heap s

/-- `str(v)`, in the monad, so it can read the heap. -/
def strOf (v : Value) : M String := fun s => .ok (pyStr reprFuel s.heap v) s

/-- `repr(v)`. -/
def reprOf (v : Value) : M String := fun s => .ok (pyRepr reprFuel s.heap v) s

/-- Raise `TypeError`. -/
def typeError {α} (msg : String) : M α := M.raisePy "TypeError" msg

/-- The elements of an iterable.  Iterating a dict yields its keys.  This is a
pure read of the heap, so it never allocates. -/
def iterOf (h : Array Obj) (v : Value) : Option (List Value) :=
  match v with
  | .str s => some (s.toList.map fun c => .str (String.singleton c))
  | .tuple vs => some vs
  | .ref a => match h[a]? with
    | some (.list xs) => some xs
    | some (.dict kvs) => some (kvs.map (·.1))
    | Option.none => Option.none
  | _ => Option.none

/-- `iterOf`, raising `TypeError` when the value is not iterable. -/
def iterM (v : Value) : M (List Value) := fun s =>
  match iterOf s.heap v with
  | some xs => .ok xs s
  | Option.none =>
    .exn (.exc "TypeError" [.str s!"'{v.typeName s.heap}' object is not iterable"]) s

/-! ## Deep equality and ordering

The kernel deliberately declines to compare heap objects, so the interpreter
supplies fuelled versions that follow references. -/

mutual

/-- Python `==`, following references. -/
def eqDeep (fuel : Nat) (h : Array Obj) (a b : Value) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if isSimple a && isSimple b then eqCore a b
    else match a, b with
      | .ref x, .ref y =>
        if x == y then true
        else match h[x]?, h[y]? with
          | some (.list xs), some (.list ys) => eqDeepList fuel h xs ys
          | some (.dict xs), some (.dict ys) =>
            xs.length == ys.length &&
              xs.all fun kv => match dictLook ys kv.1 with
                | some v => eqDeep fuel h kv.2 v
                | Option.none => false
          | _, _ => false
      | .tuple xs, .tuple ys => eqDeepList fuel h xs ys
      | .exc n xs, .exc m ys => n == m && eqDeepList fuel h xs ys
      | .builtin x, .builtin y => x == y
      | .excClass x, .excClass y => x == y
      | _, _ => false

/-- Elementwise `eqDeep`. -/
def eqDeepList (fuel : Nat) (h : Array Obj) : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqDeep fuel h x y && eqDeepList fuel h xs ys
  | _, _ => false

end

mutual

/-- Python ordering, following references.  `none` means `TypeError`. -/
def cmpDeep (fuel : Nat) (h : Array Obj) (a b : Value) : Option Ordering :=
  match fuel with
  | 0 => Option.none
  | fuel + 1 =>
    match cmpCore a b with
    | some o => some o
    | Option.none =>
      match a, b with
      | .ref x, .ref y => match h[x]?, h[y]? with
        | some (.list xs), some (.list ys) => cmpDeepList fuel h xs ys
        | _, _ => Option.none
      | .tuple xs, .tuple ys => cmpDeepList fuel h xs ys
      | _, _ => Option.none

/-- Lexicographic `cmpDeep`. -/
def cmpDeepList (fuel : Nat) (h : Array Obj) : List Value → List Value → Option Ordering
  | [], [] => some .eq
  | [], _ :: _ => some .lt
  | _ :: _, [] => some .gt
  | x :: xs, y :: ys => match cmpDeep fuel h x y with
    | some .eq => cmpDeepList fuel h xs ys
    | some o => some o
    | Option.none => Option.none

end

/-- Insertion sort using Python's ordering.  `none` on incomparable elements. -/
def sortValues (h : Array Obj) (xs : List Value) : Option (List Value) :=
  xs.foldlM (init := []) fun acc x => insert acc x
where
  insert : List Value → Value → Option (List Value)
    | [], x => some [x]
    | y :: ys, x => match cmpDeep cmpFuel h x y with
      | some .lt | some .eq => some (x :: y :: ys)
      | some .gt => (insert ys x).map (y :: ·)
      | Option.none => Option.none

/-! ## Builtin functions -/

/-- `int(v)`. -/
def toIntV (v : Value) : M Value :=
  match v with
  | .int i => pure (.int i)
  | .bool b => pure (.int (if b then 1 else 0))
  | .str s =>
    let t := strTrim s
    let (neg, digits) := match t.toList with
      | '-' :: rest => (true, rest)
      | '+' :: rest => (false, rest)
      | rest => (false, rest)
    if digits.isEmpty || !digits.all Char.isDigit then
      M.raisePy "ValueError" s!"invalid literal for int() with base 10: '{s}'"
    else
      let n : Int := (String.ofList digits).toNat!
      pure (.int (if neg then -n else n))
  | _ => typeError "int() argument must be a string or a number"

/-- `min`/`max` over a list of values. -/
def extremum (isMax : Bool) (name : String) (vs : List Value) : M Value := fun s =>
  match vs with
  | [] => .exn (.exc "ValueError" [.str s!"{name}() arg is an empty sequence"]) s
  | v :: rest =>
    let step : Option Value → Value → Option Value := fun acc x =>
      match acc with
      | Option.none => Option.none
      | some best => match cmpDeep cmpFuel s.heap x best with
        | some o => some (if (if isMax then o == .gt else o == .lt) then x else best)
        | Option.none => Option.none
    match rest.foldl step (some v) with
    | some r => .ok r s
    | Option.none => .exn (.exc "TypeError" [.str s!"'{name}()' arguments are not comparable"]) s

/-- `range(...)` as an explicit list of ints.

SnakeFight materializes ranges instead of modelling a lazy iterator, so
`range(10**9)` is not usable; every other use behaves like Python's. -/
def rangeList (start stop step : Int) : List Value :=
  let n : Int :=
    if step > 0 then (stop - start + step - 1) / step
    else if step < 0 then (start - stop + (-step) - 1) / (-step)
    else 0
  let count := if n ≤ 0 then 0 else n.toNat
  (List.range count).map fun (i : Nat) => Value.int (start + step * (i : Int))

/-- Is `name` one of the builtin type constructors that `isinstance` accepts? -/
def typeishName : String → Bool
  | "int" | "str" | "bool" | "list" | "dict" | "tuple" => true
  | _ => false

/-- `isinstance(v, cls)`. -/
def isinstanceV (h : Array Obj) (v cls : Value) : Option Bool :=
  let clsName := match cls with
    | .builtin n => if typeishName n then some n else Option.none
    | .excClass n => some n
    | _ => Option.none
  match clsName with
  | Option.none => Option.none
  | some n =>
    let tn := v.typeName h
    if tn == n then some true
    -- `bool` is a subclass of `int`, and exception classes have a hierarchy.
    else if n == "int" && tn == "bool" then some true
    else if isExcName n then some (match v with
      | .exc en _ => excIsSubclass en n
      | _ => false)
    else some false

/-- Call a builtin function with positional arguments. -/
def callBuiltinPos (name : String) (args : List Value) : M Value := do
  match name, args with
  | "print", vs => do
    let parts ← vs.mapM strOf
    M.modify fun s => { s with out := String.intercalate " " parts :: s.out }
    pure .none
  | "len", [v] => do
    let h ← getHeap
    match v with
    | .str x => pure (.int x.toList.length)
    | .tuple xs => pure (.int xs.length)
    | .ref a => match h[a]? with
      | some (.list xs) => pure (.int xs.length)
      | some (.dict kvs) => pure (.int kvs.length)
      | Option.none => typeError "dangling reference"
    | _ => typeError s!"object of type '{v.typeName h}' has no len()"
  | "range", [a] => do
    let some x := asInt a | typeError "range() argument must be an integer"
    M.allocRef (.list (rangeList 0 x 1))
  | "range", [a, b] => do
    let some x := asInt a | typeError "range() argument must be an integer"
    let some y := asInt b | typeError "range() argument must be an integer"
    M.allocRef (.list (rangeList x y 1))
  | "range", [a, b, c] => do
    let some x := asInt a | typeError "range() argument must be an integer"
    let some y := asInt b | typeError "range() argument must be an integer"
    let some z := asInt c | typeError "range() argument must be an integer"
    if z == 0 then M.raisePy "ValueError" "range() arg 3 must not be zero"
    else M.allocRef (.list (rangeList x y z))
  | "str", [v] => do let s ← strOf v; pure (.str s)
  | "str", [] => pure (.str "")
  | "repr", [v] => do let s ← reprOf v; pure (.str s)
  | "int", [v] => toIntV v
  | "int", [] => pure (.int 0)
  | "bool", [v] => do let h ← getHeap; pure (.bool (v.truthy h))
  | "bool", [] => pure (.bool false)
  | "abs", [v] => do
    let some x := asInt v | typeError "bad operand type for abs()"
    pure (.int (if x < 0 then -x else x))
  | "min", vs => do
    let items ← if vs.length == 1 then iterM vs[0]! else pure vs
    extremum false "min" items
  | "max", vs => do
    let items ← if vs.length == 1 then iterM vs[0]! else pure vs
    extremum true "max" items
  | "sum", (v :: rest) => do
    let items ← iterM v
    let start : Value := rest.headD (.int 0)
    let some z := asInt start | typeError "sum() start must be a number"
    items.foldlM (init := Value.int z) fun acc x => do
      let some a := asInt acc | typeError "unsupported operand type(s) for +"
      let some b := asInt x | typeError "unsupported operand type(s) for +"
      pure (.int (a + b))
  | "sorted", [v] => do
    let items ← iterM v
    let h ← getHeap
    match sortValues h items with
    | some xs => M.allocRef (.list xs)
    | Option.none => typeError "elements are not comparable"
  | "list", [] => M.allocRef (.list [])
  | "list", [v] => do let items ← iterM v; M.allocRef (.list items)
  | "tuple", [] => pure (.tuple [])
  | "tuple", [v] => do let items ← iterM v; pure (.tuple items)
  | "dict", [] => M.allocRef (.dict [])
  | "dict", [v] => do
    let items ← iterM v
    let entries ← items.mapM fun it => match it with
      | .tuple [k, x] => pure (k, x)
      | _ => typeError "dict() expects an iterable of key/value pairs"
    M.allocRef (.dict (entries.foldl (fun acc kv => dictSet acc kv.1 kv.2) []))
  | "reversed", [v] => do let items ← iterM v; M.allocRef (.list items.reverse)
  | "enumerate", [v] => do
    let items ← iterM v
    M.allocRef (.list ((items.zipIdx).map fun (x, i) => .tuple [.int i, x]))
  | "zip", vs => do
    let lists ← vs.mapM iterM
    let n := lists.foldl (fun acc l => min acc l.length) (lists.foldl (fun a l => max a l.length) 0)
    let rows := (List.range n).map fun i => Value.tuple (lists.map fun l => l[i]!)
    M.allocRef (.list rows)
  | "isinstance", [v, c] => do
    let h ← getHeap
    match isinstanceV h v c with
    | some b => pure (.bool b)
    | Option.none => typeError "isinstance() arg 2 must be a type"
  | "type", [v] => do let h ← getHeap; pure (.excClass (v.typeName h))
  | "ord", [v] => do
    match v with
    | .str s => match s.toList with
      | [c] => pure (.int c.toNat)
      | _ => typeError "ord() expected a character"
    | _ => typeError "ord() expected a string"
  | "chr", [v] => do
    let some x := asInt v | typeError "chr() expected an integer"
    if x < 0 || x > 0x10FFFF then M.raisePy "ValueError" "chr() arg not in range"
    else pure (.str (String.singleton (Char.ofNat x.toNat)))
  | "divmod", [a, b] => do
    let some x := asInt a | typeError "unsupported operand type(s) for divmod()"
    let some y := asInt b | typeError "unsupported operand type(s) for divmod()"
    if y == 0 then M.raisePy "ZeroDivisionError" "integer division or modulo by zero"
    else pure (.tuple [.int (Int.fdiv x y), .int (Int.fmod x y)])
  | "any", [v] => do
    let items ← iterM v
    let h ← getHeap
    pure (.bool (items.any fun x => x.truthy h))
  | "all", [v] => do
    let items ← iterM v
    let h ← getHeap
    pure (.bool (items.all fun x => x.truthy h))
  | "id", [v] => pure (.int (match v with | .ref a => a | _ => 0))
  | _, _ => typeError s!"{name}() got {args.length} argument(s), which is not supported"

/-- Call a builtin function.  No builtin takes keyword arguments. -/
def callBuiltin (name : String) (args : List Value) (kwargs : List (String × Value)) :
    M Value :=
  if kwargs.isEmpty then callBuiltinPos name args
  else typeError s!"{name}() takes no keyword arguments"

/-! ## Methods -/

/-- Split a string on a separator. -/
def strSplitOn (s sep : String) : List String :=
  if sep.isEmpty then [s] else s.splitOn sep

/-- Worker for `strSplitWS`; `cur` is the current word, reversed. -/
def splitWSGo : List Char → List Char → List String
  | [], cur => if cur.isEmpty then [] else [String.ofList cur.reverse]
  | c :: cs, cur =>
    if isWSChar c then
      if cur.isEmpty then splitWSGo cs [] else String.ofList cur.reverse :: splitWSGo cs []
    else splitWSGo cs (c :: cur)

/-- `str.split()` with no argument splits on runs of whitespace. -/
def strSplitWS (s : String) : List String := splitWSGo s.toList []

/-- Remove the first element equal to `v`. -/
def listRemoveFirst (h : Array Obj) (v : Value) : List Value → Option (List Value)
  | [] => Option.none
  | x :: xs =>
    if eqDeep cmpFuel h x v then some xs else (listRemoveFirst h v xs).map (x :: ·)

/-- Index of the first element equal to `v`. -/
def listIndexOf (h : Array Obj) (v : Value) : List Value → Nat → Option Nat
  | [], _ => Option.none
  | x :: xs, i => if eqDeep cmpFuel h x v then some i else listIndexOf h v xs (i + 1)

/-- Index of the first occurrence of `needle`, or `-1`. -/
def strFind (hay needle : String) : Int :=
  go hay.toList needle.toList 0
where
  go : List Char → List Char → Int → Int
    | cs, n, i => if listStartsWith n cs then i else match cs with
      | [] => -1
      | _ :: t => go t n (i + 1)

/-- `str.replace`. -/
def strReplace (s old new : String) : String :=
  if old.isEmpty then s else String.intercalate new (s.splitOn old)

/-- Call a method on a string. -/
def strMethod (s : String) (name : String) (args : List Value) : M Value := do
  match name, args with
  | "upper", [] => pure (.str (String.ofList (s.toList.map Char.toUpper)))
  | "lower", [] => pure (.str (String.ofList (s.toList.map Char.toLower)))
  | "strip", [] => pure (.str (strTrim s))
  | "split", [] => do
    let parts := strSplitWS s
    M.allocRef (.list (parts.map (Value.str ·)))
  | "split", [.str sep] => M.allocRef (.list ((strSplitOn s sep).map (Value.str ·)))
  | "join", [v] => do
    let items ← iterM v
    let parts ← items.mapM fun x => match x with
      | .str t => pure t
      | _ => typeError "sequence item: expected str"
    pure (.str (String.intercalate s parts))
  | "startswith", [.str p] => pure (.bool (listStartsWith p.toList s.toList))
  | "endswith", [.str p] => pure (.bool (listStartsWith p.toList.reverse s.toList.reverse))
  | "replace", [.str a, .str b] => pure (.str (strReplace s a b))
  | "find", [.str n] => pure (.int (strFind s n))
  | "count", [.str n] => pure (.int (if n.isEmpty then 0 else (s.splitOn n).length - 1))
  | "isdigit", [] => pure (.bool (!s.isEmpty && s.toList.all Char.isDigit))
  | "isalpha", [] => pure (.bool (!s.isEmpty && s.toList.all Char.isAlpha))
  | _, _ => M.raisePy "AttributeError" s!"'str' object has no attribute '{name}'"

/-- Call a method on a list living at address `a`. -/
def listMethod (a : Addr) (items : List Value) (name : String) (args : List Value) :
    M Value := do
  let store (xs : List Value) : M Unit := M.modify fun s => s.setObj a (.list xs)
  match name, args with
  | "append", [v] => do store (items ++ [v]); pure .none
  | "extend", [v] => do let more ← iterM v; store (items ++ more); pure .none
  | "insert", [i, v] => do
    let some n := asInt i | typeError "insert() index must be an integer"
    let k := if n < 0 then (if n + items.length < 0 then 0 else (n + items.length).toNat)
             else min n.toNat items.length
    store (items.take k ++ [v] ++ items.drop k)
    pure .none
  | "pop", [] =>
    match items.reverse with
    | [] => M.raisePy "IndexError" "pop from empty list"
    | last :: revInit => do store revInit.reverse; pure last
  | "pop", [i] => do
    let some n := asInt i | typeError "pop() index must be an integer"
    match normIndex n items.length with
    | Option.none => M.raisePy "IndexError" "pop index out of range"
    | some k => do
      let some v := items[k]? | M.raisePy "IndexError" "pop index out of range"
      store (items.take k ++ items.drop (k + 1))
      pure v
  | "remove", [v] => do
    let h ← getHeap
    match listRemoveFirst h v items with
    | some xs => do store xs; pure .none
    | Option.none => M.raisePy "ValueError" "list.remove(x): x not in list"
  | "index", [v] => do
    let h ← getHeap
    match listIndexOf h v items 0 with
    | some i => pure (.int i)
    | Option.none => M.raisePy "ValueError" "value is not in list"
  | "count", [v] => do
    let h ← getHeap
    pure (.int ((items.filter fun x => eqDeep cmpFuel h x v).length))
  | "clear", [] => do store []; pure .none
  | "reverse", [] => do store items.reverse; pure .none
  | "sort", [] => do
    let h ← getHeap
    match sortValues h items with
    | some xs => do store xs; pure .none
    | Option.none => typeError "elements are not comparable"
  | "copy", [] => M.allocRef (.list items)
  | _, _ => M.raisePy "AttributeError" s!"'list' object has no attribute '{name}'"

/-- Call a method on a dict living at address `a`. -/
def dictMethod (a : Addr) (entries : List (Value × Value)) (name : String)
    (args : List Value) : M Value := do
  let store (kvs : List (Value × Value)) : M Unit := M.modify fun s => s.setObj a (.dict kvs)
  match name, args with
  | "keys", [] => M.allocRef (.list (entries.map (·.1)))
  | "values", [] => M.allocRef (.list (entries.map (·.2)))
  | "items", [] => M.allocRef (.list (entries.map fun kv => .tuple [kv.1, kv.2]))
  | "get", [k] => pure ((dictLook entries k).getD .none)
  | "get", [k, d] => pure ((dictLook entries k).getD d)
  | "pop", [k] =>
    match dictLook entries k with
    | some v => do store (dictDel entries k); pure v
    | Option.none => M.throwValue (.exc "KeyError" [k])
  | "pop", [k, d] =>
    match dictLook entries k with
    | some v => do store (dictDel entries k); pure v
    | Option.none => pure d
  | "setdefault", [k, d] =>
    match dictLook entries k with
    | some v => pure v
    | Option.none => do store (dictSet entries k d); pure d
  | "update", [v] => do
    let items ← iterM v
    -- `d.update(other)` where `other` is a dict, or an iterable of pairs.
    let pairs ← match v with
      | .ref b => do
        let o ← getObj b
        match o with
        | .dict kvs => pure kvs
        | .list _ => items.mapM fun it => match it with
          | .tuple [k, x] => pure (k, x)
          | _ => typeError "update() expects key/value pairs"
      | _ => items.mapM fun it => match it with
        | .tuple [k, x] => pure (k, x)
        | _ => typeError "update() expects key/value pairs"
    store (pairs.foldl (fun acc kv => dictSet acc kv.1 kv.2) entries)
    pure .none
  | "clear", [] => do store []; pure .none
  | "copy", [] => M.allocRef (.dict entries)
  | _, _ => M.raisePy "AttributeError" s!"'dict' object has no attribute '{name}'"

/-- Dispatch a method call on any value. -/
def callMethodV (recv : Value) (name : String) (args : List Value) : M Value := do
  match recv with
  | .str s => strMethod s name args
  | .ref a => do
    let o ← getObj a
    match o with
    | .list items => listMethod a items name args
    | .dict entries => dictMethod a entries name args
  | .exc _ eargs =>
    match name, args with
    | "args", [] => pure (.tuple eargs)
    | _, _ => M.raisePy "AttributeError" s!"exception has no attribute '{name}'"
  | _ => do
    let h ← getHeap
    M.raisePy "AttributeError" s!"'{recv.typeName h}' object has no attribute '{name}'"

end SnakeFight
