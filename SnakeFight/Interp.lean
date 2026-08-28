import SnakeFight.Builtins
import SnakeFight.Parser

/-!
# The interpreter

`execBlock` is a total function `Nat → Block → State → Res Signal`: given a fuel
budget it either finishes, raises a Python exception, or reports that it ran out
of fuel.  Nothing here is `partial`, so the whole thing can be unfolded inside a
proof, and `SnakeFight.Hoare` does exactly that.

Fuel is spent uniformly: every function in the mutual block below matches on
`fuel + 1` and passes `fuel` to its callees, so termination is structural in the
first argument.  One consequence is that fuel counts evaluation *steps* (AST
nodes visited, loop iterations, calls), so budgets are generous by default.

Effectful operations are ordered exactly as in CPython -- left operand before
right, arguments left to right, target expressions before the assigned value --
because the monad threads the state through in that order.
-/

namespace SnakeFight

/-- The environment a `def` or `lambda` captures: the current locals, then the
variables the enclosing function captured.  Locals come first so that they
shadow.

This copies the values, so a nested function does not see later rebindings of an
enclosing local -- the one place where SnakeFight knowingly diverges from
CPython, which captures the variable itself.  Matching it would mean giving
frames identity by allocating them in the heap.  At module level there is no
divergence: there is no frame, so globals are looked up late. -/
def currentEnv : M (List (String × Value)) := fun s =>
  match s.frame with
  | Option.none => .ok [] s
  | some fr => .ok (fr.locals ++ fr.captured) s

/-- Look up a name, raising `NameError` if it is unbound. -/
def lookupOrRaise (x : String) : M Value := fun s =>
  match s.lookupName x with
  | some v => .ok v s
  | Option.none => .exn (.exc "NameError" [.str s!"name '{x}' is not defined"]) s

/-- Turn a kernel answer into a monadic action. -/
def ofKRes (k : KRes) : M Value :=
  match k with
  | .val v => pure v
  | .err ty msg => M.raisePy ty msg
  | .errV ty args => M.throwValue (.exc ty args)

/-- Binary operators.  The kernel handles the arithmetic; the cases left over
either allocate (list concatenation) or are type errors. -/
def applyBinOp (op : BinOp) (a b : Value) : M Value := do
  match binOpK op a b with
  | some k => ofKRes k
  | Option.none => do
    let h ← getHeap
    let fail : M Value := match op with
      | .div => typeError
          s!"unsupported operand type(s) for /: '{a.typeName h}' and '{b.typeName h}' \
             (SnakeFight has no floats; use //)"
      | _ => typeError
          s!"unsupported operand type(s) for {op.symbol}: '{a.typeName h}' and '{b.typeName h}'"
    match op, a, b with
    | .add, .ref x, .ref y =>
      match h[x]?, h[y]? with
      | some (.list xs), some (.list ys) => M.allocRef (.list (xs ++ ys))
      | _, _ => fail
    | .mul, .ref x, n =>
      match h[x]?, asInt n with
      | some (.list xs), some k =>
        M.allocRef (.list (List.flatten (List.replicate (if k ≤ 0 then 0 else k.toNat) xs)))
      | _, _ => fail
    | .mul, n, .ref x =>
      match h[x]?, asInt n with
      | some (.list xs), some k =>
        M.allocRef (.list (List.flatten (List.replicate (if k ≤ 0 then 0 else k.toNat) xs)))
      | _, _ => fail
    | _, _, _ => fail

/-- Comparisons.  Again the kernel first, then the cases that have to follow
references. -/
def applyCmp (op : CmpOp) (a b : Value) : M Value := do
  match cmpK op a b with
  | some k => ofKRes k
  | Option.none => do
    let h ← getHeap
    match op with
    | .eq => pure (.bool (eqDeep cmpFuel h a b))
    | .ne => pure (.bool (!eqDeep cmpFuel h a b))
    | .is => pure (.bool (a == b))
    | .isNot => pure (.bool (!(a == b)))
    | .isIn | .notIn =>
      match iterOf h b with
      | some items =>
        let found := items.any fun x => eqDeep cmpFuel h x a
        pure (.bool (if op == CmpOp.isIn then found else !found))
      | Option.none => typeError s!"argument of type '{b.typeName h}' is not iterable"
    | _ =>
      match cmpDeep cmpFuel h a b with
      | some o =>
        pure (.bool (match op with
          | .lt => o == .lt
          | .le => o != .gt
          | .gt => o == .gt
          | _ => o != .lt))
      | Option.none =>
        typeError
          s!"'{op.symbol}' not supported between instances of '{a.typeName h}' and '{b.typeName h}'"

/-- Resolve the bounds of `obj[lo:hi]` the way Python does: negative values
count from the end, and everything is clamped to the sequence. -/
def sliceBounds (lo hi : Option Int) (n : Nat) : Nat × Nat :=
  let norm : Int → Nat := fun i =>
    let j := if i < 0 then i + n else i
    if j < 0 then 0 else if j > (n : Int) then n else j.toNat
  let a := match lo with | some i => norm i | Option.none => 0
  let b := match hi with | some i => norm i | Option.none => n
  (a, if b < a then a else b)

/-- `obj[lo:hi]`. -/
def applySlice (obj : Value) (lo hi : Option Value) : M Value := do
  let toIdx : Option Value → M (Option Int) := fun ov =>
    match ov with
    | Option.none => pure Option.none
    | some v => match asInt v with
      | some i => pure (some i)
      | Option.none => typeError "slice indices must be integers"
  let lo' ← toIdx lo
  let hi' ← toIdx hi
  let h ← getHeap
  match obj with
  | .str s =>
    let cs := s.toList
    let (a, b) := sliceBounds lo' hi' cs.length
    pure (.str (String.ofList ((cs.take b).drop a)))
  | .tuple vs =>
    let (a, b) := sliceBounds lo' hi' vs.length
    pure (.tuple ((vs.take b).drop a))
  | .ref r =>
    match h[r]? with
    | some (.list xs) =>
      let (a, b) := sliceBounds lo' hi' xs.length
      M.allocRef (.list ((xs.take b).drop a))
    | _ => typeError s!"'{obj.typeName h}' object is not subscriptable"
  | _ => typeError s!"'{obj.typeName h}' object is not subscriptable"

/-- `obj[idx] = v`. -/
def setIndex (obj idx v : Value) : M Unit := do
  let h ← getHeap
  match obj with
  | .ref a =>
    match h[a]? with
    | some (.list xs) =>
      match asInt idx with
      | some i =>
        match normIndex i xs.length with
        | some j => M.modify fun s => s.setObj a (.list (xs.set j v))
        | Option.none => M.raisePy "IndexError" "list assignment index out of range"
      | Option.none => typeError "list indices must be integers"
    | some (.dict kvs) =>
      if isSimple idx then M.modify fun s => s.setObj a (.dict (dictSet kvs idx v))
      else typeError s!"unhashable type: '{idx.typeName h}'"
    | Option.none => typeError "dangling reference"
  | _ => typeError s!"'{obj.typeName h}' object does not support item assignment"

/-- `del obj[idx]`. -/
def delIndex (obj idx : Value) : M Unit := do
  let h ← getHeap
  match obj with
  | .ref a =>
    match h[a]? with
    | some (.list xs) =>
      match asInt idx with
      | some i =>
        match normIndex i xs.length with
        | some j => M.modify fun s => s.setObj a (.list (xs.take j ++ xs.drop (j + 1)))
        | Option.none => M.raisePy "IndexError" "list assignment index out of range"
      | Option.none => typeError "list indices must be integers"
    | some (.dict kvs) =>
      match dictLook kvs idx with
      | some _ => M.modify fun s => s.setObj a (.dict (dictDel kvs idx))
      | Option.none => M.throwValue (.exc "KeyError" [idx])
    | Option.none => typeError "dangling reference"
  | _ => typeError s!"'{obj.typeName h}' object does not support item deletion"

mutual

/-- Does exception value `e` match the `except` clause value `tv`?  `tv` may be
a single exception class or a tuple of them. -/
def excMatches (e : Value) (tv : Value) : Bool :=
  match tv with
  | .excClass n => match e with
    | .exc en _ => excIsSubclass en n
    | _ => false
  | .tuple ts => excMatchesAny e ts
  | _ => false

/-- Does `e` match any of these `except` clause values? -/
def excMatchesAny (e : Value) : List Value → Bool
  | [] => false
  | t :: ts => excMatches e t || excMatchesAny e ts

end

/-- Bind call arguments to parameter names.

`defaults` supplies the last parameters, as in Python; keyword arguments may
fill in any parameter. -/
def bindParams (fname : String) (params : List String) (defaults : List Value)
    (args : List Value) (kwargs : List (String × Value)) :
    M (List (String × Value)) := do
  if args.length > params.length then
    typeError s!"{fname}() takes {params.length} positional argument(s) but {args.length} were given"
  else
    let nreq := params.length - defaults.length
    -- Walk the parameters in order, preferring positional, then keyword, then default.
    let rec go (i : Nat) (ps : List String) (acc : List (String × Value)) :
        M (List (String × Value)) :=
      match ps with
      | [] => pure acc
      | p :: rest =>
        match args[i]? with
        | some v => go (i + 1) rest (aset acc p v)
        | Option.none =>
          match kwargs.find? (fun kv => kv.1 == p) with
          | some (_, v) => go (i + 1) rest (aset acc p v)
          | Option.none =>
            if i ≥ nreq then
              match defaults[i - nreq]? with
              | some d => go (i + 1) rest (aset acc p d)
              | Option.none => typeError s!"{fname}() missing required argument: '{p}'"
            else typeError s!"{fname}() missing required argument: '{p}'"
    let locals ← go 0 params []
    -- Reject keyword arguments that do not name a parameter.
    match kwargs.find? (fun kv => !params.contains kv.1) with
    | some (k, _) => typeError s!"{fname}() got an unexpected keyword argument '{k}'"
    | Option.none => pure locals

mutual

/-- Evaluate an expression. -/
def evalExpr : Nat → Expr → M Value
  | 0, _ => M.timeout
  | fuel + 1, e =>
    match e with
    | .int i => pure (.int i)
    | .str s => pure (.str s)
    | .bool b => pure (.bool b)
    | .none => pure .none
    | .name x => lookupOrRaise x
    | .unop op e => do
      let v ← evalExpr fuel e
      let h ← getHeap
      match unOpK h op v with
      | some k => ofKRes k
      | Option.none => typeError s!"bad operand type for unary {op.symbol}: '{v.typeName h}'"
    | .binop op l r => do
      let a ← evalExpr fuel l
      let b ← evalExpr fuel r
      applyBinOp op a b
    | .compare l rest => do
      let a ← evalExpr fuel l
      evalCmpChain fuel a rest
    | .andE l r => do
      let a ← evalExpr fuel l
      let h ← getHeap
      if a.truthy h then evalExpr fuel r else pure a
    | .orE l r => do
      let a ← evalExpr fuel l
      let h ← getHeap
      if a.truthy h then pure a else evalExpr fuel r
    | .ifE c t f => do
      let cv ← evalExpr fuel c
      let h ← getHeap
      if cv.truthy h then evalExpr fuel t else evalExpr fuel f
    | .call fe args kwargs =>
      match fe with
      | .attr obj name => do
        -- Method call: the receiver is evaluated once.
        let recv ← evalExpr fuel obj
        let avs ← evalExprs fuel args
        if kwargs.isEmpty then callMethodV recv name avs
        else typeError "methods do not accept keyword arguments"
      | _ => do
        let fv ← evalExpr fuel fe
        let avs ← evalExprs fuel args
        let kvs ← evalKwargs fuel kwargs
        callValue fuel fv avs kvs
    | .listE es => do
      let vs ← evalExprs fuel es
      M.allocRef (.list vs)
    | .tupleE es => do
      let vs ← evalExprs fuel es
      pure (.tuple vs)
    | .dictE kvs => do
      let pairs ← evalDictItems fuel kvs
      -- Later duplicate keys overwrite earlier ones but keep the first
      -- position, which is what folding `dictSet` from the left does.
      M.allocRef (.dict (pairs.foldl (fun acc kv => dictSet acc kv.1 kv.2) []))
    | .subscript o i => do
      let ov ← evalExpr fuel o
      let iv ← evalExpr fuel i
      let h ← getHeap
      match indexK h ov iv with
      | some k => ofKRes k
      | Option.none =>
        match ov with
        | .ref a =>
          match h[a]? with
          | some (.dict _) => typeError s!"unhashable type: '{iv.typeName h}'"
          | _ => typeError s!"'{ov.typeName h}' indices must be integers"
        | _ => typeError s!"'{ov.typeName h}' object is not subscriptable"
    | .slice o lo hi => do
      let ov ← evalExpr fuel o
      let lov ← evalOptExpr fuel lo
      let hiv ← evalOptExpr fuel hi
      applySlice ov lov hiv
    | .attr o field => do
      let ov ← evalExpr fuel o
      match ov, field with
      | .exc _ args, "args" => pure (.tuple args)
      | _, _ => pure (.method ov field)
    | .lam params body => do
      let defaults ← evalDefaults fuel params
      let env ← currentEnv
      pure (.func "<lambda>" (params.map (·.1)) defaults [.ret (some body)] env)
    | .listComp elem tgt iter cond => do
      let itv ← evalExpr fuel iter
      let items ← iterM itv
      let vs ← evalComp fuel elem tgt items cond
      M.allocRef (.list vs)

/-- Evaluate expressions left to right. -/
def evalExprs : Nat → List Expr → M (List Value)
  | _, [] => pure []
  | 0, _ => M.timeout
  | fuel + 1, e :: es => do
    let v ← evalExpr fuel e
    let vs ← evalExprs fuel es
    pure (v :: vs)

/-- Evaluate an optional expression. -/
def evalOptExpr : Nat → Option Expr → M (Option Value)
  | _, Option.none => pure Option.none
  | 0, _ => M.timeout
  | fuel + 1, some e => do
    let v ← evalExpr fuel e
    pure (some v)

/-- Evaluate keyword arguments left to right. -/
def evalKwargs : Nat → List (String × Expr) → M (List (String × Value))
  | _, [] => pure []
  | 0, _ => M.timeout
  | fuel + 1, (k, e) :: rest => do
    let v ← evalExpr fuel e
    let vs ← evalKwargs fuel rest
    pure ((k, v) :: vs)

/-- Evaluate the items of a dict display in source order, rejecting unhashable
keys. -/
def evalDictItems : Nat → List (Expr × Expr) → M (List (Value × Value))
  | _, [] => pure []
  | 0, _ => M.timeout
  | fuel + 1, (ke, ve) :: rest => do
    let k ← evalExpr fuel ke
    let v ← evalExpr fuel ve
    if !isSimple k then do
      let h ← getHeap
      typeError s!"unhashable type: '{k.typeName h}'"
    else do
      let others ← evalDictItems fuel rest
      pure ((k, v) :: others)

/-- The tail of a chained comparison.  Each operand is evaluated at most once,
and evaluation stops at the first false comparison. -/
def evalCmpChain : Nat → Value → List (CmpOp × Expr) → M Value
  | _, _, [] => pure (.bool true)
  | 0, _, _ => M.timeout
  | fuel + 1, prev, (op, e) :: rest => do
    let cur ← evalExpr fuel e
    let r ← applyCmp op prev cur
    let h ← getHeap
    if r.truthy h then
      match rest with
      | [] => pure r
      | _ => evalCmpChain fuel cur rest
    else pure (.bool false)

/-- The elements of a list comprehension. -/
def evalComp : Nat → Expr → Target → List Value → Option Expr → M (List Value)
  | _, _, _, [], _ => pure []
  | 0, _, _, _, _ => M.timeout
  | fuel + 1, elem, tgt, v :: rest, cond => do
    bindTarget fuel tgt v
    let keep ← match cond with
      | Option.none => pure true
      | some c => do
        let cv ← evalExpr fuel c
        let h ← getHeap
        pure (cv.truthy h)
    if keep then do
      let x ← evalExpr fuel elem
      let xs ← evalComp fuel elem tgt rest cond
      pure (x :: xs)
    else evalComp fuel elem tgt rest cond

/-- Call a value. -/
def callValue : Nat → Value → List Value → List (String × Value) → M Value
  | 0, _, _, _ => M.timeout
  | fuel + 1, fv, args, kwargs =>
    match fv with
    | .builtin n => callBuiltin n args kwargs
    | .method recv n =>
      if kwargs.isEmpty then callMethodV recv n args
      else typeError "methods do not accept keyword arguments"
    | .excClass n =>
      if isExcName n then pure (.exc n args)
      else typeError s!"'{n}' object is not callable"
    | .func name params defaults body env => do
      let locals ← bindParams name params defaults args kwargs
      let caller ← (fun s => Res.ok s.frame s)
      M.modify fun s =>
        { s with frame := some { locals := locals, captured := env, globalDecls := [] } }
      let r ← M.attempt (execBlock fuel body)
      M.modify fun s => { s with frame := caller }
      match r with
      | .error e => M.throwValue e
      | .ok sig =>
        match sig with
        | .ret v => pure v
        | _ => pure .none
    | v => do
      let h ← getHeap
      typeError s!"'{v.typeName h}' object is not callable"

/-- Assign `v` to a target. -/
def bindTarget : Nat → Target → Value → M Unit
  | 0, _, _ => M.timeout
  | fuel + 1, t, v =>
    match t with
    | .name x => M.modify fun s => s.setVar x v
    | .index oe ie => do
      let ov ← evalExpr fuel oe
      let iv ← evalExpr fuel ie
      setIndex ov iv v
    | .tuple ts => do
      let items ← iterM v
      if items.length != ts.length then
        M.raisePy "ValueError"
          s!"expected {ts.length} value(s) to unpack, got {items.length}"
      else bindTargets fuel ts items

/-- Assign several targets elementwise (tuple unpacking). -/
def bindTargets : Nat → List Target → List Value → M Unit
  | _, [], _ => pure ()
  | 0, _, _ => M.timeout
  | fuel + 1, t :: ts, vs => do
    match vs with
    | [] => pure ()
    | v :: rest => do
      bindTarget fuel t v
      bindTargets fuel ts rest

/-- Assign the same value to each target of `a = b = e`. -/
def bindAll : Nat → List Target → Value → M Unit
  | _, [], _ => pure ()
  | 0, _, _ => M.timeout
  | fuel + 1, t :: ts, v => do
    bindTarget fuel t v
    bindAll fuel ts v

/-- Read the current value of an assignment target, for `op=`. -/
def readTarget : Nat → Target → M Value
  | 0, _ => M.timeout
  | fuel + 1, t =>
    match t with
    | .name x => lookupOrRaise x
    | .index oe ie => evalExpr fuel (.subscript oe ie)
    | .tuple _ => typeError "augmented assignment is not allowed on a tuple target"

/-- Evaluate the default values of a `def`, left to right.  They apply to the
trailing parameters; the parser has already checked that the parameters with
defaults form a suffix. -/
def evalDefaults : Nat → List (String × Option Expr) → M (List Value)
  | _, [] => pure []
  | 0, _ => M.timeout
  | fuel + 1, (_, d) :: rest =>
    match d with
    | Option.none => evalDefaults fuel rest
    | some e => do
      let v ← evalExpr fuel e
      let ds ← evalDefaults fuel rest
      pure (v :: ds)

/-- Execute one statement. -/
def execStmt : Nat → Stmt → M Signal
  | 0, _ => M.timeout
  | fuel + 1, st =>
    match st with
    | .pass => pure .normal
    | .expr e => do
      let _ ← evalExpr fuel e
      pure .normal
    | .assign targets e => do
      let v ← evalExpr fuel e
      bindAll fuel targets v
      pure .normal
    | .augAssign t op e => do
      let cur ← readTarget fuel t
      let rv ← evalExpr fuel e
      let nv ← applyBinOp op cur rv
      bindTarget fuel t nv
      pure .normal
    | .ifS c thn els => do
      let cv ← evalExpr fuel c
      let h ← getHeap
      if cv.truthy h then execBlock fuel thn else execBlock fuel els
    | .whileS c body => whileLoop fuel c body
    | .forS t iter body => do
      let itv ← evalExpr fuel iter
      let items ← iterM itv
      execFor fuel t items body
    | .funcDef name params body => do
      let defaults ← evalDefaults fuel params
      let env ← currentEnv
      M.modify fun s => s.setVar name (.func name (params.map (·.1)) defaults body env)
      pure .normal
    | .ret e => do
      let v ← match e with
        | Option.none => pure Value.none
        | some e => evalExpr fuel e
      pure (.ret v)
    | .brk => pure .brk
    | .cont => pure .cont
    | .globalS names => do
      M.modify fun s =>
        match s.frame with
        | Option.none => s
        | some fr => { s with frame := some { fr with globalDecls := fr.globalDecls ++ names } }
      pure .normal
    | .raiseS e => do
      match e with
      | Option.none => M.raisePy "RuntimeError" "No active exception to re-raise"
      | some e => do
        let v ← evalExpr fuel e
        match v with
        | .exc _ _ => M.throwValue v
        | .excClass n => M.throwValue (.exc n [])
        | _ => typeError "exceptions must derive from BaseException"
    | .assertS c msg => do
      let cv ← evalExpr fuel c
      let h ← getHeap
      if cv.truthy h then pure .normal
      else do
        let args ← match msg with
          | Option.none => pure []
          | some m => do
            let mv ← evalExpr fuel m
            pure [mv]
        M.throwValue (.exc "AssertionError" args)
    | .delS o i => do
      let ov ← evalExpr fuel o
      let iv ← evalExpr fuel i
      delIndex ov iv
      pure .normal
    | .tryS body handlers orelse fin => execTry fuel body handlers orelse fin

/-- Execute a block, stopping at the first statement that does not fall
through. -/
def execBlock : Nat → Block → M Signal
  | _, [] => pure .normal
  | 0, _ => M.timeout
  | fuel + 1, s :: rest => do
    let sig ← execStmt fuel s
    match sig with
    | .normal => execBlock fuel rest
    | sig => pure sig

/-- `while c: body`.

Written in explicit state-passing style rather than with `do`, for two reasons:
the recursive call is then a genuine tail call, and unfolding one iteration in a
proof needs no reasoning about `bind` (see `SnakeFight.Hoare`). -/
def whileLoop : Nat → Expr → Block → M Signal
  | 0, _, _ => M.timeout
  | fuel + 1, c, body => fun s =>
    match evalExpr fuel c s with
    | .exn e s' => .exn e s'
    | .timeout s' => .timeout s'
    | .ok cv s1 =>
      if cv.truthy s1.heap then
        match execBlock fuel body s1 with
        | .exn e s' => .exn e s'
        | .timeout s' => .timeout s'
        | .ok .brk s2 => .ok .normal s2
        | .ok (.ret v) s2 => .ok (.ret v) s2
        | .ok _ s2 => whileLoop fuel c body s2
      else .ok .normal s1

/-- Run the body of a `for` over the remaining items. -/
def execFor : Nat → Target → List Value → Block → M Signal
  | _, _, [], _ => pure .normal
  | 0, _, _, _ => M.timeout
  | fuel + 1, t, v :: rest, body => fun s =>
    match bindTarget fuel t v s with
    | .exn e s' => .exn e s'
    | .timeout s' => .timeout s'
    | .ok _ s1 =>
      match execBlock fuel body s1 with
      | .exn e s' => .exn e s'
      | .timeout s' => .timeout s'
      | .ok .brk s2 => .ok .normal s2
      | .ok (.ret r) s2 => .ok (.ret r) s2
      | .ok _ s2 => execFor fuel t rest body s2

/-- `try` / `except` / `else` / `finally`. -/
def execTry : Nat → Block → List (Option Expr × Option String × Block) → Block → Block →
    M Signal
  | 0, _, _, _, _ => M.timeout
  | fuel + 1, body, handlers, orelse, fin => do
    -- The body, and then `else` if the body fell through.
    let r1 ← M.attempt (do
      let sig ← execBlock fuel body
      match sig with
      | .normal => execBlock fuel orelse
      | sig => pure sig)
    -- An exception gets offered to each handler in turn.
    let r2 ← match r1 with
      | .ok sig => pure (Except.ok sig)
      | .error e => M.attempt (runHandlers fuel e handlers)
    -- `finally` runs either way, and its own signal or exception wins.
    let r3 ← M.attempt (execBlock fuel fin)
    match r3 with
    | .error e3 => M.throwValue e3
    | .ok sigF =>
      match sigF with
      | .normal =>
        match r2 with
        | .ok sig => pure sig
        | .error e => M.throwValue e
      | sig => pure sig

/-- Offer exception `e` to each `except` clause; re-raise if none matches. -/
def runHandlers : Nat → Value → List (Option Expr × Option String × Block) → M Signal
  | _, e, [] => M.throwValue e
  | 0, _, _ => M.timeout
  | fuel + 1, e, (ty, bind, hbody) :: rest => do
    let matched ← match ty with
      | Option.none => pure true
      | some te => do
        let tv ← evalExpr fuel te
        pure (excMatches e tv)
    if matched then do
      match bind with
      | some n => M.modify fun s => s.setVar n e
      | Option.none => pure ()
      execBlock fuel hbody
    else runHandlers fuel e rest

end

/-! ## Running a program -/

/-- The default step budget for the command line and the test suite. -/
def defaultFuel : Nat := 2000000

/-- What happened when a program ran. -/
inductive Outcome where
  /-- The program finished; these are the lines it printed. -/
  | ok (out : List String)
  /-- The program died with an uncaught exception. -/
  | error (out : List String) (msg : String)
  /-- The program ran out of fuel. -/
  | timeout (out : List String)
  deriving Repr, BEq, Inhabited

/-- Run a program from the empty state. -/
def runProgram (fuel : Nat) (p : Program) : Res Signal := execBlock fuel p {}

/-- Run a program and summarize what happened. -/
def runOutcome (fuel : Nat) (p : Program) : Outcome :=
  match runProgram fuel p with
  | .ok _ s => .ok s.stdout
  | .exn e s => .error s.stdout (excMessage reprFuel s.heap e)
  | .timeout s => .timeout s.stdout

/-- Parse and run Python source. -/
def runSource (fuel : Nat) (src : String) : Except String Outcome := do
  let p ← parse src
  .ok (runOutcome fuel p)

/-- The lines a program prints, or `none` if it fails.  Handy in `#guard`. -/
def outputOf (src : String) : Option (List String) :=
  match runSource defaultFuel src with
  | .ok (.ok out) => some out
  | _ => Option.none

end SnakeFight
