import SnakeFight.Lexer

/-!
# Parser

A recursive-descent parser, with precedence climbing for the binary operators.
Fuel is threaded explicitly so that every function is structurally recursive;
the initial budget is derived from the token count, so exhausting it means the
parser has a bug rather than that the input was large.

Two Python details worth pointing out, because they show up later in the
semantics:

* comparisons chain (`0 <= i < n` parses as one `Expr.compare` node with two
  operators, and the middle operand is evaluated once);
* `elif` is desugared here into a nested `Stmt.ifS`.
-/

namespace SnakeFight

/-- Parser state: the token array and a cursor. -/
structure PState where
  /-- All tokens, ending with `Tok.eof`. -/
  toks : Array PTok
  /-- Cursor. -/
  pos : Nat
  deriving Inhabited

namespace PState

/-- The token under the cursor. -/
def cur (st : PState) : PTok := st.toks[st.pos]?.getD ⟨.eof, 0⟩
/-- The token under the cursor, without its line. -/
def tok (st : PState) : Tok := st.cur.tok
/-- Look ahead `n` tokens. -/
def tokAt (st : PState) (n : Nat) : Tok := (st.toks[st.pos + n]?.getD ⟨.eof, 0⟩).tok
/-- Advance the cursor. -/
def next (st : PState) : PState := { st with pos := st.pos + 1 }
/-- The current source line. -/
def line (st : PState) : Nat := st.cur.line

end PState

/-- Report a parse error at the cursor. -/
def perr {α} (st : PState) (msg : String) : Except String α :=
  .error s!"line {st.line}: {msg}"

/-- Consume the operator `o`. -/
def expectOp (st : PState) (o : String) : Except String PState :=
  if st.tok == Tok.op o then .ok st.next
  else perr st s!"expected '{o}' but found {st.tok.describe}"

/-- Consume the keyword `k`. -/
def expectKw (st : PState) (k : String) : Except String PState :=
  if st.tok == Tok.kw k then .ok st.next
  else perr st s!"expected '{k}' but found {st.tok.describe}"

/-- Consume an identifier. -/
def expectName (st : PState) : Except String (String × PState) :=
  match st.tok with
  | .name n => .ok (n, st.next)
  | t => perr st s!"expected a name but found {t.describe}"

/-- Consume the operator `o` if it is there. -/
def acceptOp (st : PState) (o : String) : Option PState :=
  if st.tok == Tok.op o then some st.next else Option.none

/-- Consume the keyword `k` if it is there. -/
def acceptKw (st : PState) (k : String) : Option PState :=
  if st.tok == Tok.kw k then some st.next else Option.none

/-- Skip blank logical lines.

Fuel makes this structurally recursive; one unit per remaining token is always
enough, so the budget can never actually run out. -/
def skipNewlines (st : PState) : PState :=
  go (st.toks.size + 1) st
where
  go : Nat → PState → PState
    | 0, st => st
    | n + 1, st =>
      match st.tok with
      | .newline => go n st.next
      | _ => st

/-- Turn an expression into an assignment target. -/
def exprToTarget : Expr → Except String Target
  | .name x => .ok (.name x)
  | .tupleE es | .listE es => do
    let ts ← es.mapM exprToTarget
    .ok (.tuple ts)
  | .subscript o i => .ok (.index o i)
  | _ => .error "cannot assign to this expression"

/-- Binary operator precedence.  Higher binds tighter. -/
def binPrec : Tok → Option (BinOp × Nat)
  | .op "|" => some (.bor, 1)
  | .op "^" => some (.bxor, 2)
  | .op "&" => some (.band, 3)
  | .op "<<" => some (.lshift, 4)
  | .op ">>" => some (.rshift, 4)
  | .op "+" => some (.add, 5)
  | .op "-" => some (.sub, 5)
  | .op "*" => some (.mul, 6)
  | .op "/" => some (.div, 6)
  | .op "//" => some (.floordiv, 6)
  | .op "%" => some (.mod, 6)
  | .op "**" => some (.pow, 8)
  | _ => Option.none

/-- The comparison operator at the cursor, and the state after it.  Handles the
two-token forms `not in` and `is not`. -/
def cmpOpAt (st : PState) : Option (CmpOp × PState) :=
  match st.tok with
  | .op "<" => some (.lt, st.next)
  | .op ">" => some (.gt, st.next)
  | .op "<=" => some (.le, st.next)
  | .op ">=" => some (.ge, st.next)
  | .op "==" => some (.eq, st.next)
  | .op "!=" => some (.ne, st.next)
  | .kw "in" => some (.isIn, st.next)
  | .kw "not" => if st.tokAt 1 == Tok.kw "in" then some (.notIn, st.next.next) else Option.none
  | .kw "is" => if st.tokAt 1 == Tok.kw "not" then some (.isNot, st.next.next) else some (.is, st.next)
  | _ => Option.none

/-- Augmented assignment operators. -/
def augOp : Tok → Option BinOp
  | .op "+=" => some .add
  | .op "-=" => some .sub
  | .op "*=" => some .mul
  | .op "/=" => some .div
  | .op "//=" => some .floordiv
  | .op "%=" => some .mod
  | .op "**=" => some .pow
  | .op "<<=" => some .lshift
  | .op ">>=" => some .rshift
  | .op "&=" => some .band
  | .op "|=" => some .bor
  | .op "^=" => some .bxor
  | _ => Option.none

/-- Python statement keywords that SnakeFight does not implement.  They are not
keywords in this lexer, so without this list they would produce a confusing
message about an unexpected name. -/
def unsupportedStmts : List String :=
  ["class", "import", "from", "with", "yield", "nonlocal", "async", "await", "match"]

/-- Python requires the parameters that have defaults to form a suffix of the
parameter list. -/
def defaultsAreSuffix (params : List (String × Option Expr)) : Bool :=
  go false params
where
  go : Bool → List (String × Option Expr) → Bool
    | _, [] => true
    | seen, (_, d) :: rest =>
      match d with
      | some _ => go true rest
      | Option.none => !seen && go false rest

/-- Tokens that cannot start an expression, used to detect an empty `return`. -/
def endsExpr : Tok → Bool
  | .newline | .eof | .dedent => true
  | .op ")" | .op "]" | .op "}" | .op ";" | .op ":" | .op "," | .op "=" => true
  | .kw "else" => true
  | _ => false

mutual

/-- `e if c else f`, the lowest-precedence expression form. -/
def pTernary (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (e, st) ← pOr fuel st
    match acceptKw st "if" with
    | some st => do
      let (c, st) ← pOr fuel st
      let st ← expectKw st "else"
      let (f, st) ← pTernary fuel st
      .ok (.ifE c e f, st)
    | Option.none => .ok (e, st)

/-- `or`, right-nested (which is fine: `or` is associative and both nestings
short-circuit identically). -/
def pOr (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (l, st) ← pAnd fuel st
    match acceptKw st "or" with
    | some st => do
      let (r, st) ← pOr fuel st
      .ok (.orE l r, st)
    | Option.none => .ok (l, st)

/-- `and`. -/
def pAnd (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (l, st) ← pNot fuel st
    match acceptKw st "and" with
    | some st => do
      let (r, st) ← pAnd fuel st
      .ok (.andE l r, st)
    | Option.none => .ok (l, st)

/-- `not`. -/
def pNot (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    -- `not in` is a comparison operator, not a `not` applied to `in`.
    if st.tok == Tok.kw "not" && st.tokAt 1 != Tok.kw "in" then do
      let (e, st) ← pNot fuel st.next
      .ok (.unop .not e, st)
    else pComparison fuel st

/-- A comparison chain: `a < b <= c`. -/
def pComparison (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (l, st) ← pBin fuel 0 st
    let (rest, st) ← pCmpRest fuel st
    .ok (if rest.isEmpty then l else .compare l rest, st)

/-- The `(op, operand)` tail of a comparison chain. -/
def pCmpRest (fuel : Nat) (st : PState) :
    Except String (List (CmpOp × Expr) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match cmpOpAt st with
    | some (op, st) => do
      let (r, st) ← pBin fuel 0 st
      let (rest, st) ← pCmpRest fuel st
      .ok ((op, r) :: rest, st)
    | Option.none => .ok ([], st)

/-- Binary operators by precedence climbing. -/
def pBin (fuel : Nat) (minPrec : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (l, st) ← pUnary fuel st
    pBinLoop fuel minPrec l st

/-- Absorb operators of precedence at least `minPrec` into `l`. -/
def pBinLoop (fuel : Nat) (minPrec : Nat) (l : Expr) (st : PState) :
    Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match binPrec st.tok with
    | some (op, prec) =>
      if prec < minPrec then .ok (l, st)
      else do
        -- `**` is right-associative; everything else is left-associative.
        let (r, st) ← pBin fuel (if op == BinOp.pow then prec else prec + 1) st.next
        pBinLoop fuel minPrec (.binop op l r) st
    | Option.none => .ok (l, st)

/-- Unary `+`, `-`, `~`.  These bind looser than `**`, as in Python. -/
def pUnary (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match st.tok with
    | .op "-" => do let (e, st) ← pUnary fuel st.next; .ok (.unop .neg e, st)
    | .op "+" => do let (e, st) ← pUnary fuel st.next; .ok (.unop .pos e, st)
    | .op "~" => do let (e, st) ← pUnary fuel st.next; .ok (.unop .invert e, st)
    | _ => do
      let (e, st) ← pAtom fuel st
      pTrailers fuel e st

/-- Calls, subscripts, slices and attribute access. -/
def pTrailers (fuel : Nat) (e : Expr) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match st.tok with
    | .op "(" => do
      let (args, kwargs, st) ← pArgs fuel st.next
      let st ← expectOp st ")"
      pTrailers fuel (.call e args kwargs) st
    | .op "[" => do
      let (idx, st) ← pSubscript fuel e st.next
      let st ← expectOp st "]"
      pTrailers fuel idx st
    | .op "." => do
      let (n, st) ← expectName st.next
      pTrailers fuel (.attr e n) st
    | _ => .ok (e, st)

/-- The inside of `obj[...]`: either an index or a slice. -/
def pSubscript (fuel : Nat) (obj : Expr) (st : PState) :
    Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    if st.tok == Tok.op ":" then do
      -- `obj[:hi]`
      let st := st.next
      if st.tok == Tok.op "]" then .ok (.slice obj Option.none Option.none, st)
      else if st.tok == Tok.op ":" then perr st "slice steps (a[i:j:k]) are not supported"
      else do
        let (hi, st) ← pTernary fuel st
        if st.tok == Tok.op ":" then perr st "slice steps (a[i:j:k]) are not supported"
        else .ok (.slice obj Option.none (some hi), st)
    else do
      let (i, st) ← pTernary fuel st
      if st.tok == Tok.op ":" then do
        let st := st.next
        if st.tok == Tok.op "]" then .ok (.slice obj (some i) Option.none, st)
        else if st.tok == Tok.op ":" then perr st "slice steps (a[i:j:k]) are not supported"
        else do
          let (hi, st) ← pTernary fuel st
          if st.tok == Tok.op ":" then perr st "slice steps (a[i:j:k]) are not supported"
          else .ok (.slice obj (some i) (some hi), st)
      else .ok (.subscript obj i, st)

/-- Call arguments: positional then keyword. -/
def pArgs (fuel : Nat) (st : PState) :
    Except String (List Expr × List (String × Expr) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    if st.tok == Tok.op ")" then .ok ([], [], st)
    else do
      -- `name = expr` is a keyword argument; anything else is positional.
      match st.tok, st.tokAt 1 with
      | .name n, .op "=" => do
        let (v, st) ← pTernary fuel st.next.next
        let (args, kwargs, st) ← pArgsTail fuel st
        if !args.isEmpty then perr st "positional argument follows keyword argument"
        else .ok ([], (n, v) :: kwargs, st)
      | _, _ => do
        let (a, st) ← pTernary fuel st
        let (args, kwargs, st) ← pArgsTail fuel st
        .ok (a :: args, kwargs, st)

/-- The `, ...` tail of an argument list. -/
def pArgsTail (fuel : Nat) (st : PState) :
    Except String (List Expr × List (String × Expr) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match acceptOp st "," with
    | some st => pArgs fuel st
    | Option.none => .ok ([], [], st)

/-- A comma-separated list of expressions, used for tuple displays, `return`
values and assignment targets.  Returns a tuple node if there was a comma. -/
def pExprList (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (e, st) ← pTernary fuel st
    if st.tok == Tok.op "," then do
      let (es, st) ← pExprListTail fuel st
      .ok (.tupleE (e :: es), st)
    else .ok (e, st)

/-- The elements after the first comma of an expression list. -/
def pExprListTail (fuel : Nat) (st : PState) : Except String (List Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match acceptOp st "," with
    | some st =>
      if endsExpr st.tok then .ok ([], st)   -- trailing comma
      else do
        let (e, st) ← pTernary fuel st
        let (es, st) ← pExprListTail fuel st
        .ok (e :: es, st)
    | Option.none => .ok ([], st)

/-- A target list, as used by `for` and by comprehensions.

This deliberately does *not* go through `pTernary`: in `for i in xs`, the `in`
must not be absorbed as a comparison operator, so targets are parsed with the
much tighter `pUnary` (an atom plus its trailers). -/
def pTargetList (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (e, st) ← pUnary fuel st
    if st.tok == Tok.op "," then do
      let (es, st) ← pTargetListTail fuel st
      .ok (.tupleE (e :: es), st)
    else .ok (e, st)

/-- The elements after the first comma of a target list. -/
def pTargetListTail (fuel : Nat) (st : PState) : Except String (List Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match acceptOp st "," with
    | some st =>
      if st.tok == Tok.kw "in" || st.tok == Tok.op "=" || endsExpr st.tok then .ok ([], st)
      else do
        let (e, st) ← pUnary fuel st
        let (es, st) ← pTargetListTail fuel st
        .ok (e :: es, st)
    | Option.none => .ok ([], st)

/-- Atoms: literals, names, parenthesized expressions, displays, `lambda`. -/
def pAtom (fuel : Nat) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match st.tok with
    | .int i => .ok (.int i, st.next)
    | .str s => pStrCat fuel s st.next
    | .name n => .ok (.name n, st.next)
    | .kw "None" => .ok (.none, st.next)
    | .kw "True" => .ok (.bool true, st.next)
    | .kw "False" => .ok (.bool false, st.next)
    | .kw "lambda" => do
      let (ps, st) ← pLambdaParams fuel st.next
      if !defaultsAreSuffix ps then
        perr st "non-default argument follows default argument"
      else do
      let st ← expectOp st ":"
      let (body, st) ← pTernary fuel st
      .ok (.lam ps body, st)
    | .op "(" =>
      let st := st.next
      if st.tok == Tok.op ")" then .ok (.tupleE [], st.next)
      else do
        let (e, st) ← pExprList fuel st
        let st ← expectOp st ")"
        .ok (e, st)
    | .op "[" =>
      let st := st.next
      if st.tok == Tok.op "]" then .ok (.listE [], st.next)
      else do
        let (first, st) ← pTernary fuel st
        if st.tok == Tok.kw "for" then do
          -- `[e for t in it if c]`
          let st ← expectKw st "for"
          let (te, st) ← pTargetList fuel st
          let tgt ← match exprToTarget te with
            | .ok t => .ok t
            | .error e => perr st e
          let st ← expectKw st "in"
          let (iter, st) ← pOr fuel st
          let (cond, st) ← match acceptKw st "if" with
            | some st => do let (c, st) ← pOr fuel st; .ok (some c, st)
            | Option.none => .ok (Option.none, st)
          let st ← expectOp st "]"
          .ok (.listComp first tgt iter cond, st)
        else do
          let (rest, st) ← pExprListTail fuel st
          let st ← expectOp st "]"
          .ok (.listE (first :: rest), st)
    | .op "{" =>
      let st := st.next
      if st.tok == Tok.op "}" then .ok (.dictE [], st.next)
      else do
        let (kvs, st) ← pDictItems fuel st
        let st ← expectOp st "}"
        .ok (.dictE kvs, st)
    | t => perr st s!"unexpected {t.describe}"

/-- Adjacent string literals are concatenated. -/
def pStrCat (fuel : Nat) (acc : String) (st : PState) : Except String (Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match st.tok with
    | .str s => pStrCat fuel (acc ++ s) st.next
    | _ => .ok (.str acc, st)

/-- `lambda` parameters, which may have default values. -/
def pLambdaParams (fuel : Nat) (st : PState) :
    Except String (List (String × Option Expr) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    if st.tok == Tok.op ":" then .ok ([], st)
    else do
      let (n, st) ← expectName st
      let (d, st) ← match acceptOp st "=" with
        | some st => do let (e, st) ← pTernary fuel st; .ok (some e, st)
        | Option.none => .ok (Option.none, st)
      match acceptOp st "," with
      | some st => do let (ns, st) ← pLambdaParams fuel st; .ok ((n, d) :: ns, st)
      | Option.none => .ok ([(n, d)], st)

/-- `key: value` pairs of a dict display. -/
def pDictItems (fuel : Nat) (st : PState) :
    Except String (List (Expr × Expr) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (k, st) ← pTernary fuel st
    if st.tok == Tok.op "," || st.tok == Tok.op "}" then
      perr st "set literals are not supported (this looks like a set, not a dict)"
    else do
    let st ← expectOp st ":"
    let (v, st) ← pTernary fuel st
    match acceptOp st "," with
    | some st =>
      if st.tok == Tok.op "}" then .ok ([(k, v)], st)
      else do
        let (rest, st) ← pDictItems fuel st
        .ok ((k, v) :: rest, st)
    | Option.none => .ok ([(k, v)], st)

end

/-! ### Statements -/

/-- Function parameters: `x`, or `x=default`. -/
def pParams (fuel : Nat) (st : PState) :
    Except String (List (String × Option Expr) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    if st.tok == Tok.op ")" then .ok ([], st)
    else do
      let (n, st) ← expectName st
      let (d, st) ← match acceptOp st "=" with
        | some st => do let (e, st) ← pTernary (32 * fuel + 64) st; .ok (some e, st)
        | Option.none => .ok (Option.none, st)
      match acceptOp st "," with
      | some st => do let (ps, st) ← pParams fuel st; .ok ((n, d) :: ps, st)
      | Option.none => .ok ([(n, d)], st)

mutual

/-- One statement. -/
def pStmt (fuel : Nat) (st : PState) : Except String (List Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match st.tok with
    | .kw "if" => do
      let (s, st) ← pIf fuel st
      .ok ([s], st)
    | .kw "while" => do
      let (c, st) ← pTernary fuel st.next
      let (body, st) ← pBlock fuel st
      .ok ([.whileS c body], st)
    | .kw "for" => do
      let (te, st) ← pTargetList fuel st.next
      let tgt ← match exprToTarget te with
        | .ok t => .ok t
        | .error e => perr st e
      let st ← expectKw st "in"
      let (iter, st) ← pExprList fuel st
      let (body, st) ← pBlock fuel st
      .ok ([.forS tgt iter body], st)
    | .kw "def" => do
      let (n, st) ← expectName st.next
      let st ← expectOp st "("
      let (ps, st) ← pParams fuel st
      if !defaultsAreSuffix ps then
        perr st "non-default argument follows default argument"
      else do
      let st ← expectOp st ")"
      -- Optional return annotation, which we ignore.
      let st ← match acceptOp st "->" with
        | some st => do let (_, st) ← pTernary fuel st; .ok st
        | Option.none => .ok st
      let (body, st) ← pBlock fuel st
      .ok ([.funcDef n ps body], st)
    | .kw "try" => pTry fuel st
    | .kw "else" =>
      perr st "unexpected 'else' ('for'/'while' else clauses are not supported)"
    | .name n =>
      if unsupportedStmts.contains n && st.tokAt 1 != Tok.op "=" then
        perr st s!"'{n}' is not supported by SnakeFight"
      else pSimpleLine fuel st
    | _ => pSimpleLine fuel st

/-- `if` / `elif` / `else`, desugaring `elif` into a nested `if`. -/
def pIf (fuel : Nat) (st : PState) : Except String (Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let st ← if st.tok == Tok.kw "elif" then expectKw st "elif" else expectKw st "if"
    let (c, st) ← pTernary fuel st
    let (thn, st) ← pBlock fuel st
    let st := skipNewlines st
    if st.tok == Tok.kw "elif" then do
      let (s, st) ← pIf fuel st
      .ok (.ifS c thn [s], st)
    else match acceptKw st "else" with
      | some st => do
        let (els, st) ← pBlock fuel st
        .ok (.ifS c thn els, st)
      | Option.none => .ok (.ifS c thn [], st)

/-- `try` / `except` / `else` / `finally`. -/
def pTry (fuel : Nat) (st : PState) : Except String (List Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let st ← expectKw st "try"
    let (body, st) ← pBlock fuel st
    let (handlers, st) ← pHandlers fuel (skipNewlines st)
    let st := skipNewlines st
    let (orelse, st) ← match acceptKw st "else" with
      | some st => pBlock fuel st
      | Option.none => .ok ([], st)
    let st := skipNewlines st
    let (fin, st) ← match acceptKw st "finally" with
      | some st => pBlock fuel st
      | Option.none => .ok ([], st)
    if handlers.isEmpty && fin.isEmpty then
      perr st "'try' must have at least one 'except' or 'finally' clause"
    else .ok ([.tryS body handlers orelse fin], st)

/-- `except [T [as n]]:` clauses. -/
def pHandlers (fuel : Nat) (st : PState) :
    Except String (List (Option Expr × Option String × List Stmt) × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match acceptKw st "except" with
    | Option.none => .ok ([], st)
    | some st => do
      let (ty, bind, st) ←
        if st.tok == Tok.op ":" then .ok (Option.none, Option.none, st)
        else do
          let (t, st) ← pTernary fuel st
          match acceptKw st "as" with
          | some st => do let (n, st) ← expectName st; .ok (some t, some n, st)
          | Option.none =>
            -- `except ValueError as e` may also be written with a name token
            -- because `as` is not a keyword in this lexer.
            match st.tok with
            | .name "as" => do let (n, st) ← expectName st.next; .ok (some t, some n, st)
            | _ => .ok (some t, Option.none, st)
      let (hbody, st) ← pBlock fuel st
      let (rest, st) ← pHandlers fuel (skipNewlines st)
      .ok ((ty, bind, hbody) :: rest, st)

/-- `: suite`, either inline or an indented block. -/
def pBlock (fuel : Nat) (st : PState) : Except String (List Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let st ← expectOp st ":"
    if st.tok == Tok.newline then do
      let st := skipNewlines st
      if st.tok != Tok.indent then perr st "expected an indented block"
      else do
        let (ss, st) ← pStmts fuel st.next
        if st.tok == Tok.dedent then .ok (ss, st.next)
        else perr st "expected the block to end"
    else pSimpleLine fuel st

/-- Statements until the end of a block. -/
def pStmts (fuel : Nat) (st : PState) : Except String (List Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    let st := skipNewlines st
    match st.tok with
    | .dedent | .eof => .ok ([], st)
    | _ => do
      let (ss, st) ← pStmt fuel st
      let (rest, st) ← pStmts fuel st
      .ok (ss ++ rest, st)

/-- A line of one or more simple statements separated by `;`. -/
def pSimpleLine (fuel : Nat) (st : PState) : Except String (List Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (s, st) ← pSmall fuel st
    match acceptOp st ";" with
    | some st =>
      if st.tok == Tok.newline then .ok ([s], st.next)
      else do
        let (rest, st) ← pSimpleLine fuel st
        .ok (s :: rest, st)
    | Option.none =>
      match st.tok with
      | .newline => .ok ([s], st.next)
      | .eof | .dedent => .ok ([s], st)
      | t => perr st s!"unexpected {t.describe} after a statement"

/-- One simple statement. -/
def pSmall (fuel : Nat) (st : PState) : Except String (Stmt × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 =>
    match st.tok with
    | .kw "pass" => .ok (.pass, st.next)
    | .kw "break" => .ok (.brk, st.next)
    | .kw "continue" => .ok (.cont, st.next)
    | .kw "return" =>
      let st := st.next
      if endsExpr st.tok then .ok (.ret Option.none, st)
      else do
        let (e, st) ← pExprList fuel st
        .ok (.ret (some e), st)
    | .kw "raise" =>
      let st := st.next
      if endsExpr st.tok then .ok (.raiseS Option.none, st)
      else do
        let (e, st) ← pTernary fuel st
        .ok (.raiseS (some e), st)
    | .kw "assert" => do
      let (e, st) ← pTernary fuel st.next
      match acceptOp st "," with
      | some st => do
        let (m, st) ← pTernary fuel st
        .ok (.assertS e (some m), st)
      | Option.none => .ok (.assertS e Option.none, st)
    | .kw "global" => do
      let (ns, st) ← pNameList fuel st.next
      .ok (.globalS ns, st)
    | .kw "del" => do
      let (e, st) ← pTernary fuel st.next
      match e with
      | .subscript o i => .ok (.delS o i, st)
      | _ => perr st "only 'del obj[key]' is supported"
    | _ => do
      let (e, st) ← pExprList fuel st
      match augOp st.tok with
      | some op => do
        let (r, st) ← pExprList fuel st.next
        match exprToTarget e with
        | .ok t => .ok (.augAssign t op r, st)
        | .error m => perr st m
      | Option.none =>
        if st.tok == Tok.op "=" then do
          let (targets, rhs, st) ← pAssignRest fuel [e] st
          let ts ← targets.mapM fun te => match exprToTarget te with
            | .ok t => .ok t
            | .error m => perr st m
          .ok (.assign ts rhs, st)
        else .ok (.expr e, st)

/-- The `= ...` chain of an assignment; the last expression is the value. -/
def pAssignRest (fuel : Nat) (acc : List Expr) (st : PState) :
    Except String (List Expr × Expr × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let st ← expectOp st "="
    let (e, st) ← pExprList fuel st
    if st.tok == Tok.op "=" then pAssignRest fuel (acc ++ [e]) st
    else .ok (acc, e, st)

/-- `a, b, c` -- names only. -/
def pNameList (fuel : Nat) (st : PState) : Except String (List String × PState) :=
  match fuel with
  | 0 => perr st "parser ran out of fuel"
  | fuel + 1 => do
    let (n, st) ← expectName st
    match acceptOp st "," with
    | some st => do let (ns, st) ← pNameList fuel st; .ok (n :: ns, st)
    | Option.none => .ok ([n], st)

end

/-- Parse a whole module. -/
def parse (src : String) : Except String Program := do
  let toks ← tokenize src
  let st : PState := { toks := toks.toArray, pos := 0 }
  let fuel := 32 * toks.length + 256
  let (ss, st) ← pStmts fuel st
  if st.tok == Tok.eof then .ok ss
  else perr st s!"unexpected {st.tok.describe}"

/-- Parse a single expression, for the REPL and for tests. -/
def parseExpr (src : String) : Except String Expr := do
  let toks ← tokenize src
  let st : PState := { toks := toks.toArray, pos := 0 }
  let (e, _) ← pTernary (32 * toks.length + 256) st
  .ok e

end SnakeFight
