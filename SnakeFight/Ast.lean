/-
Abstract syntax for MiniPython: the subset of Python that SnakeFight understands.

The AST is deliberately close to CPython's own `ast` module so that the parser
stays boring and the interpreter reads like the language reference.
-/

namespace SnakeFight

/-- Unary operators: `-x`, `+x`, `not x`, `~x`. -/
inductive UnOp where
  | neg | pos | not | invert
  deriving Repr, BEq, Inhabited

/-- Binary arithmetic/bitwise operators. -/
inductive BinOp where
  | add | sub | mul | div | floordiv | mod | pow
  | lshift | rshift | band | bor | bxor
  deriving Repr, BEq, Inhabited

/-- How a binary operator is written, for error messages. -/
def BinOp.symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
  | .floordiv => "//" | .mod => "%" | .pow => "**"
  | .lshift => "<<" | .rshift => ">>"
  | .band => "&" | .bor => "|" | .bxor => "^"

/-- How a unary operator is written. -/
def UnOp.symbol : UnOp → String
  | .neg => "-" | .pos => "+" | .not => "not" | .invert => "~"

/-- Comparison operators, including the identity and membership tests. -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge | isIn | notIn | is | isNot
  deriving Repr, BEq, Inhabited

/-- How a comparison operator is written. -/
def CmpOp.symbol : CmpOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .isIn => "in" | .notIn => "not in" | .is => "is" | .isNot => "is not"

mutual

/-- Expressions. -/
inductive Expr where
  /-- Integer literal. Python integers are unbounded, so we use `Int`. -/
  | int (i : Int)
  /-- String literal. -/
  | str (s : String)
  /-- `True` / `False`. -/
  | bool (b : Bool)
  /-- `None`. -/
  | none
  /-- Variable reference. -/
  | name (x : String)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (l r : Expr)
  /-- Chained comparison: `a < b <= c` is `compare a [(lt, b), (le, c)]`. -/
  | compare (l : Expr) (rest : List (CmpOp × Expr))
  /-- `l and r`, short-circuiting and value-returning. -/
  | andE (l r : Expr)
  /-- `l or r`, short-circuiting and value-returning. -/
  | orE (l r : Expr)
  /-- `t if c else f`. -/
  | ifE (c t f : Expr)
  /-- `f(a, b, k=v)`. -/
  | call (f : Expr) (args : List Expr) (kwargs : List (String × Expr))
  | listE (es : List Expr)
  | tupleE (es : List Expr)
  | dictE (kvs : List (Expr × Expr))
  /-- `obj[idx]`. -/
  | subscript (obj idx : Expr)
  /-- `obj[lo:hi]`. -/
  | slice (obj : Expr) (lo hi : Option Expr)
  /-- `obj.field`, used for method lookup. -/
  | attr (obj : Expr) (field : String)
  /-- `lambda x, y=d: body`. -/
  | lam (params : List (String × Option Expr)) (body : Expr)
  /-- `[elem for tgt in iter if cond]`. -/
  | listComp (elem : Expr) (tgt : Target) (iter : Expr) (cond : Option Expr)
  deriving Repr, BEq, Inhabited

/-- Assignment targets. -/
inductive Target where
  | name (x : String)
  /-- `a, b = ...` -- also used for `[a, b] = ...`. -/
  | tuple (ts : List Target)
  /-- `obj[idx] = ...` -/
  | index (obj idx : Expr)
  deriving Repr, BEq, Inhabited

end

/-- Statements.

`elif` is desugared by the parser into a nested `ifS` in the else-branch, so an
`ifS` node always carries exactly one condition.  That keeps both the
interpreter and the program logic in `SnakeFight.Hoare` free of an auxiliary
induction over branch lists. -/
inductive Stmt where
  /-- A bare expression, evaluated for its side effects. -/
  | expr (e : Expr)
  /-- `t1 = t2 = e`. -/
  | assign (targets : List Target) (e : Expr)
  /-- `t op= e`. -/
  | augAssign (t : Target) (op : BinOp) (e : Expr)
  /-- `if c: thn else: els`. -/
  | ifS (c : Expr) (thn els : List Stmt)
  | whileS (c : Expr) (body : List Stmt)
  | forS (t : Target) (iter : Expr) (body : List Stmt)
  /-- `def name(p1, p2=default): body`. -/
  | funcDef (name : String) (params : List (String × Option Expr)) (body : List Stmt)
  | ret (e : Option Expr)
  | brk
  | cont
  | pass
  | globalS (names : List String)
  /-- `raise e`; bare `raise` is not supported (`none` re-raises nothing). -/
  | raiseS (e : Option Expr)
  /-- `try: body except T as x: h ... else: orelse finally: fin`.

  A handler is `(exception type, bound name, body)`; a `none` type is a bare
  `except:`. -/
  | tryS (body : List Stmt) (handlers : List (Option Expr × Option String × List Stmt))
      (orelse : List Stmt) (fin : List Stmt)
  | assertS (e : Expr) (msg : Option Expr)
  /-- `del obj[idx]`. -/
  | delS (obj idx : Expr)
  deriving Repr, BEq, Inhabited

/-- A module is a block of statements. -/
abbrev Block := List Stmt

/-- A whole parsed program. -/
abbrev Program := Block

end SnakeFight
