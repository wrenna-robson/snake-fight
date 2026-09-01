import SnakeFight.Ast

/-!
# Tokenizer

The only interesting part of tokenizing Python is that layout is significant.
This lexer therefore does what CPython's does:

* it tracks a stack of indentation columns and synthesizes `indent` / `dedent`
  tokens at the start of each logical line;
* blank lines and comment-only lines produce no tokens at all, so they cannot
  change the indentation stack;
* inside `(`, `[` or `{` newlines are ignored (implicit line joining), and a
  trailing `\` joins lines explicitly.

Tabs count as 8 columns.  Fuel is derived from the input length, so the loop is
structurally obviously terminating; running out of it is an internal error.
-/

namespace SnakeFight

/-- A token. -/
inductive Tok where
  | name (s : String)
  | kw (s : String)
  | int (i : Int)
  | str (s : String)
  | op (s : String)
  /-- End of a logical line. -/
  | newline
  | indent
  | dedent
  | eof
  deriving Repr, BEq, Inhabited

/-- Render a token the way it should appear in a parse error. -/
def Tok.describe : Tok → String
  | .name s => "name '" ++ s ++ "'"
  | .kw s => "keyword '" ++ s ++ "'"
  | .int i => "number " ++ toString i
  | .str _ => "string literal"
  | .op s => "'" ++ s ++ "'"
  | .newline => "end of line"
  | .indent => "an indented block"
  | .dedent => "a dedent"
  | .eof => "end of file"

/-- A token together with the line it came from, for error reporting. -/
structure PTok where
  /-- The token. -/
  tok : Tok
  /-- 1-based source line. -/
  line : Nat
  deriving Repr, BEq, Inhabited

/-- Python's reserved words (only those MiniPython recognizes). -/
def keywords : List String :=
  ["if", "elif", "else", "while", "for", "in", "def", "return", "break",
   "continue", "pass", "and", "or", "not", "is", "None", "True", "False",
   "global", "raise", "try", "except", "finally", "assert", "lambda", "del"]

/-- Multi-character operators, longest first so that greedy matching is correct. -/
def multiOps : List String :=
  ["**=", "//=", "<<=", ">>=", "**", "//", "<<", ">>", "<=", ">=", "==", "!=",
   "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "->"]

/-- Single-character operators and delimiters. -/
def singleOps : List Char :=
  ['+', '-', '*', '/', '%', '(', ')', '[', ']', '{', '}', ':', ',', '.', '=',
   '<', '>', '&', '|', '^', '~', ';']

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentCont (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Does `cs` start with the characters of `p`? -/
private def startsWith (cs : List Char) (p : String) : Bool :=
  go cs p.toList
where
  go : List Char → List Char → Bool
    | _, [] => true
    | [], _ :: _ => false
    | c :: cs, d :: ds => c == d && go cs ds

private def dropN (cs : List Char) (n : Nat) : List Char := cs.drop n

/-- Scan an identifier or keyword. -/
private def takeIdent (cs : List Char) : String × List Char :=
  let ⟨pre, rest⟩ := cs.span isIdentCont
  (String.ofList pre, rest)

/-- Value of a list of decimal digits.  Structural on the list, so the kernel
can evaluate it; `String.toNat!` cannot be reduced by the kernel at all. -/
private def natOfDigits (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Scan a decimal integer, allowing `_` separators. -/
private def takeInt (cs : List Char) : Except String (Int × List Char) :=
  let ⟨pre, rest⟩ := cs.span (fun c => c.isDigit || c == '_')
  match rest with
  | '.' :: _ => .error "floating point literals are not supported"
  | 'e' :: _ | 'E' :: _ => .error "floating point literals are not supported"
  | _ =>
    let digits := pre.filter (fun c => c != '_')
    .ok (natOfDigits digits, rest)

/-- Scan a string literal body, given the quote character and whether it is a
triple-quoted string. -/
private def takeStrBody : Nat → String → Char → List Char → Bool →
    Except String (String × List Char)
  | 0, _, _, _, _ => .error "internal error: string literal too long"
  | fuel + 1, acc, q, cs, triple =>
    match cs with
    | [] => .error "unterminated string literal"
    | '\\' :: c :: rest =>
      let e :=
        if c == 'n' then "\n" else if c == 't' then "\t" else if c == 'r' then "\r"
        else if c == '\\' then "\\" else if c == '\'' then "'" else if c == '"' then "\""
        else if c == '0' then "\x00" else String.ofList ['\\', c]
      takeStrBody fuel (acc ++ e) q rest triple
    | c :: rest =>
      if c == q then
        if triple then
          if startsWith rest (String.ofList [q, q]) then .ok (acc, dropN rest 2)
          else takeStrBody fuel (acc.push c) q rest triple
        else .ok (acc, rest)
      else if c == '\n' && !triple then .error "unterminated string literal"
      else takeStrBody fuel (acc.push c) q rest triple

/-- Lexer state. -/
private structure LSt where
  toks : List PTok := []      -- reversed
  indents : List Nat := [0]   -- innermost first
  depth : Nat := 0            -- bracket nesting
  lineStart : Bool := true
  hadTok : Bool := false      -- did the current logical line produce a token?
  line : Nat := 1

private def emit (st : LSt) (t : Tok) : LSt :=
  { st with toks := ⟨t, st.line⟩ :: st.toks, hadTok := true }

/-- Column width of the leading whitespace, and the rest of the line. -/
private def measureIndent (cs : List Char) : Nat × List Char :=
  go cs 0
where
  go : List Char → Nat → Nat × List Char
    | ' ' :: rest, n => go rest (n + 1)
    | '\t' :: rest, n => go rest (n + 8)
    | cs, n => (n, cs)

/-- Pop indentation levels down to `col`, emitting `dedent`s.

Fuel is the depth of the indentation stack, which is exactly how many levels can
be popped, so the budget is never exhausted.  (Structural recursion on the fuel
keeps this reducible in the kernel, which matters for the proofs in
`SnakeFight.Examples`.) -/
private def closeToGo : Nat → LSt → Nat → Except String LSt
  | 0, st, _ => .ok st
  | n + 1, st, col =>
    match st.indents with
    | [] => .error "internal error: empty indentation stack"
    | top :: rest =>
      if top == col then .ok st
      else if top < col then .error s!"line {st.line}: unexpected indent"
      else closeToGo n { (emit st .dedent) with indents := rest, hadTok := st.hadTok } col

private def closeTo (st : LSt) (col : Nat) : Except String LSt :=
  closeToGo (st.indents.length + 1) st col

/-- Tokenize a Python source file. -/
def tokenize (src : String) : Except String (List PTok) :=
  let cs := src.toList
  go (8 * cs.length + 64) cs {}
where
  go : Nat → List Char → LSt → Except String (List PTok)
    | 0, _, _ => .error "internal error: lexer ran out of fuel"
    | fuel + 1, cs, st => do
      if st.lineStart && st.depth == 0 then
        let (col, rest) := measureIndent cs
        match rest with
        | [] =>
          -- End of input: close all blocks.
          let st ← closeTo { st with lineStart := false } 0
          .ok ((emit st .eof).toks.reverse)
        | '\n' :: rest' => go fuel rest' { st with line := st.line + 1 }
        | '#' :: _ => go fuel (rest.dropWhile (fun c => c != '\n')) st
        | _ =>
          match st.indents with
          | [] => .error "internal error: empty indentation stack"
          | top :: _ =>
            if col > top then
              go fuel rest { (emit st .indent) with
                indents := col :: st.indents, lineStart := false, hadTok := false }
            else
              let st ← closeTo st col
              go fuel rest { st with lineStart := false, hadTok := false }
      else
        match cs with
        | [] =>
          let st := if st.hadTok then emit st .newline else st
          let st ← closeTo { st with lineStart := false } 0
          .ok ((emit st .eof).toks.reverse)
        | ' ' :: rest | '\t' :: rest | '\r' :: rest => go fuel rest st
        | '#' :: rest => go fuel (rest.dropWhile (fun c => c != '\n')) st
        | '\\' :: '\n' :: rest => go fuel rest { st with line := st.line + 1 }
        | '\n' :: rest =>
          if st.depth > 0 then go fuel rest { st with line := st.line + 1 }
          else
            let st := if st.hadTok then emit st .newline else st
            go fuel rest { st with lineStart := true, line := st.line + 1, hadTok := false }
        | c :: rest =>
          if c == '"' || c == '\'' then
            let triple := startsWith rest (String.ofList [c, c])
            let body := if triple then dropN rest 2 else rest
            match takeStrBody (8 * cs.length + 8) "" c body triple with
            | .error e => .error s!"line {st.line}: {e}"
            | .ok (s, rest') => go fuel rest' (emit st (.str s))
          else if c.isDigit then
            match takeInt cs with
            | .error e => .error s!"line {st.line}: {e}"
            | .ok (i, rest') => go fuel rest' (emit st (.int i))
          else if isIdentStart c then
            let (id, rest') := takeIdent cs
            -- Reject string prefixes we do not implement rather than silently
            -- treating `f"..."` as a name followed by a string.
            match rest' with
            | q :: _ =>
              if (q == '"' || q == '\'') then
                .error s!"line {st.line}: string prefix '{id}' is not supported"
              else
                go fuel rest' (emit st (if keywords.contains id then .kw id else .name id))
            | [] => go fuel rest' (emit st (if keywords.contains id then .kw id else .name id))
          else
            match multiOps.find? (fun o => startsWith cs o) with
            | some o => go fuel (dropN cs o.length) (emit st (.op o))
            | Option.none =>
              if singleOps.contains c then
                let st := emit st (.op (String.ofList [c]))
                let st :=
                  if c == '(' || c == '[' || c == '{' then { st with depth := st.depth + 1 }
                  else if c == ')' || c == ']' || c == '}' then { st with depth := st.depth - 1 }
                  else st
                go fuel rest st
              else
                .error s!"line {st.line}: unexpected character '{c}'"

end SnakeFight
