import SnakeFight.Lexer

/-!
# Token lists for the worked examples

`PState` is a token array plus a `Nat` cursor, so every step of the parser
reads `st.toks[st.pos]?`.  Reduction zeta-expands `let`, so inside `parse src`
that array is the *unreduced* `tokenize src` term and each of those reads
re-derives the whole token list from the source.  Reducing `parse src` in one
go therefore reruns the lexer once per cursor read and never finishes, even
though the lexer and the parser each reduce in well under a second.

Naming the token list breaks that fusion.  `SnakeFight.Examples` proves
`tokenize src = .ok <the list named here>` and then runs the parser on the
named list, so each half is reduced exactly once.

These lists are generated from the example sources by `tests/gen_toks.lean`;
regenerate them if an example changes.  A wrong list here cannot make a proof
pass -- the `tokenize src = .ok ...` step is itself checked by the kernel, so a
mismatch fails the build.
-/

namespace SnakeFight

/-- Tokens of `addSrc`. -/
def addToks : List PTok :=
  [⟨.name "print", 1⟩, ⟨.op "(", 1⟩, ⟨.int 1, 1⟩, ⟨.op "+", 1⟩,
   ⟨.int 2, 1⟩, ⟨.op ")", 1⟩, ⟨.newline, 1⟩, ⟨.eof, 2⟩]

/-- Tokens of `concatSrc`. -/
def concatToks : List PTok :=
  [⟨.name "print", 1⟩, ⟨.op "(", 1⟩, ⟨.str "hello ", 1⟩, ⟨.op "+", 1⟩,
   ⟨.str "world", 1⟩, ⟨.op ")", 1⟩, ⟨.newline, 1⟩, ⟨.eof, 2⟩]

/-- Tokens of `aliasSrc`. -/
def aliasToks : List PTok :=
  [⟨.name "a", 1⟩, ⟨.op "=", 1⟩, ⟨.op "[", 1⟩, ⟨.int 1, 1⟩, ⟨.op ",", 1⟩,
   ⟨.int 2, 1⟩, ⟨.op "]", 1⟩, ⟨.newline, 1⟩, ⟨.name "b", 2⟩, ⟨.op "=", 2⟩,
   ⟨.name "a", 2⟩, ⟨.newline, 2⟩, ⟨.name "b", 3⟩, ⟨.op ".", 3⟩,
   ⟨.name "append", 3⟩, ⟨.op "(", 3⟩, ⟨.int 3, 3⟩, ⟨.op ")", 3⟩,
   ⟨.newline, 3⟩, ⟨.name "print", 4⟩, ⟨.op "(", 4⟩, ⟨.name "a", 4⟩,
   ⟨.op ",", 4⟩, ⟨.name "a", 4⟩, ⟨.kw "is", 4⟩, ⟨.name "b", 4⟩,
   ⟨.op ")", 4⟩, ⟨.newline, 4⟩, ⟨.eof, 5⟩]

/-- Tokens of `adderSrc`. -/
def adderToks : List PTok :=
  [⟨.kw "def", 1⟩, ⟨.name "make_adder", 1⟩, ⟨.op "(", 1⟩, ⟨.name "n", 1⟩,
   ⟨.op ")", 1⟩, ⟨.op ":", 1⟩, ⟨.newline, 1⟩, ⟨.indent, 2⟩,
   ⟨.kw "def", 2⟩, ⟨.name "add", 2⟩, ⟨.op "(", 2⟩, ⟨.name "v", 2⟩,
   ⟨.op ")", 2⟩, ⟨.op ":", 2⟩, ⟨.newline, 2⟩, ⟨.indent, 3⟩,
   ⟨.kw "return", 3⟩, ⟨.name "v", 3⟩, ⟨.op "+", 3⟩, ⟨.name "n", 3⟩,
   ⟨.newline, 3⟩, ⟨.dedent, 4⟩, ⟨.kw "return", 4⟩, ⟨.name "add", 4⟩,
   ⟨.newline, 4⟩, ⟨.dedent, 5⟩, ⟨.name "add3", 5⟩, ⟨.op "=", 5⟩,
   ⟨.name "make_adder", 5⟩, ⟨.op "(", 5⟩, ⟨.int 3, 5⟩, ⟨.op ")", 5⟩,
   ⟨.newline, 5⟩, ⟨.name "print", 6⟩, ⟨.op "(", 6⟩, ⟨.op "[", 6⟩,
   ⟨.name "add3", 6⟩, ⟨.op "(", 6⟩, ⟨.name "i", 6⟩, ⟨.op ")", 6⟩,
   ⟨.kw "for", 6⟩, ⟨.name "i", 6⟩, ⟨.kw "in", 6⟩, ⟨.name "range", 6⟩,
   ⟨.op "(", 6⟩, ⟨.int 5, 6⟩, ⟨.op ")", 6⟩, ⟨.op "]", 6⟩, ⟨.op ")", 6⟩,
   ⟨.newline, 6⟩, ⟨.eof, 7⟩]

/-- Tokens of `excSrc`. -/
def excToks : List PTok :=
  [⟨.kw "try", 1⟩, ⟨.op ":", 1⟩, ⟨.newline, 1⟩, ⟨.indent, 2⟩,
   ⟨.kw "raise", 2⟩, ⟨.name "KeyError", 2⟩, ⟨.op "(", 2⟩, ⟨.str "k", 2⟩,
   ⟨.op ")", 2⟩, ⟨.newline, 2⟩, ⟨.dedent, 3⟩, ⟨.kw "except", 3⟩,
   ⟨.name "LookupError", 3⟩, ⟨.name "as", 3⟩, ⟨.name "e", 3⟩,
   ⟨.op ":", 3⟩, ⟨.newline, 3⟩, ⟨.indent, 4⟩, ⟨.name "print", 4⟩,
   ⟨.op "(", 4⟩, ⟨.str "caught", 4⟩, ⟨.op ",", 4⟩, ⟨.name "e", 4⟩,
   ⟨.op ")", 4⟩, ⟨.newline, 4⟩, ⟨.dedent, 5⟩, ⟨.kw "finally", 5⟩,
   ⟨.op ":", 5⟩, ⟨.newline, 5⟩, ⟨.indent, 6⟩, ⟨.name "print", 6⟩,
   ⟨.op "(", 6⟩, ⟨.str "cleanup", 6⟩, ⟨.op ")", 6⟩, ⟨.newline, 6⟩,
   ⟨.dedent, 7⟩, ⟨.eof, 7⟩]

/-- Tokens of `divSrc`. -/
def divToks : List PTok :=
  [⟨.name "print", 1⟩, ⟨.op "(", 1⟩, ⟨.op "-", 1⟩, ⟨.int 7, 1⟩,
   ⟨.op "//", 1⟩, ⟨.int 2, 1⟩, ⟨.op ",", 1⟩, ⟨.op "-", 1⟩, ⟨.int 7, 1⟩,
   ⟨.op "%", 1⟩, ⟨.int 2, 1⟩, ⟨.op ",", 1⟩, ⟨.int 2, 1⟩, ⟨.op "**", 1⟩,
   ⟨.int 70, 1⟩, ⟨.op ")", 1⟩, ⟨.newline, 1⟩, ⟨.eof, 2⟩]

/-- Tokens of `mulNonnegSrc`. -/
def mulNonnegToks : List PTok :=
  [⟨.name "r", 1⟩, ⟨.op "=", 1⟩, ⟨.int 0, 1⟩, ⟨.newline, 1⟩,
   ⟨.name "i", 2⟩, ⟨.op "=", 2⟩, ⟨.int 0, 2⟩, ⟨.newline, 2⟩,
   ⟨.kw "while", 3⟩, ⟨.name "i", 3⟩, ⟨.op "<", 3⟩, ⟨.name "n", 3⟩,
   ⟨.op ":", 3⟩, ⟨.newline, 3⟩, ⟨.indent, 4⟩, ⟨.name "r", 4⟩,
   ⟨.op "=", 4⟩, ⟨.name "r", 4⟩, ⟨.op "+", 4⟩, ⟨.name "m", 4⟩,
   ⟨.newline, 4⟩, ⟨.name "i", 5⟩, ⟨.op "=", 5⟩, ⟨.name "i", 5⟩,
   ⟨.op "+", 5⟩, ⟨.int 1, 5⟩, ⟨.newline, 5⟩, ⟨.dedent, 6⟩, ⟨.eof, 6⟩]

/-- Tokens of `mul67Src`. -/
def mul67Toks : List PTok :=
  [⟨.name "m", 1⟩, ⟨.op "=", 1⟩, ⟨.int 6, 1⟩, ⟨.newline, 1⟩,
   ⟨.name "n", 2⟩, ⟨.op "=", 2⟩, ⟨.int 7, 2⟩, ⟨.newline, 2⟩,
   ⟨.name "r", 3⟩, ⟨.op "=", 3⟩, ⟨.int 0, 3⟩, ⟨.newline, 3⟩,
   ⟨.name "i", 4⟩, ⟨.op "=", 4⟩, ⟨.int 0, 4⟩, ⟨.newline, 4⟩,
   ⟨.kw "while", 5⟩, ⟨.name "i", 5⟩, ⟨.op "<", 5⟩, ⟨.name "n", 5⟩,
   ⟨.op ":", 5⟩, ⟨.newline, 5⟩, ⟨.indent, 6⟩, ⟨.name "r", 6⟩,
   ⟨.op "=", 6⟩, ⟨.name "r", 6⟩, ⟨.op "+", 6⟩, ⟨.name "m", 6⟩,
   ⟨.newline, 6⟩, ⟨.name "i", 7⟩, ⟨.op "=", 7⟩, ⟨.name "i", 7⟩,
   ⟨.op "+", 7⟩, ⟨.int 1, 7⟩, ⟨.newline, 7⟩, ⟨.dedent, 8⟩,
   ⟨.name "print", 8⟩, ⟨.op "(", 8⟩, ⟨.name "r", 8⟩, ⟨.op ")", 8⟩,
   ⟨.newline, 8⟩, ⟨.eof, 9⟩]

/-- Tokens of `absSrc`. -/
def absToks : List PTok :=
  [⟨.kw "if", 1⟩, ⟨.name "x", 1⟩, ⟨.op "<", 1⟩, ⟨.int 0, 1⟩, ⟨.op ":", 1⟩,
   ⟨.newline, 1⟩, ⟨.indent, 2⟩, ⟨.name "y", 2⟩, ⟨.op "=", 2⟩, ⟨.int 0, 2⟩,
   ⟨.op "-", 2⟩, ⟨.name "x", 2⟩, ⟨.newline, 2⟩, ⟨.dedent, 3⟩,
   ⟨.kw "else", 3⟩, ⟨.op ":", 3⟩, ⟨.newline, 3⟩, ⟨.indent, 4⟩,
   ⟨.name "y", 4⟩, ⟨.op "=", 4⟩, ⟨.name "x", 4⟩, ⟨.newline, 4⟩,
   ⟨.dedent, 5⟩, ⟨.eof, 5⟩]

/-- Tokens of `mulSrc`. -/
def mulToks : List PTok :=
  [⟨.kw "def", 1⟩, ⟨.name "sign", 1⟩, ⟨.op "(", 1⟩, ⟨.name "n", 1⟩,
   ⟨.op ")", 1⟩, ⟨.op ":", 1⟩, ⟨.newline, 1⟩, ⟨.indent, 2⟩, ⟨.kw "if", 2⟩,
   ⟨.name "n", 2⟩, ⟨.op "<", 2⟩, ⟨.int 0, 2⟩, ⟨.op ":", 2⟩, ⟨.newline, 2⟩,
   ⟨.indent, 3⟩, ⟨.kw "return", 3⟩, ⟨.op "-", 3⟩, ⟨.int 1, 3⟩,
   ⟨.newline, 3⟩, ⟨.dedent, 4⟩, ⟨.kw "elif", 4⟩, ⟨.name "n", 4⟩,
   ⟨.op ">", 4⟩, ⟨.int 0, 4⟩, ⟨.op ":", 4⟩, ⟨.newline, 4⟩, ⟨.indent, 5⟩,
   ⟨.kw "return", 5⟩, ⟨.int 1, 5⟩, ⟨.newline, 5⟩, ⟨.dedent, 6⟩,
   ⟨.kw "else", 6⟩, ⟨.op ":", 6⟩, ⟨.newline, 6⟩, ⟨.indent, 7⟩,
   ⟨.kw "return", 7⟩, ⟨.int 0, 7⟩, ⟨.newline, 7⟩, ⟨.dedent, 9⟩,
   ⟨.dedent, 9⟩, ⟨.kw "def", 9⟩, ⟨.name "mulNonneg", 9⟩, ⟨.op "(", 9⟩,
   ⟨.name "m", 9⟩, ⟨.op ",", 9⟩, ⟨.name "n", 9⟩, ⟨.op ")", 9⟩,
   ⟨.op ":", 9⟩, ⟨.newline, 9⟩, ⟨.indent, 10⟩, ⟨.name "r", 10⟩,
   ⟨.op "=", 10⟩, ⟨.int 0, 10⟩, ⟨.newline, 10⟩, ⟨.name "i", 11⟩,
   ⟨.op "=", 11⟩, ⟨.int 0, 11⟩, ⟨.newline, 11⟩, ⟨.kw "while", 12⟩,
   ⟨.name "i", 12⟩, ⟨.op "<", 12⟩, ⟨.name "n", 12⟩, ⟨.op ":", 12⟩,
   ⟨.newline, 12⟩, ⟨.indent, 13⟩, ⟨.name "r", 13⟩, ⟨.op "=", 13⟩,
   ⟨.name "r", 13⟩, ⟨.op "+", 13⟩, ⟨.name "m", 13⟩, ⟨.newline, 13⟩,
   ⟨.name "i", 14⟩, ⟨.op "=", 14⟩, ⟨.name "i", 14⟩, ⟨.op "+", 14⟩,
   ⟨.int 1, 14⟩, ⟨.newline, 14⟩, ⟨.dedent, 15⟩, ⟨.kw "return", 15⟩,
   ⟨.name "r", 15⟩, ⟨.newline, 15⟩, ⟨.dedent, 17⟩, ⟨.kw "def", 17⟩,
   ⟨.name "mul", 17⟩, ⟨.op "(", 17⟩, ⟨.name "m", 17⟩, ⟨.op ",", 17⟩,
   ⟨.name "n", 17⟩, ⟨.op ")", 17⟩, ⟨.op ":", 17⟩, ⟨.newline, 17⟩,
   ⟨.indent, 18⟩, ⟨.kw "return", 18⟩, ⟨.name "mulNonneg", 18⟩,
   ⟨.op "(", 18⟩, ⟨.name "m", 18⟩, ⟨.op "*", 18⟩, ⟨.name "sign", 18⟩,
   ⟨.op "(", 18⟩, ⟨.name "n", 18⟩, ⟨.op ")", 18⟩, ⟨.op ",", 18⟩,
   ⟨.name "abs", 18⟩, ⟨.op "(", 18⟩, ⟨.name "n", 18⟩, ⟨.op ")", 18⟩,
   ⟨.op ")", 18⟩, ⟨.newline, 18⟩, ⟨.dedent, 20⟩, ⟨.name "r", 20⟩,
   ⟨.op "=", 20⟩, ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.name "m", 20⟩,
   ⟨.op ",", 20⟩, ⟨.name "n", 20⟩, ⟨.op ")", 20⟩, ⟨.newline, 20⟩,
   ⟨.eof, 21⟩]

/-- Tokens of `mulRunSrc`. -/
def mulRunToks : List PTok :=
  [⟨.kw "def", 1⟩, ⟨.name "sign", 1⟩, ⟨.op "(", 1⟩, ⟨.name "n", 1⟩,
   ⟨.op ")", 1⟩, ⟨.op ":", 1⟩, ⟨.newline, 1⟩, ⟨.indent, 2⟩, ⟨.kw "if", 2⟩,
   ⟨.name "n", 2⟩, ⟨.op "<", 2⟩, ⟨.int 0, 2⟩, ⟨.op ":", 2⟩, ⟨.newline, 2⟩,
   ⟨.indent, 3⟩, ⟨.kw "return", 3⟩, ⟨.op "-", 3⟩, ⟨.int 1, 3⟩,
   ⟨.newline, 3⟩, ⟨.dedent, 4⟩, ⟨.kw "elif", 4⟩, ⟨.name "n", 4⟩,
   ⟨.op ">", 4⟩, ⟨.int 0, 4⟩, ⟨.op ":", 4⟩, ⟨.newline, 4⟩, ⟨.indent, 5⟩,
   ⟨.kw "return", 5⟩, ⟨.int 1, 5⟩, ⟨.newline, 5⟩, ⟨.dedent, 6⟩,
   ⟨.kw "else", 6⟩, ⟨.op ":", 6⟩, ⟨.newline, 6⟩, ⟨.indent, 7⟩,
   ⟨.kw "return", 7⟩, ⟨.int 0, 7⟩, ⟨.newline, 7⟩, ⟨.dedent, 9⟩,
   ⟨.dedent, 9⟩, ⟨.kw "def", 9⟩, ⟨.name "mulNonneg", 9⟩, ⟨.op "(", 9⟩,
   ⟨.name "m", 9⟩, ⟨.op ",", 9⟩, ⟨.name "n", 9⟩, ⟨.op ")", 9⟩,
   ⟨.op ":", 9⟩, ⟨.newline, 9⟩, ⟨.indent, 10⟩, ⟨.name "r", 10⟩,
   ⟨.op "=", 10⟩, ⟨.int 0, 10⟩, ⟨.newline, 10⟩, ⟨.name "i", 11⟩,
   ⟨.op "=", 11⟩, ⟨.int 0, 11⟩, ⟨.newline, 11⟩, ⟨.kw "while", 12⟩,
   ⟨.name "i", 12⟩, ⟨.op "<", 12⟩, ⟨.name "n", 12⟩, ⟨.op ":", 12⟩,
   ⟨.newline, 12⟩, ⟨.indent, 13⟩, ⟨.name "r", 13⟩, ⟨.op "=", 13⟩,
   ⟨.name "r", 13⟩, ⟨.op "+", 13⟩, ⟨.name "m", 13⟩, ⟨.newline, 13⟩,
   ⟨.name "i", 14⟩, ⟨.op "=", 14⟩, ⟨.name "i", 14⟩, ⟨.op "+", 14⟩,
   ⟨.int 1, 14⟩, ⟨.newline, 14⟩, ⟨.dedent, 15⟩, ⟨.kw "return", 15⟩,
   ⟨.name "r", 15⟩, ⟨.newline, 15⟩, ⟨.dedent, 17⟩, ⟨.kw "def", 17⟩,
   ⟨.name "mul", 17⟩, ⟨.op "(", 17⟩, ⟨.name "m", 17⟩, ⟨.op ",", 17⟩,
   ⟨.name "n", 17⟩, ⟨.op ")", 17⟩, ⟨.op ":", 17⟩, ⟨.newline, 17⟩,
   ⟨.indent, 18⟩, ⟨.kw "return", 18⟩, ⟨.name "mulNonneg", 18⟩,
   ⟨.op "(", 18⟩, ⟨.name "m", 18⟩, ⟨.op "*", 18⟩, ⟨.name "sign", 18⟩,
   ⟨.op "(", 18⟩, ⟨.name "n", 18⟩, ⟨.op ")", 18⟩, ⟨.op ",", 18⟩,
   ⟨.name "abs", 18⟩, ⟨.op "(", 18⟩, ⟨.name "n", 18⟩, ⟨.op ")", 18⟩,
   ⟨.op ")", 18⟩, ⟨.newline, 18⟩, ⟨.dedent, 20⟩, ⟨.name "print", 20⟩,
   ⟨.op "(", 20⟩, ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.int 6, 20⟩,
   ⟨.op ",", 20⟩, ⟨.int 7, 20⟩, ⟨.op ")", 20⟩, ⟨.op ",", 20⟩,
   ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.int 6, 20⟩, ⟨.op ",", 20⟩,
   ⟨.op "-", 20⟩, ⟨.int 7, 20⟩, ⟨.op ")", 20⟩, ⟨.op ",", 20⟩,
   ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.op "-", 20⟩, ⟨.int 6, 20⟩,
   ⟨.op ",", 20⟩, ⟨.int 7, 20⟩, ⟨.op ")", 20⟩, ⟨.op ",", 20⟩,
   ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.op "-", 20⟩, ⟨.int 6, 20⟩,
   ⟨.op ",", 20⟩, ⟨.op "-", 20⟩, ⟨.int 7, 20⟩, ⟨.op ")", 20⟩,
   ⟨.op ")", 20⟩, ⟨.newline, 20⟩, ⟨.eof, 21⟩]

/-- Tokens of `mulZeroSrc`. -/
def mulZeroToks : List PTok :=
  [⟨.kw "def", 1⟩, ⟨.name "sign", 1⟩, ⟨.op "(", 1⟩, ⟨.name "n", 1⟩,
   ⟨.op ")", 1⟩, ⟨.op ":", 1⟩, ⟨.newline, 1⟩, ⟨.indent, 2⟩, ⟨.kw "if", 2⟩,
   ⟨.name "n", 2⟩, ⟨.op "<", 2⟩, ⟨.int 0, 2⟩, ⟨.op ":", 2⟩, ⟨.newline, 2⟩,
   ⟨.indent, 3⟩, ⟨.kw "return", 3⟩, ⟨.op "-", 3⟩, ⟨.int 1, 3⟩,
   ⟨.newline, 3⟩, ⟨.dedent, 4⟩, ⟨.kw "elif", 4⟩, ⟨.name "n", 4⟩,
   ⟨.op ">", 4⟩, ⟨.int 0, 4⟩, ⟨.op ":", 4⟩, ⟨.newline, 4⟩, ⟨.indent, 5⟩,
   ⟨.kw "return", 5⟩, ⟨.int 1, 5⟩, ⟨.newline, 5⟩, ⟨.dedent, 6⟩,
   ⟨.kw "else", 6⟩, ⟨.op ":", 6⟩, ⟨.newline, 6⟩, ⟨.indent, 7⟩,
   ⟨.kw "return", 7⟩, ⟨.int 0, 7⟩, ⟨.newline, 7⟩, ⟨.dedent, 9⟩,
   ⟨.dedent, 9⟩, ⟨.kw "def", 9⟩, ⟨.name "mulNonneg", 9⟩, ⟨.op "(", 9⟩,
   ⟨.name "m", 9⟩, ⟨.op ",", 9⟩, ⟨.name "n", 9⟩, ⟨.op ")", 9⟩,
   ⟨.op ":", 9⟩, ⟨.newline, 9⟩, ⟨.indent, 10⟩, ⟨.name "r", 10⟩,
   ⟨.op "=", 10⟩, ⟨.int 0, 10⟩, ⟨.newline, 10⟩, ⟨.name "i", 11⟩,
   ⟨.op "=", 11⟩, ⟨.int 0, 11⟩, ⟨.newline, 11⟩, ⟨.kw "while", 12⟩,
   ⟨.name "i", 12⟩, ⟨.op "<", 12⟩, ⟨.name "n", 12⟩, ⟨.op ":", 12⟩,
   ⟨.newline, 12⟩, ⟨.indent, 13⟩, ⟨.name "r", 13⟩, ⟨.op "=", 13⟩,
   ⟨.name "r", 13⟩, ⟨.op "+", 13⟩, ⟨.name "m", 13⟩, ⟨.newline, 13⟩,
   ⟨.name "i", 14⟩, ⟨.op "=", 14⟩, ⟨.name "i", 14⟩, ⟨.op "+", 14⟩,
   ⟨.int 1, 14⟩, ⟨.newline, 14⟩, ⟨.dedent, 15⟩, ⟨.kw "return", 15⟩,
   ⟨.name "r", 15⟩, ⟨.newline, 15⟩, ⟨.dedent, 17⟩, ⟨.kw "def", 17⟩,
   ⟨.name "mul", 17⟩, ⟨.op "(", 17⟩, ⟨.name "m", 17⟩, ⟨.op ",", 17⟩,
   ⟨.name "n", 17⟩, ⟨.op ")", 17⟩, ⟨.op ":", 17⟩, ⟨.newline, 17⟩,
   ⟨.indent, 18⟩, ⟨.kw "return", 18⟩, ⟨.name "mulNonneg", 18⟩,
   ⟨.op "(", 18⟩, ⟨.name "m", 18⟩, ⟨.op "*", 18⟩, ⟨.name "sign", 18⟩,
   ⟨.op "(", 18⟩, ⟨.name "n", 18⟩, ⟨.op ")", 18⟩, ⟨.op ",", 18⟩,
   ⟨.name "abs", 18⟩, ⟨.op "(", 18⟩, ⟨.name "n", 18⟩, ⟨.op ")", 18⟩,
   ⟨.op ")", 18⟩, ⟨.newline, 18⟩, ⟨.dedent, 20⟩, ⟨.name "print", 20⟩,
   ⟨.op "(", 20⟩, ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.int 5, 20⟩,
   ⟨.op ",", 20⟩, ⟨.int 0, 20⟩, ⟨.op ")", 20⟩, ⟨.op ",", 20⟩,
   ⟨.name "mul", 20⟩, ⟨.op "(", 20⟩, ⟨.int 0, 20⟩, ⟨.op ",", 20⟩,
   ⟨.op "-", 20⟩, ⟨.int 3, 20⟩, ⟨.op ")", 20⟩, ⟨.op ")", 20⟩,
   ⟨.newline, 20⟩, ⟨.eof, 21⟩]

end SnakeFight
