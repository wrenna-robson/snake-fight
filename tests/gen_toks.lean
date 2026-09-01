/-
Regenerates `SnakeFight/ExampleToks.lean`, the token lists that let the
source-to-AST proofs in `SnakeFight.Examples` reduce in the kernel.

  lake env lean tests/gen_toks.lean > SnakeFight/ExampleToks.lean

The output is not trusted: `SnakeFight.Examples` proves `tokenize src = .ok
<list>` by `rfl`, so a stale or wrong list fails the build rather than making a
proof pass.
-/
import SnakeFight.Examples

namespace SnakeFight.GenToks

/-- Render a token as the Lean syntax that denotes it. -/
def tokSyn : Tok → String
  | .name s  => s!".name {s.quote}"
  | .kw s    => s!".kw {s.quote}"
  | .op s    => s!".op {s.quote}"
  | .str s   => s!".str {s.quote}"
  | .int i   => if i < 0 then s!".int ({i})" else s!".int {i}"
  | .newline => ".newline"
  | .indent  => ".indent"
  | .dedent  => ".dedent"
  | .eof     => ".eof"

/-- Render a token with its line number. -/
def ptokSyn (t : PTok) : String := s!"⟨{tokSyn t.tok}, {t.line}⟩"

/-- Pack rendered tokens into lines of at most `width` columns, never splitting
a token across lines. -/
def pack (items : List String) (width : Nat := 74) : String :=
  String.intercalate "\n" (go items "  [" [])
where
  go : List String → String → List String → List String
    | [], cur, acc => acc ++ [cur ++ "]"]
    | it :: rest, cur, acc =>
      let piece := it ++ (if rest.isEmpty then "" else ",")
      let open' := cur.endsWith "["
      let cand := if open' then cur ++ piece else cur ++ " " ++ piece
      if cand.length > width && !open' then go rest ("   " ++ piece) (acc ++ [cur])
      else go rest cand acc

/-- The examples, paired with the names used in `ExampleToks.lean`. -/
def examples : List (String × String) :=
  [("add", addSrc), ("concat", concatSrc), ("alias", aliasSrc),
   ("adder", adderSrc), ("exc", excSrc), ("div", divSrc),
   ("mulNonneg", mulNonnegSrc), ("mul67", mul67Src), ("abs", absSrc),
   ("mul", mulSrc), ("mulRun", mulRunSrc), ("mulZero", mulZeroSrc)]

def header : String :=
  "import SnakeFight.Lexer\n\n/-!\n# Token lists for the worked examples\n\n\
  `PState` is a token array plus a `Nat` cursor, so every step of the parser\n\
  reads `st.toks[st.pos]?`.  Reduction zeta-expands `let`, so inside `parse src`\n\
  that array is the *unreduced* `tokenize src` term and each of those reads\n\
  re-derives the whole token list from the source.  Reducing `parse src` in one\n\
  go therefore reruns the lexer once per cursor read and never finishes, even\n\
  though the lexer and the parser each reduce in well under a second.\n\n\
  Naming the token list breaks that fusion.  `SnakeFight.Examples` proves\n\
  `tokenize src = .ok <the list named here>` and then runs the parser on the\n\
  named list, so each half is reduced exactly once.\n\n\
  These lists are generated from the example sources by `tests/gen_toks.lean`;\n\
  regenerate them if an example changes.  A wrong list here cannot make a proof\n\
  pass -- the `tokenize src = .ok ...` step is itself checked by the kernel, so a\n\
  mismatch fails the build.\n-/\n\nnamespace SnakeFight\n"

def main : IO Unit := do
  IO.print header
  for (n, s) in examples do
    match tokenize s with
    | .error e => throw (IO.userError s!"{n}Src does not lex: {e}")
    | .ok l =>
      IO.println ""
      IO.println s!"/-- Tokens of `{n}Src`. -/"
      IO.println s!"def {n}Toks : List PTok :="
      IO.println (pack (l.map ptokSyn))
  IO.println ""
  IO.println "end SnakeFight"

end SnakeFight.GenToks

#eval SnakeFight.GenToks.main
