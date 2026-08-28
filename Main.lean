import SnakeFight

open SnakeFight

def usage : String :=
"snake-fight -- a Python interpreter written in Lean 4

usage:
  snake-fight FILE.py            run a file
  snake-fight -c 'CODE'          run a string
  snake-fight --ast FILE.py      print the parsed AST
  snake-fight test               run the interpreter test suite
  snake-fight --fuel N ...       set the step budget (default 2000000)

SnakeFight implements a subset of Python: see README.md."

/-- Print a program's output, then report how it ended. -/
def report (fuel : Nat) (src : String) : IO UInt32 := do
  match parse src with
  | .error e => do
    IO.eprintln s!"SyntaxError: {e}"
    pure 2
  | .ok prog =>
    match runOutcome fuel prog with
    | .ok out => do
      out.forM IO.println
      pure 0
    | .error out msg => do
      out.forM IO.println
      IO.eprintln "Traceback (most recent call last):"
      IO.eprintln s!"  {msg}"
      pure 1
    | .timeout out => do
      out.forM IO.println
      IO.eprintln s!"snake-fight: ran out of fuel after {fuel} steps"
      pure 3

/-- Print the AST of a program. -/
def dumpAst (src : String) : IO UInt32 := do
  match parse src with
  | .error e => do IO.eprintln s!"SyntaxError: {e}"; pure 2
  | .ok prog => do
    for s in prog do
      IO.println (repr s).pretty
    pure 0

/-- Split off a leading `--fuel N`. -/
def takeFuel : List String → Nat × List String
  | "--fuel" :: n :: rest => (n.toNat?.getD defaultFuel, rest)
  | args => (defaultFuel, args)

def main (argv : List String) : IO UInt32 := do
  let (fuel, args) := takeFuel argv
  match args with
  | [] => do IO.println usage; pure 0
  | ["--help"] | ["-h"] => do IO.println usage; pure 0
  | ["test"] => runTests
  | ["-c", src] => report fuel src
  | ["--ast", path] => do dumpAst (← IO.FS.readFile path)
  | [path] =>
    if path.startsWith "-" then do
      IO.eprintln s!"snake-fight: unknown option {path}"
      IO.eprintln usage
      pure 2
    else do report fuel (← IO.FS.readFile path)
  | _ => do
    IO.eprintln usage
    pure 2
