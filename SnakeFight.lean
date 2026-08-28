-- SnakeFight: a Python interpreter written in Lean 4, with a program logic for
-- reasoning about the programs it runs.  See README.md for an overview.

-- Syntax and the front end.
import SnakeFight.Ast
import SnakeFight.Lexer
import SnakeFight.Parser

-- Values, the shared semantic kernel, and the interpreter.
import SnakeFight.Value
import SnakeFight.Kernel
import SnakeFight.Builtins
import SnakeFight.Interp

-- Reasoning: a pure specification of expressions, a Hoare logic, and helpers.
import SnakeFight.Pure
import SnakeFight.Hoare
import SnakeFight.Reason

-- Machine-checked examples and the CPython-derived test suite.
import SnakeFight.Examples
import SnakeFight.Tests
