import SnakeFight.Hoare

/-!
# Reasoning helpers

`evalP` and the kernel operations are defined for all of Python's dynamic
behaviour, which makes them clumsy to unfold by hand.  This module packages the
integer fragment -- the part loop invariants are usually about -- into lemmas
with clean statements, so that an example proof mentions Python semantics only
through names like `evalP_add` and `Truthy_lt`.
-/

namespace SnakeFight

@[simp] theorem evalP_int_lit (s : State) (i : Int) : evalP s (.int i) = some (.int i) := rfl
@[simp] theorem evalP_bool_lit (s : State) (b : Bool) : evalP s (.bool b) = some (.bool b) := rfl
@[simp] theorem evalP_name_eq (s : State) (x : String) :
    evalP s (.name x) = s.lookupName x := rfl

@[simp] theorem truthy_bool (h : Array Obj) (b : Bool) : (Value.bool b).truthy h = b := rfl

/-! ## Arithmetic -/

theorem evalP_add {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.binop .add x y) = some (.int (a + b)) := by
  simp [evalP, hx, hy, binOpK, asInt, intBinOpK]

theorem evalP_sub {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.binop .sub x y) = some (.int (a - b)) := by
  simp [evalP, hx, hy, binOpK, asInt, intBinOpK]

theorem evalP_mul {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.binop .mul x y) = some (.int (a * b)) := by
  simp [evalP, hx, hy, binOpK, asInt, intBinOpK]

theorem evalP_neg {s : State} {x : Expr} {a : Int} (hx : evalP s x = some (.int a)) :
    evalP s (.unop .neg x) = some (.int (-a)) := by
  simp [evalP, hx, unOpK, asInt]

/-! ## Comparisons

Python comparisons chain, so `x < y` is a one-element `Expr.compare`. -/

theorem evalP_lt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.compare x [(.lt, y)]) = some (.bool (decide (a < b))) := by
  simp only [evalP, hx, evalPChain, hy, cmpK, cmpCore, asInt]
  by_cases h : a < b
  · simp [h]
  · simp [h]
    by_cases h2 : a = b <;> simp [h2] <;> omega

theorem evalP_le {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.compare x [(.le, y)]) = some (.bool (decide (a ≤ b))) := by
  simp only [evalP, hx, evalPChain, hy, cmpK, cmpCore, asInt]
  by_cases h : a < b
  · have hle : a ≤ b := Int.le_of_lt h
    simp [h, hle]
  · by_cases h2 : a = b <;> simp [h, h2] <;> omega

theorem evalP_gt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.compare x [(.gt, y)]) = some (.bool (decide (b < a))) := by
  simp only [evalP, hx, evalPChain, hy, cmpK, cmpCore, asInt]
  by_cases h : a < b
  · simp [h]; omega
  · by_cases h2 : a = b <;> simp [h, h2] <;> omega

theorem evalP_eqInt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    evalP s (.compare x [(.eq, y)]) = some (.bool (decide (a = b))) := by
  simp only [evalP, hx, evalPChain, hy, cmpK, isSimple, eqCore]
  by_cases h : a = b <;> simp [h]

/-! ## Truth of a comparison -/

theorem Truthy_of_bool {s : State} {e : Expr} {b : Bool} (h : evalP s e = some (.bool b))
    (hb : b = true) : Truthy e s := ⟨.bool b, h, by simp [hb]⟩

theorem Falsy_of_bool {s : State} {e : Expr} {b : Bool} (h : evalP s e = some (.bool b))
    (hb : b = false) : Falsy e s := ⟨.bool b, h, by simp [hb]⟩

theorem of_Truthy_bool {s : State} {e : Expr} {b : Bool} (h : evalP s e = some (.bool b))
    (ht : Truthy e s) : b = true := by
  obtain ⟨v, hv, htv⟩ := ht
  rw [h] at hv
  cases hv
  simpa using htv

theorem of_Falsy_bool {s : State} {e : Expr} {b : Bool} (h : evalP s e = some (.bool b))
    (hf : Falsy e s) : b = false := by
  obtain ⟨v, hv, hfv⟩ := hf
  rw [h] at hv
  cases hv
  simpa using hfv

/-- `x < y` is true exactly when it should be. -/
theorem Truthy_lt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    Truthy (.compare x [(.lt, y)]) s ↔ a < b := by
  constructor
  · intro ht
    have := of_Truthy_bool (evalP_lt hx hy) ht
    simpa using this
  · intro hab
    exact Truthy_of_bool (evalP_lt hx hy) (by simp [hab])

/-- and `x < y` is false exactly when it should be. -/
theorem Falsy_lt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    Falsy (.compare x [(.lt, y)]) s ↔ ¬ a < b := by
  constructor
  · intro hf
    have := of_Falsy_bool (evalP_lt hx hy) hf
    simpa using this
  · intro hab
    exact Falsy_of_bool (evalP_lt hx hy) (by simp [hab])

/-- `x > y` is true exactly when it should be. -/
theorem Truthy_gt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    Truthy (.compare x [(.gt, y)]) s ↔ b < a := by
  constructor
  · intro ht
    have := of_Truthy_bool (evalP_gt hx hy) ht
    simpa using this
  · intro hab
    exact Truthy_of_bool (evalP_gt hx hy) (by simp [hab])

/-- and `x > y` is false exactly when it should be. -/
theorem Falsy_gt {s : State} {x y : Expr} {a b : Int}
    (hx : evalP s x = some (.int a)) (hy : evalP s y = some (.int b)) :
    Falsy (.compare x [(.gt, y)]) s ↔ ¬ b < a := by
  constructor
  · intro hf
    have := of_Falsy_bool (evalP_gt hx hy) hf
    simpa using this
  · intro hab
    exact Falsy_of_bool (evalP_gt hx hy) (by simp [hab])

/-! ## Variables

Inside a plain scope -- module level, or a frame with no `global` declaration in
force -- reading and writing a variable is a plain association-list update, and
these two lemmas are all a proof needs.  Taking `plainScope` rather than
`s.frame = none` is what lets one verified block be used both at module level and
inside a function body. -/

theorem lookup_set_self {s : State} (hf : s.plainScope) (x : String) (v : Value) :
    (s.setVar x v).lookupName x = some v :=
  State.lookupName_setVar_self s x v hf

theorem lookup_set_other {s : State} (hf : s.plainScope) {x y : String} (hxy : x ≠ y)
    (v : Value) : (s.setVar x v).lookupName y = s.lookupName y :=
  State.lookupName_setVar_of_ne s hxy v hf

end SnakeFight
