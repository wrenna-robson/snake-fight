import SnakeFight.Interp

/-!
# A specification-level evaluator, and its agreement with the interpreter

To state a loop invariant one needs to talk about the value of a Python
expression in a given state.  Doing that with `evalExpr` directly is awkward: it
is a state transformer, it takes a fuel budget, and it can allocate.

`evalP` is the alternative: a plain function `State → Expr → Option Value` that
models the *effect-free* fragment of the language.  It answers `none` whenever an
expression is outside that fragment (a call, a list display, a slice) or whenever
evaluating it would raise.

The link between the two is `evalP_agrees`:

> if `evalP s e = some v`, then any successful run of `evalExpr fuel e s`
> produces exactly `v` and leaves the state alone.

Note the direction.  `evalP` never has to be complete -- it is allowed to give
up -- but where it does commit to a value, the interpreter is obliged to agree.
That is what makes it usable as the assertion language of a program logic, and
it also means a Hoare rule must *prove* `evalP` is defined, which in a
dynamically typed language is exactly the obligation "these operands really do
have compatible types here".

Both sides call the same kernel operations (`binOpK`, `cmpK`, `indexK`, ...), so
the proof is a structural induction on fuel with no semantic gap to bridge.
-/

namespace SnakeFight

mutual

/-- Specification-level evaluation of the effect-free fragment of Python.
`none` means "outside the fragment, or raises". -/
def evalP (s : State) : Expr → Option Value
  | .int i => some (.int i)
  | .str t => some (.str t)
  | .bool b => some (.bool b)
  | .none => some Value.none
  | .name x => s.lookupName x
  | .unop op e =>
    match evalP s e with
    | some v => match unOpK s.heap op v with
      | some (.val r) => some r
      | _ => Option.none
    | Option.none => Option.none
  | .binop op l r =>
    match evalP s l, evalP s r with
    | some a, some b => match binOpK op a b with
      | some (.val v) => some v
      | _ => Option.none
    | _, _ => Option.none
  | .compare l rest =>
    match evalP s l with
    | some a => evalPChain s a rest
    | Option.none => Option.none
  | .andE l r =>
    match evalP s l with
    | some a => if a.truthy s.heap then evalP s r else some a
    | Option.none => Option.none
  | .orE l r =>
    match evalP s l with
    | some a => if a.truthy s.heap then some a else evalP s r
    | Option.none => Option.none
  | .ifE c t f =>
    match evalP s c with
    | some cv => if cv.truthy s.heap then evalP s t else evalP s f
    | Option.none => Option.none
  | .tupleE es =>
    match evalPs s es with
    | some vs => some (.tuple vs)
    | Option.none => Option.none
  | .subscript o i =>
    match evalP s o, evalP s i with
    | some ov, some iv => match indexK s.heap ov iv with
      | some (.val v) => some v
      | _ => Option.none
    | _, _ => Option.none
  -- Calls, list and dict displays, slices, comprehensions, attributes and
  -- lambdas all either allocate, mutate, or run user code.
  | _ => Option.none

/-- `evalP` over a list of expressions. -/
def evalPs (s : State) : List Expr → Option (List Value)
  | [] => some []
  | e :: es =>
    match evalP s e, evalPs s es with
    | some v, some vs => some (v :: vs)
    | _, _ => Option.none

/-- The tail of a chained comparison, mirroring `evalCmpChain`. -/
def evalPChain (s : State) (prev : Value) : List (CmpOp × Expr) → Option Value
  | [] => some (.bool true)
  | (op, e) :: rest =>
    match evalP s e with
    | some cur =>
      match cmpK op prev cur with
      | some (.val r) =>
        if r.truthy s.heap then
          match rest with
          | [] => some r
          | _ => evalPChain s cur rest
        else some (.bool false)
      | _ => Option.none
    | Option.none => Option.none

end

/-! ## Unfolding lemmas for the interpreter

Each of these holds by `rfl`; naming them keeps the proofs below readable. -/

@[simp] theorem evalExpr_zero (e : Expr) (s : State) : evalExpr 0 e s = .timeout s := rfl
@[simp] theorem evalExprs_zero (e : Expr) (es : List Expr) (s : State) :
    evalExprs 0 (e :: es) s = .timeout s := rfl
@[simp] theorem evalCmpChain_zero (v : Value) (p : CmpOp × Expr) (rest : List (CmpOp × Expr))
    (s : State) : evalCmpChain 0 v (p :: rest) s = .timeout s := rfl

theorem evalExpr_int (f : Nat) (i : Int) (s : State) :
    evalExpr (f + 1) (.int i) s = .ok (.int i) s := rfl
theorem evalExpr_str (f : Nat) (t : String) (s : State) :
    evalExpr (f + 1) (.str t) s = .ok (.str t) s := rfl
theorem evalExpr_bool (f : Nat) (b : Bool) (s : State) :
    evalExpr (f + 1) (.bool b) s = .ok (.bool b) s := rfl
theorem evalExpr_none (f : Nat) (s : State) :
    evalExpr (f + 1) .none s = .ok Value.none s := rfl
theorem evalExpr_name (f : Nat) (x : String) (s : State) :
    evalExpr (f + 1) (.name x) s = lookupOrRaise x s := rfl

@[simp] theorem evalExprs_nil (f : Nat) (s : State) : evalExprs f [] s = .ok [] s := by
  cases f <;> rfl

@[simp] theorem evalCmpChain_nil (f : Nat) (v : Value) (s : State) :
    evalCmpChain f v [] s = .ok (.bool true) s := by
  cases f <;> rfl

/-! Each compound case is unfolded to its `do` block, which holds by `rfl`.
Combined with the `@[simp]` lemma `M.run_bind`, `simp only` then turns it into a
`match` on the sub-result, which is what the proofs case on. -/

theorem evalExpr_unop (f : Nat) (op : UnOp) (e : Expr) (s : State) :
    evalExpr (f + 1) (.unop op e) s =
      (do
        let v ← evalExpr f e
        let h ← getHeap
        match unOpK h op v with
        | some k => ofKRes k
        | Option.none => typeError s!"bad operand type for unary {op.symbol}: '{v.typeName h}'") s :=
  rfl

theorem evalExpr_binop (f : Nat) (op : BinOp) (l r : Expr) (s : State) :
    evalExpr (f + 1) (.binop op l r) s =
      (do
        let a ← evalExpr f l
        let b ← evalExpr f r
        applyBinOp op a b) s := rfl

theorem evalExpr_compare (f : Nat) (l : Expr) (rest : List (CmpOp × Expr)) (s : State) :
    evalExpr (f + 1) (.compare l rest) s =
      (do
        let a ← evalExpr f l
        evalCmpChain f a rest) s := rfl

theorem evalExpr_andE (f : Nat) (l r : Expr) (s : State) :
    evalExpr (f + 1) (.andE l r) s =
      (do
        let a ← evalExpr f l
        let h ← getHeap
        if a.truthy h then evalExpr f r else pure a) s := rfl

theorem evalExpr_orE (f : Nat) (l r : Expr) (s : State) :
    evalExpr (f + 1) (.orE l r) s =
      (do
        let a ← evalExpr f l
        let h ← getHeap
        if a.truthy h then pure a else evalExpr f r) s := rfl

theorem evalExpr_ifE (f : Nat) (c t e : Expr) (s : State) :
    evalExpr (f + 1) (.ifE c t e) s =
      (do
        let cv ← evalExpr f c
        let h ← getHeap
        if cv.truthy h then evalExpr f t else evalExpr f e) s := rfl

theorem evalExpr_tupleE (f : Nat) (es : List Expr) (s : State) :
    evalExpr (f + 1) (.tupleE es) s =
      (do
        let vs ← evalExprs f es
        pure (Value.tuple vs)) s := rfl

theorem evalExprs_cons (f : Nat) (e : Expr) (es : List Expr) (s : State) :
    evalExprs (f + 1) (e :: es) s =
      (do
        let v ← evalExpr f e
        let vs ← evalExprs f es
        pure (v :: vs)) s := rfl

theorem evalCmpChain_cons (f : Nat) (prev : Value) (op : CmpOp) (e : Expr)
    (rest : List (CmpOp × Expr)) (s : State) :
    evalCmpChain (f + 1) prev ((op, e) :: rest) s =
      (do
        let cur ← evalExpr f e
        let r ← applyCmp op prev cur
        let h ← getHeap
        if r.truthy h then
          match rest with
          | [] => pure r
          | _ :: _ => evalCmpChain f cur rest
        else pure (.bool false)) s := by
  cases rest <;> rfl

theorem evalExpr_subscript (f : Nat) (o i : Expr) (s : State) :
    evalExpr (f + 1) (.subscript o i) s =
      (do
        let ov ← evalExpr f o
        let iv ← evalExpr f i
        let h ← getHeap
        match indexK h ov iv with
        | some k => ofKRes k
        | Option.none =>
          match ov with
          | .ref a =>
            match h[a]? with
            | some (.dict _) => typeError s!"unhashable type: '{iv.typeName h}'"
            | _ => typeError s!"'{ov.typeName h}' indices must be integers"
          | _ => typeError s!"'{ov.typeName h}' object is not subscriptable") s := rfl

/-- A kernel value answer determines `applyBinOp`. -/
theorem applyBinOp_val {op : BinOp} {a b v : Value} (h : binOpK op a b = some (.val v))
    (s : State) : applyBinOp op a b s = .ok v s := by
  simp [applyBinOp, h, ofKRes]

/-- A kernel value answer determines `applyCmp`. -/
theorem applyCmp_val {op : CmpOp} {a b v : Value} (h : cmpK op a b = some (.val v))
    (s : State) : applyCmp op a b s = .ok v s := by
  simp [applyCmp, h, ofKRes]

/-- A successful name lookup determines `lookupOrRaise`. -/
theorem lookupOrRaise_of_eq {x : String} {s : State} {v : Value} (h : s.lookupName x = some v) :
    lookupOrRaise x s = .ok v s := by
  simp [lookupOrRaise, h]


/-! ## Agreement -/

/-- The workhorse: if the first half of a `bind` agrees with a known pure value
`a` and leaves the state alone, the whole `bind` reduces to its continuation
applied to `a` in the original state. -/
theorem bind_agree {α β} {m : M α} {k : α → M β} {s : State} {a : α}
    (hm : ∀ a' s', m s = .ok a' s' → a' = a ∧ s' = s)
    {b' : β} {s' : State} (hr : (m >>= k) s = .ok b' s') :
    k a s = .ok b' s' := by
  simp only [M.run_bind] at hr
  cases hms : m s with
  | ok a1 s1 =>
    obtain ⟨rfl, rfl⟩ := hm a1 s1 hms
    rw [hms] at hr
    exact hr
  | exn e s1 => rw [hms] at hr; simp at hr
  | timeout s1 => rw [hms] at hr; simp at hr

/-- A computation that is already known to succeed without touching the state
satisfies `bind_agree`'s hypothesis. -/
theorem ok_agree {α} {m : M α} {s : State} {a : α} (h : m s = .ok a s) :
    ∀ a' s', m s = .ok a' s' → a' = a ∧ s' = s := by
  intro a' s' h'
  rw [h] at h'
  simp at h'
  exact ⟨h'.1.symm, h'.2.symm⟩

theorem getHeap_ok (s : State) : getHeap s = .ok s.heap s := rfl

/-- **The interpreter respects the specification-level evaluator.**

Stated for all three mutually recursive pieces at once, since they call each
other.  See `evalP_agrees` for the usable corollary. -/
theorem agree (f : Nat) :
    (∀ (e : Expr) (s s' : State) (v v' : Value),
      evalP s e = some v → evalExpr f e s = .ok v' s' → v' = v ∧ s' = s)
    ∧ (∀ (es : List Expr) (s s' : State) (vs vs' : List Value),
      evalPs s es = some vs → evalExprs f es s = .ok vs' s' → vs' = vs ∧ s' = s)
    ∧ (∀ (prev : Value) (rest : List (CmpOp × Expr)) (s s' : State) (v v' : Value),
      evalPChain s prev rest = some v → evalCmpChain f prev rest s = .ok v' s' →
        v' = v ∧ s' = s) := by
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e s s' v v' _ hr; simp at hr
    · intro es s s' vs vs' hp hr
      cases es with
      | nil => simp only [evalPs] at hp; simp only [evalExprs_nil] at hr; simp_all
      | cons e es => simp at hr
    · intro prev rest s s' v v' hp hr
      cases rest with
      | nil => simp only [evalPChain] at hp; simp only [evalCmpChain_nil] at hr; simp_all
      | cons p rest => simp at hr
  | succ f ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- ### Expressions
    · intro e s s' v v' hp hr
      cases e with
      | int i =>
        simp only [evalP] at hp
        rw [evalExpr_int] at hr
        simp_all
      | str t =>
        simp only [evalP] at hp
        rw [evalExpr_str] at hr
        simp_all
      | bool b =>
        simp only [evalP] at hp
        rw [evalExpr_bool] at hr
        simp_all
      | none =>
        simp only [evalP] at hp
        rw [evalExpr_none] at hr
        simp_all
      | name x =>
        simp only [evalP] at hp
        rw [evalExpr_name, lookupOrRaise_of_eq hp] at hr
        simp at hr
        exact ⟨hr.1.symm, hr.2.symm⟩
      | unop op e =>
        simp only [evalP] at hp
        rw [evalExpr_unop] at hr
        cases hpe : evalP s e with
        | none => simp [hpe] at hp
        | some a =>
          simp only [hpe] at hp
          cases hk : unOpK s.heap op a with
          | none => simp [hk] at hp
          | some k =>
            cases k with
            | err t m => simp [hk] at hp
            | errV t as => simp [hk] at hp
            | val w =>
              simp only [hk] at hp
              simp only [Option.some.injEq] at hp
              have h1 := bind_agree (fun a' s'' h => ih1 e s s'' a a' hpe h) hr
              have h2 := bind_agree (ok_agree (getHeap_ok s)) h1
              simp only [hk] at h2
              simp only [ofKRes, M.run_pure, Res.ok.injEq] at h2
              exact ⟨by rw [← h2.1, hp], h2.2.symm⟩
      | binop op l r =>
        simp only [evalP] at hp
        rw [evalExpr_binop] at hr
        cases hpl : evalP s l with
        | none => simp [hpl] at hp
        | some a =>
          cases hpr : evalP s r with
          | none => simp [hpl, hpr] at hp
          | some b =>
            simp only [hpl, hpr] at hp
            cases hk : binOpK op a b with
            | none => simp [hk] at hp
            | some k =>
              cases k with
              | err t m => simp [hk] at hp
              | errV t as => simp [hk] at hp
              | val w =>
                simp only [hk] at hp
                simp only [Option.some.injEq] at hp
                have h1 := bind_agree (fun a' s'' h => ih1 l s s'' a a' hpl h) hr
                have h2 := bind_agree (fun b' s'' h => ih1 r s s'' b b' hpr h) h1
                rw [applyBinOp_val hk] at h2
                simp only [Res.ok.injEq] at h2
                exact ⟨by rw [← h2.1, hp], h2.2.symm⟩
      | compare l rest =>
        simp only [evalP] at hp
        rw [evalExpr_compare] at hr
        cases hpl : evalP s l with
        | none => simp [hpl] at hp
        | some a =>
          simp only [hpl] at hp
          have h1 := bind_agree (fun a' s'' h => ih1 l s s'' a a' hpl h) hr
          exact ih3 a rest s s' v v' hp h1
      | andE l r =>
        simp only [evalP] at hp
        rw [evalExpr_andE] at hr
        cases hpl : evalP s l with
        | none => simp [hpl] at hp
        | some a =>
          simp only [hpl] at hp
          have h1 := bind_agree (fun a' s'' h => ih1 l s s'' a a' hpl h) hr
          have h2 := bind_agree (ok_agree (getHeap_ok s)) h1
          by_cases ht : a.truthy s.heap = true
          · rw [if_pos ht] at h2
            simp only [if_pos ht] at hp
            exact ih1 r s s' v v' hp h2
          · rw [if_neg ht] at h2
            simp only [if_neg ht] at hp
            simp only [M.run_pure, Res.ok.injEq] at h2
            simp only [Option.some.injEq] at hp
            exact ⟨by rw [← h2.1, hp], h2.2.symm⟩
      | orE l r =>
        simp only [evalP] at hp
        rw [evalExpr_orE] at hr
        cases hpl : evalP s l with
        | none => simp [hpl] at hp
        | some a =>
          simp only [hpl] at hp
          have h1 := bind_agree (fun a' s'' h => ih1 l s s'' a a' hpl h) hr
          have h2 := bind_agree (ok_agree (getHeap_ok s)) h1
          by_cases ht : a.truthy s.heap = true
          · rw [if_pos ht] at h2
            simp only [if_pos ht] at hp
            simp only [M.run_pure, Res.ok.injEq] at h2
            simp only [Option.some.injEq] at hp
            exact ⟨by rw [← h2.1, hp], h2.2.symm⟩
          · rw [if_neg ht] at h2
            simp only [if_neg ht] at hp
            exact ih1 r s s' v v' hp h2
      | ifE c t e =>
        simp only [evalP] at hp
        rw [evalExpr_ifE] at hr
        cases hpc : evalP s c with
        | none => simp [hpc] at hp
        | some cv =>
          simp only [hpc] at hp
          have h1 := bind_agree (fun a' s'' h => ih1 c s s'' cv a' hpc h) hr
          have h2 := bind_agree (ok_agree (getHeap_ok s)) h1
          by_cases ht : cv.truthy s.heap = true
          · rw [if_pos ht] at h2 hp
            exact ih1 t s s' v v' hp h2
          · rw [if_neg ht] at h2 hp
            exact ih1 e s s' v v' hp h2
      | tupleE es =>
        simp only [evalP] at hp
        rw [evalExpr_tupleE] at hr
        cases hpe : evalPs s es with
        | none => simp [hpe] at hp
        | some vs =>
          simp only [hpe] at hp
          simp only [Option.some.injEq] at hp
          have h1 := bind_agree (fun vs' s'' h => ih2 es s s'' vs vs' hpe h) hr
          simp only [M.run_pure, Res.ok.injEq] at h1
          exact ⟨by rw [← h1.1, hp], h1.2.symm⟩
      | subscript o i =>
        simp only [evalP] at hp
        rw [evalExpr_subscript] at hr
        cases hpo : evalP s o with
        | none => simp [hpo] at hp
        | some ov =>
          cases hpi : evalP s i with
          | none => simp [hpo, hpi] at hp
          | some iv =>
            simp only [hpo, hpi] at hp
            cases hk : indexK s.heap ov iv with
            | none => simp [hk] at hp
            | some k =>
              cases k with
              | err t m => simp [hk] at hp
              | errV t as => simp [hk] at hp
              | val w =>
                simp only [hk] at hp
                simp only [Option.some.injEq] at hp
                have h1 := bind_agree (fun a' s'' h => ih1 o s s'' ov a' hpo h) hr
                have h2 := bind_agree (fun a' s'' h => ih1 i s s'' iv a' hpi h) h1
                have h3 := bind_agree (ok_agree (getHeap_ok s)) h2
                simp only [hk] at h3
                simp only [ofKRes, M.run_pure, Res.ok.injEq] at h3
                exact ⟨by rw [← h3.1, hp], h3.2.symm⟩
      -- Everything below is outside the fragment `evalP` models.
      | call fe args kwargs => simp [evalP] at hp
      | listE es => simp [evalP] at hp
      | dictE kvs => simp [evalP] at hp
      | slice o lo hi => simp [evalP] at hp
      | attr o field => simp [evalP] at hp
      | lam ps body => simp [evalP] at hp
      | listComp el tgt it cond => simp [evalP] at hp
    -- ### Lists of expressions
    · intro es s s' vs vs' hp hr
      cases es with
      | nil => simp only [evalPs] at hp; simp only [evalExprs_nil] at hr; simp_all
      | cons e es =>
        simp only [evalPs] at hp
        rw [evalExprs_cons] at hr
        cases hpe : evalP s e with
        | none => simp [hpe] at hp
        | some a =>
          cases hpes : evalPs s es with
          | none => simp [hpe, hpes] at hp
          | some as =>
            simp only [hpe, hpes] at hp
            simp only [Option.some.injEq] at hp
            have h1 := bind_agree (fun a' s'' h => ih1 e s s'' a a' hpe h) hr
            have h2 := bind_agree (fun as' s'' h => ih2 es s s'' as as' hpes h) h1
            simp only [M.run_pure, Res.ok.injEq] at h2
            exact ⟨by rw [← h2.1, hp], h2.2.symm⟩
    -- ### Comparison chains
    · intro prev rest s s' v v' hp hr
      cases rest with
      | nil => simp only [evalPChain] at hp; simp only [evalCmpChain_nil] at hr; simp_all
      | cons p rest =>
        obtain ⟨op, e⟩ := p
        simp only [evalPChain] at hp
        rw [evalCmpChain_cons] at hr
        cases hpe : evalP s e with
        | none => simp [hpe] at hp
        | some cur =>
          simp only [hpe] at hp
          cases hk : cmpK op prev cur with
          | none => simp [hk] at hp
          | some k =>
            cases k with
            | err t m => simp [hk] at hp
            | errV t as => simp [hk] at hp
            | val rv =>
              simp only [hk] at hp
              have h1 := bind_agree (fun a' s'' h => ih1 e s s'' cur a' hpe h) hr
              have h2 := bind_agree (ok_agree (applyCmp_val hk s)) h1
              have h3 := bind_agree (ok_agree (getHeap_ok s)) h2
              by_cases ht : rv.truthy s.heap = true
              · rw [if_pos ht] at h3 hp
                cases rest with
                | nil =>
                  simp only [M.run_pure, Res.ok.injEq] at h3
                  simp only [Option.some.injEq] at hp
                  exact ⟨by rw [← h3.1, hp], h3.2.symm⟩
                | cons q qs => exact ih3 cur (q :: qs) s s' v v' hp h3
              · rw [if_neg ht] at h3 hp
                simp only [M.run_pure, Res.ok.injEq] at h3
                simp only [Option.some.injEq] at hp
                exact ⟨by rw [← h3.1, hp], h3.2.symm⟩

/-- **Agreement.**  If the specification-level evaluator commits to a value,
then any successful interpreter run produces exactly that value and leaves the
state unchanged. -/
theorem evalP_agrees {f : Nat} {e : Expr} {s s' : State} {v v' : Value}
    (hp : evalP s e = some v) (hr : evalExpr f e s = .ok v' s') : v' = v ∧ s' = s :=
  (agree f).1 e s s' v v' hp hr

/-- The state cannot change while evaluating an expression `evalP` models. -/
theorem evalP_state {f : Nat} {e : Expr} {s s' : State} {v v' : Value}
    (hp : evalP s e = some v) (hr : evalExpr f e s = .ok v' s') : s' = s :=
  (evalP_agrees hp hr).2

end SnakeFight
