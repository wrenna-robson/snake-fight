import SnakeFight.Pure

/-!
# A Hoare logic for the imperative core, proved sound against the interpreter

Assertions are Lean predicates on machine states (a shallow embedding), and the
judgement `H P b Q Rt` is partial correctness: *if* the block `b` starts in a
state satisfying `P` and finishes normally, the final state satisfies `Q`; if it
finishes by `return`ing a value, that value and state satisfy `Rt`.  Soundness
(`H.sound`) is proved directly against `execBlock`, the function the CLI runs --
there is no separate "paper" semantics that could disagree with the
implementation.

Four things are worth pointing out.

**Type obligations are explicit.**  Python has no static types, so `x < n` may
raise `TypeError` instead of producing a bool.  Every rule whose *conclusion*
mentions the value of an expression therefore carries a `Defined` side
condition: the precondition must imply that `evalP` -- the effect-free evaluator
of `SnakeFight.Pure` -- actually commits to a value.  In practice this means
invariants have to say "`i` and `n` are ints", which is exactly the information
a Python reader supplies mentally.

**`break` is ruled out rather than modelled.**  The soundness statement (`Ok`)
says a verified block may finish normally, return, raise, or run out of fuel,
but may *not* `break` or `continue` out of itself.  Since no rule derives
`break`, that is automatic, and it is what makes the usual `while` rule sound: a
`break` would otherwise let control leave the loop in a state where the negated
guard does not hold.  Extending the logic to `break` means adding a third
postcondition for the abrupt exit, which is a well-understood but noisier
design.

**Calls are described by `EvalTo`, not by `evalP`.**  `evalP` declines every
call, deliberately -- it is the effect-free fragment, and that is what makes the
`Defined` obligations meaningful.  So the rules that merely *consume* the value
of an expression (assignment, `return`) take an `EvalTo` premise instead: a
semantic judgement saying "however this expression evaluates, it leaves the
state alone and its value satisfies `R`".  `EvalTo.of_evalP` covers the pure
fragment, `EvalTo.callName` covers a call whose callee has a `CallSpec`, and
`EvalTo.binop` glues them together, so a call may appear nested inside an
argument.

**What is not covered.**  `for`, `try`, method and builtin-method calls, and
assignment to subscripts have no rules: verified blocks are the imperative core
plus procedure calls, and everything else is still executed by the same
interpreter, just not reasoned about here.
-/

namespace SnakeFight

/-- An assertion is a predicate on machine states. -/
abbrev Assn := State → Prop

/-- `e` evaluates, without side effects, to a truthy value in `s`. -/
def Truthy (e : Expr) (s : State) : Prop :=
  ∃ v, evalP s e = some v ∧ v.truthy s.heap = true

/-- `e` evaluates, without side effects, to a falsy value in `s`. -/
def Falsy (e : Expr) (s : State) : Prop :=
  ∃ v, evalP s e = some v ∧ v.truthy s.heap = false

/-- `e` is well defined -- effect-free, and not raising -- in every state
satisfying `P`.  This is the proof obligation that replaces static typing. -/
def Defined (P : Assn) (e : Expr) : Prop :=
  ∀ s, P s → ∃ v, evalP s e = some v

/-! ## Stepping through a `bind`

One lemma does all the work of unfolding the interpreter's `do` blocks: a
successful run of `m >>= k` factors into a successful run of `m` and then of `k`.
Unlike `bind_agree` in `SnakeFight.Pure` it does not need the value of `m` to be
known in advance, which is what a call needs -- the value comes back out of the
callee. -/

theorem bind_cases {α β} {m : M α} {k : α → M β} {s s' : State} {b : β}
    (hr : (m >>= k) s = .ok b s') :
    ∃ (a : α) (s1 : State), m s = .ok a s1 ∧ k a s1 = .ok b s' := by
  simp only [M.run_bind] at hr
  cases hms : m s with
  | ok a s1 => rw [hms] at hr; exact ⟨a, s1, rfl, hr⟩
  | exn e s1 => rw [hms] at hr; simp at hr
  | timeout s1 => rw [hms] at hr; simp at hr

/-! ## Expressions, including calls

`EvalTo P e R` is the expression-level judgement the statement rules take.  Like
`H` it is partial: an expression is allowed to raise or run out of fuel, but if
it produces a value at all, that value satisfies `R` and the state is exactly
where it started.  The "state is unchanged" half is what makes it composable --
and, at a call, it is precisely the promise that the callee did not scribble on
the caller. -/

/-- `e` evaluates, in any state satisfying `P`, without changing the state, to a
value satisfying `R` -- or does not evaluate at all. -/
def EvalTo (P : Assn) (e : Expr) (R : State → Value → Prop) : Prop :=
  ∀ (f : Nat) (s s' : State) (v : Value), P s → evalExpr f e s = .ok v s' → R s v ∧ s' = s

/-- `EvalTo` for an argument list, evaluated left to right. -/
def EvalsTo (P : Assn) (es : List Expr) (R : State → List Value → Prop) : Prop :=
  ∀ (f : Nat) (s s' : State) (vs : List Value), P s → evalExprs f es s = .ok vs s' →
    R s vs ∧ s' = s

/-- Everything the pure fragment can describe is an `EvalTo`.  This is
`evalP_agrees` in the shape the rules want. -/
theorem EvalTo.of_evalP {P : Assn} {e : Expr} {R : State → Value → Prop}
    (h : ∀ s, P s → ∃ v, evalP s e = some v ∧ R s v) : EvalTo P e R := by
  intro f s s' v hP hr
  obtain ⟨w, hw, hR⟩ := h s hP
  obtain ⟨rfl, rfl⟩ := evalP_agrees hw hr
  exact ⟨hR, rfl⟩

/-- Weaken the conclusion. -/
theorem EvalTo.imp {P : Assn} {e : Expr} {R R' : State → Value → Prop} (h : EvalTo P e R)
    (hR : ∀ s v, P s → R s v → R' s v) : EvalTo P e R' := by
  intro f s s' v hP hr
  obtain ⟨hRv, hs⟩ := h f s s' v hP hr
  exact ⟨hR s v hP hRv, hs⟩

/-- Strengthen the precondition. -/
theorem EvalTo.pre {P P' : Assn} {e : Expr} {R : State → Value → Prop} (h : EvalTo P e R)
    (hP : ∀ s, P' s → P s) : EvalTo P' e R := fun f s s' v hP' hr => h f s s' v (hP s hP') hr

/-- Reading a variable. -/
theorem EvalTo.name {P : Assn} (x : String) {R : State → Value → Prop}
    (h : ∀ s, P s → ∃ v, s.lookupName x = some v ∧ R s v) : EvalTo P (.name x) R :=
  EvalTo.of_evalP h

/-- The empty argument list. -/
theorem EvalsTo.nil {P : Assn} {R : State → List Value → Prop} (h : ∀ s, P s → R s []) :
    EvalsTo P [] R := by
  intro f s s' vs hP hr
  rw [evalExprs_nil] at hr
  simp only [Res.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨h s hP, rfl⟩

/-- One more argument.  Because each `EvalTo` leaves the state alone, both
components are described in the *same* state, and no intermediate assertion is
needed. -/
theorem EvalsTo.cons {P : Assn} {e : Expr} {es : List Expr}
    {A : State → Value → Prop} {B : State → List Value → Prop}
    {R : State → List Value → Prop}
    (he : EvalTo P e A) (hes : EvalsTo P es B)
    (hR : ∀ s v vs, P s → A s v → B s vs → R s (v :: vs)) :
    EvalsTo P (e :: es) R := by
  intro f s s' vs hP hr
  cases f with
  | zero => simp at hr
  | succ g =>
    rw [evalExprs_cons] at hr
    obtain ⟨v1, s1, h1, hr⟩ := bind_cases hr
    obtain ⟨hA, hs1⟩ := he g s s1 v1 hP h1
    rw [hs1] at hr
    obtain ⟨vs2, s2, h2, hr⟩ := bind_cases hr
    obtain ⟨hB, hs2⟩ := hes g s s2 vs2 hP h2
    rw [hs2] at hr
    simp only [M.run_pure, Res.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hR s v1 vs2 hP hA hB, rfl⟩

/-- A binary operator applied to two `EvalTo`s.  The side condition is the usual
type obligation, in kernel form: the operands must be ones the kernel commits a
value for. -/
theorem EvalTo.binop {P : Assn} {op : BinOp} {l r : Expr}
    {A B R : State → Value → Prop}
    (hl : EvalTo P l A) (hr : EvalTo P r B)
    (hop : ∀ s a b, P s → A s a → B s b → ∃ w, binOpK op a b = some (.val w) ∧ R s w) :
    EvalTo P (.binop op l r) R := by
  intro f s s' v hP hres
  cases f with
  | zero => simp at hres
  | succ g =>
    rw [evalExpr_binop] at hres
    obtain ⟨a, s1, h1, hres⟩ := bind_cases hres
    obtain ⟨hA, hs1⟩ := hl g s s1 a hP h1
    rw [hs1] at hres
    obtain ⟨b, s2, h2, hres⟩ := bind_cases hres
    obtain ⟨hB, hs2⟩ := hr g s s2 b hP h2
    rw [hs2] at hres
    obtain ⟨w, hk, hR⟩ := hop s a b hP hA hB
    rw [applyBinOp_val hk] at hres
    simp only [Res.ok.injEq] at hres
    obtain ⟨rfl, rfl⟩ := hres
    exact ⟨hR, rfl⟩

/-! ## The judgement -/

/-- What a verified block is permitted to do.

Normal termination must establish `Q`; a `return v` must establish `Rt v`.
Raising and running out of fuel are outside the scope of partial correctness, so
they are allowed unconditionally.  `break` and `continue` are *forbidden*: a
verified block never transfers control to an enclosing loop. -/
def Ok (Q : Assn) (Rt : Value → Assn) : Res Signal → Prop
  | .ok .normal s => Q s
  | .ok (.ret v) s => Rt v s
  | .ok .brk _ => False
  | .ok .cont _ => False
  | .exn _ _ => True
  | .timeout _ => True

theorem Ok.imp {Q Q' : Assn} {Rt Rt' : Value → Assn} (hq : ∀ s, Q s → Q' s)
    (hr : ∀ v s, Rt v s → Rt' v s) : ∀ res, Ok Q Rt res → Ok Q' Rt' res := by
  intro res h
  cases res with
  | ok sig s =>
    cases sig with
    | normal => exact hq s h
    | brk => exact h
    | cont => exact h
    | ret v => exact hr v s h
  | exn e s => trivial
  | timeout s => trivial

/-- The program logic.  `H P b Q Rt` reads "`{P} b {Q}`, and `{Rt v}` on
`return v`". -/
inductive H : Assn → Block → Assn → (Value → Assn) → Prop where
  /-- The empty block changes nothing. -/
  | nil {P : Assn} {Rt : Value → Assn} : H P [] P Rt
  /-- Sequencing. -/
  | cons {P Q R : Assn} {Rt : Value → Assn} {s : Stmt} {rest : Block} :
      H P [s] Q Rt → H Q rest R Rt → H P (s :: rest) R Rt
  /-- Strengthen the precondition and weaken both postconditions. -/
  | conseq {P P' Q Q' : Assn} {Rt Rt' : Value → Assn} {b : Block} :
      (∀ s, P' s → P s) → H P b Q Rt → (∀ s, Q s → Q' s) →
      (∀ v s, Rt v s → Rt' v s) → H P' b Q' Rt'
  /-- `pass`. -/
  | pass {P : Assn} {Rt : Value → Assn} : H P [.pass] P Rt
  /-- `x = e`, for a simple variable target.  `e` is described by an `EvalTo`,
  so it may contain calls; `H.assignP` is the special case where it lies in the
  pure fragment. -/
  | assign {P Q : Assn} {Rt : Value → Assn} (x : String) (e : Expr)
      (h : EvalTo P e fun s v => Q (s.setVar x v)) :
      H P [.assign [.name x] e] Q Rt
  /-- `x op= e`, which behaves exactly like `x = x op e`. -/
  | augAssign {P Q : Assn} {Rt : Value → Assn} (x : String) (op : BinOp) (e : Expr)
      (h : ∀ s, P s → ∃ v, evalP s (.binop op (.name x) e) = some v ∧ Q (s.setVar x v)) :
      H P [.augAssign (.name x) op e] Q Rt
  /-- `if c: thn else: els`. -/
  | ifS {P Q : Assn} {Rt : Value → Assn} (c : Expr) (thn els : Block)
      (hdef : Defined P c)
      (hthen : H (fun s => P s ∧ Truthy c s) thn Q Rt)
      (helse : H (fun s => P s ∧ Falsy c s) els Q Rt) :
      H P [.ifS c thn els] Q Rt
  /-- `while c: body`, with loop invariant `I`.  A `return` inside the body
  leaves the loop, and the enclosing block, altogether. -/
  | whileS {Rt : Value → Assn} (I : Assn) (c : Expr) (body : Block)
      (hdef : Defined I c)
      (hbody : H (fun s => I s ∧ Truthy c s) body I Rt) :
      H I [.whileS c body] (fun s => I s ∧ Falsy c s) Rt
  /-- `assert c`, which must be provably true. -/
  | assertS {P : Assn} {Rt : Value → Assn} (c : Expr) (h : ∀ s, P s → Truthy c s) :
      H P [.assertS c Option.none] P Rt
  /-- `return e`.  Nothing after it runs, so the normal postcondition is
  arbitrary. -/
  | ret {P Q : Assn} {Rt : Value → Assn} (e : Expr)
      (h : EvalTo P e fun s v => Rt v s) :
      H P [.ret (some e)] Q Rt
  /-- Bare `return`, which returns `None`. -/
  | retNone {P Q : Assn} {Rt : Value → Assn} (h : ∀ s, P s → Rt Value.none s) :
      H P [.ret Option.none] Q Rt
  /-- `def name(params): body`, for parameters with no default values -- a
  default is an expression, and evaluating it is an effect this rule does not
  model.

  The postcondition sees the very function value the interpreter builds, closure
  environment included, so the next step can prove a `CallSpec` for it. -/
  | funcDef {P Q : Assn} {Rt : Value → Assn} (name : String)
      (params : List (String × Option Expr)) (body : Block)
      (hnd : params.all (fun p => p.2.isNone) = true)
      (h : ∀ s, P s → Q (s.setVar name (.func name (params.map (·.1)) [] body s.defEnv))) :
      H P [.funcDef name params body] Q Rt

@[inherit_doc] notation "{{" P "}} " b " {{" Q "}}" " {{" Rt "}}" => H P b Q Rt

/-! ## Derived structural rules -/

/-- Weaken the postcondition. -/
theorem H.post {P Q Q' : Assn} {Rt : Value → Assn} {b : Block} (d : H P b Q Rt)
    (h : ∀ s, Q s → Q' s) : H P b Q' Rt :=
  H.conseq (fun _ h => h) d h (fun _ _ h => h)

/-- Strengthen the precondition. -/
theorem H.pre {P P' Q : Assn} {Rt : Value → Assn} {b : Block} (h : ∀ s, P' s → P s)
    (d : H P b Q Rt) : H P' b Q Rt :=
  H.conseq h d (fun _ h => h) (fun _ _ h => h)

/-- `x = e` for an `e` in the pure fragment, which is the common case. -/
theorem H.assignP {P Q : Assn} {Rt : Value → Assn} (x : String) (e : Expr)
    (h : ∀ s, P s → ∃ v, evalP s e = some v ∧ Q (s.setVar x v)) :
    H P [.assign [.name x] e] Q Rt :=
  H.assign x e (EvalTo.of_evalP h)

/-- `return e` for an `e` in the pure fragment. -/
theorem H.retP {P Q : Assn} {Rt : Value → Assn} (e : Expr)
    (h : ∀ s, P s → ∃ v, evalP s e = some v ∧ Rt v s) :
    H P [.ret (some e)] Q Rt :=
  H.ret e (EvalTo.of_evalP h)

/-- `H.append` with both postconditions of the sequel weakened.  The induction
has to carry that generality: `H.conseq` may have weakened the return
postcondition of `b₁`, and the composite then has to be stated with the weaker
one, which the plain statement cannot express. -/
private theorem H.append_aux {P Q R : Assn} {Rt : Value → Assn} {b₁ b₂ : Block}
    (d₁ : H P b₁ Q Rt) :
    ∀ {Q' : Assn} {Rt' : Value → Assn},
      (∀ s, Q s → Q' s) → (∀ v s, Rt v s → Rt' v s) →
      H Q' b₂ R Rt' → H P (b₁ ++ b₂) R Rt' := by
  induction d₁ with
  | nil => intro Q' Rt' hQ _ d₂; simpa using H.pre hQ d₂
  | cons h1 _ _ ih2 =>
      intro Q' Rt' hQ hRt d₂
      exact H.cons (H.conseq (fun _ h => h) h1 (fun _ h => h) hRt) (ih2 hQ hRt d₂)
  | conseq hpre _ hpost hret ih =>
      intro Q' Rt' hQ hRt d₂
      exact H.pre hpre (ih (fun s h => hQ s (hpost s h)) (fun v s h => hRt v s (hret v s h)) d₂)
  | pass => intro Q' Rt' hQ _ d₂; exact H.cons H.pass (H.pre hQ d₂)
  | assign x e h =>
      intro Q' Rt' hQ _ d₂
      exact H.cons (H.assign x e h) (H.pre hQ d₂)
  | augAssign x op e h =>
      intro Q' Rt' hQ _ d₂
      exact H.cons (H.augAssign x op e h) (H.pre hQ d₂)
  | ifS c thn els hdef hthen helse =>
      intro Q' Rt' hQ hRt d₂
      exact H.cons
        (H.ifS c thn els hdef (H.conseq (fun _ h => h) hthen hQ hRt)
          (H.conseq (fun _ h => h) helse hQ hRt)) d₂
  | whileS I c body hdef hbody =>
      intro Q' Rt' hQ hRt d₂
      exact H.cons
        (H.post (H.whileS I c body hdef (H.conseq (fun _ h => h) hbody (fun _ h => h) hRt)) hQ) d₂
  | assertS c h => intro Q' Rt' hQ _ d₂; exact H.cons (H.assertS c h) (H.pre hQ d₂)
  | ret e h =>
      intro Q' Rt' _ hRt d₂
      exact H.cons (H.ret e (h.imp (fun v s _ hr => hRt s v hr))) d₂
  | retNone h =>
      intro Q' Rt' _ hRt d₂
      exact H.cons (H.retNone (fun s hs => hRt Value.none s (h s hs))) d₂
  | funcDef name params body hnd h =>
      intro Q' Rt' hQ _ d₂
      exact H.cons (H.funcDef name params body hnd h) (H.pre hQ d₂)

/-- Sequencing two *blocks*.  `H.cons` only puts a statement in front of a
block, which is enough to verify a program written out in one piece but not to
reuse a verified fragment inside a larger one.  This is what lets a function
body be "the verified loop, then `return r`". -/
theorem H.append {P Q R : Assn} {Rt : Value → Assn} {b₁ b₂ : Block} (d₁ : H P b₁ Q Rt)
    (d₂ : H Q b₂ R Rt) : H P (b₁ ++ b₂) R Rt :=
  d₁.append_aux (fun _ h => h) (fun _ _ h => h) d₂

/-- **The rule of constancy.**

Every rule of this logic changes the state in exactly one way: by assigning to a
simple variable.  So an assertion that survives an assignment survives a whole
verified block, and can be carried across a fragment that was verified without
knowing about it.

`H.append` sequences blocks; this is what frames around them.  Its intended use
is `InFrame s₀`, the assertion "we are still inside the callee's frame and the
caller's state is untouched", which is what a `CallSpec` has to establish about a
body that was verified on its own. -/
theorem H.frame {P Q : Assn} {Rt : Value → Assn} {b : Block} {A : Assn}
    (d : H P b Q Rt) (hA : ∀ (s : State) (x : String) (v : Value), A s → A (s.setVar x v)) :
    H (fun s => P s ∧ A s) b (fun s => Q s ∧ A s) (fun v s => Rt v s ∧ A s) := by
  induction d with
  | nil => exact H.nil
  | cons _ _ ih1 ih2 => exact H.cons ih1 ih2
  | conseq hpre _ hpost hret ih =>
      exact H.conseq (fun s h => ⟨hpre s h.1, h.2⟩) ih
        (fun s h => ⟨hpost s h.1, h.2⟩) (fun v s h => ⟨hret v s h.1, h.2⟩)
  | pass => exact H.pass
  | assign x e h =>
      exact H.assign x e ((h.pre (fun _ hs => hs.1)).imp
        (fun s v hPA hQ => ⟨hQ, hA s x v hPA.2⟩))
  | augAssign x op e h =>
      refine H.augAssign x op e ?_
      intro s hPA
      obtain ⟨v, hv, hQ⟩ := h s hPA.1
      exact ⟨v, hv, hQ, hA s x v hPA.2⟩
  | ifS c thn els hdef _ _ ihthen ihelse =>
      refine H.ifS c thn els (fun s h => hdef s h.1) ?_ ?_
      · refine H.pre ?_ ihthen
        intro s h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
      · refine H.pre ?_ ihelse
        intro s h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
  | whileS I c body hdef _ ihbody =>
      refine H.post (H.whileS (fun s => I s ∧ A s) c body (fun s h => hdef s h.1) ?_) ?_
      · refine H.pre ?_ ihbody
        intro s h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
      · intro s h; exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩
  | assertS c h => exact H.assertS c (fun s hs => h s hs.1)
  | ret e h =>
      exact H.ret e ((h.pre (fun _ hs => hs.1)).imp (fun _ _ hPA hRt => ⟨hRt, hPA.2⟩))
  | retNone h => exact H.retNone (fun s hs => ⟨h s hs.1, hs.2⟩)
  | funcDef name params body hnd h =>
      exact H.funcDef name params body hnd (fun s hPA => ⟨h s hPA.1, hA s name _ hPA.2⟩)

/-! ## Unfolding lemmas for statements -/

@[simp] theorem execBlock_nil (f : Nat) (s : State) : execBlock f [] s = .ok .normal s := by
  cases f <;> rfl

@[simp] theorem execBlock_zero (st : Stmt) (rest : Block) (s : State) :
    execBlock 0 (st :: rest) s = .timeout s := rfl

@[simp] theorem execStmt_zero (st : Stmt) (s : State) : execStmt 0 st s = .timeout s := rfl

@[simp] theorem callValue_zero (fv : Value) (args : List Value)
    (kwargs : List (String × Value)) (s : State) :
    callValue 0 fv args kwargs s = .timeout s := rfl

theorem execBlock_cons (f : Nat) (st : Stmt) (rest : Block) (s : State) :
    execBlock (f + 1) (st :: rest) s =
      (do
        let sig ← execStmt f st
        match sig with
        | Signal.normal => execBlock f rest
        | sig => pure sig) s := rfl

/-- A one-statement block is the statement. -/
theorem execBlock_singleton (f : Nat) (st : Stmt) (s : State) :
    execBlock (f + 1) [st] s = execStmt f st s := by
  rw [execBlock_cons]
  simp only [M.run_bind]
  cases h : execStmt f st s with
  | ok sig s1 => cases sig <;> simp
  | exn e s1 => simp
  | timeout s1 => simp

theorem execStmt_pass (f : Nat) (s : State) : execStmt (f + 1) .pass s = .ok .normal s := rfl

theorem execStmt_assign (f : Nat) (ts : List Target) (e : Expr) (s : State) :
    execStmt (f + 1) (.assign ts e) s =
      (do
        let v ← evalExpr f e
        bindAll f ts v
        pure Signal.normal) s := rfl

theorem execStmt_augAssign (f : Nat) (t : Target) (op : BinOp) (e : Expr) (s : State) :
    execStmt (f + 1) (.augAssign t op e) s =
      (do
        let cur ← readTarget f t
        let rv ← evalExpr f e
        let nv ← applyBinOp op cur rv
        bindTarget f t nv
        pure Signal.normal) s := rfl

theorem execStmt_ifS (f : Nat) (c : Expr) (thn els : Block) (s : State) :
    execStmt (f + 1) (.ifS c thn els) s =
      (do
        let cv ← evalExpr f c
        let h ← getHeap
        if cv.truthy h then execBlock f thn else execBlock f els) s := rfl

theorem execStmt_whileS (f : Nat) (c : Expr) (body : Block) (s : State) :
    execStmt (f + 1) (.whileS c body) s = whileLoop f c body s := rfl

theorem execStmt_assertS (f : Nat) (c : Expr) (s : State) :
    execStmt (f + 1) (.assertS c Option.none) s =
      (do
        let cv ← evalExpr f c
        let h ← getHeap
        if cv.truthy h then pure Signal.normal
        else M.throwValue (.exc "AssertionError" [])) s := by
  rfl

theorem execStmt_ret (f : Nat) (e : Expr) (s : State) :
    execStmt (f + 1) (.ret (some e)) s =
      (do
        let v ← evalExpr f e
        pure (Signal.ret v)) s := rfl

theorem execStmt_retNone (f : Nat) (s : State) :
    execStmt (f + 1) (.ret Option.none) s = .ok (Signal.ret Value.none) s := rfl

theorem execStmt_funcDef (f : Nat) (name : String) (params : List (String × Option Expr))
    (body : Block) (s : State) :
    execStmt (f + 1) (.funcDef name params body) s =
      (do
        let defaults ← evalDefaults f params
        let env ← currentEnv
        M.modify fun s =>
          s.setVar name (Value.func name (params.map (fun (p : String × Option Expr) => p.1))
            defaults body env)
        pure Signal.normal) s := rfl

theorem whileLoop_zero (c : Expr) (body : Block) (s : State) :
    whileLoop 0 c body s = .timeout s := rfl

theorem whileLoop_succ (f : Nat) (c : Expr) (body : Block) (s : State) :
    whileLoop (f + 1) c body s =
      (match evalExpr f c s with
       | .exn e s' => .exn e s'
       | .timeout s' => .timeout s'
       | .ok cv s1 =>
         if cv.truthy s1.heap then
           match execBlock f body s1 with
           | .exn e s' => .exn e s'
           | .timeout s' => .timeout s'
           | .ok .brk s2 => .ok .normal s2
           | .ok (.ret v) s2 => .ok (.ret v) s2
           | .ok _ s2 => whileLoop f c body s2
         else .ok .normal s1) := rfl

/-- The environment a `def` captures, as a plain function of the state. -/
theorem currentEnv_ok (s : State) : currentEnv s = .ok s.defEnv s := by
  cases hf : s.frame <;> simp [currentEnv, State.defEnv, hf]

/-- Parameters without defaults need nothing evaluated, so the default list is
empty -- unless the fuel runs out first. -/
theorem evalDefaults_none (f : Nat) (params : List (String × Option Expr))
    (h : params.all (fun p => p.2.isNone) = true) (s : State) :
    evalDefaults f params s = .ok [] s ∨ evalDefaults f params s = .timeout s := by
  induction f generalizing params with
  | zero =>
    cases params with
    | nil => exact Or.inl rfl
    | cons p ps => exact Or.inr rfl
  | succ g ih =>
    cases params with
    | nil => exact Or.inl rfl
    | cons p ps =>
      obtain ⟨nm, d⟩ := p
      cases d with
      | none =>
        have heq : evalDefaults (g + 1) ((nm, Option.none) :: ps) s = evalDefaults g ps s := rfl
        rw [heq]
        exact ih ps (by simpa using h)
      | some e => simp at h

/-- Binding a simple variable either assigns it or runs out of fuel; it can
neither fail nor touch anything else. -/
theorem bindTarget_name (f : Nat) (x : String) (v : Value) (s : State) :
    bindTarget f (.name x) v s = .ok () (s.setVar x v) ∨ bindTarget f (.name x) v s = .timeout s := by
  cases f with
  | zero => exact Or.inr rfl
  | succ g => exact Or.inl rfl

/-- The same for the target list of `x = e`. -/
theorem bindAll_name (f : Nat) (x : String) (v : Value) (s : State) :
    bindAll f [.name x] v s = .ok () (s.setVar x v) ∨ bindAll f [.name x] v s = .timeout s := by
  cases f with
  | zero => exact Or.inr rfl
  | succ g =>
    cases g with
    | zero => exact Or.inr rfl
    | succ g' => exact Or.inl rfl

/-- Reading a simple variable either looks it up or runs out of fuel. -/
theorem readTarget_name (f : Nat) (x : String) (s : State) :
    readTarget f (.name x) s = lookupOrRaise x s ∨ readTarget f (.name x) s = .timeout s := by
  cases f with
  | zero => exact Or.inr rfl
  | succ g => exact Or.inl rfl

/-! ## Soundness -/

/-- The `while` rule, as a statement about `whileLoop`. -/
theorem while_sound {I : Assn} {Rt : Value → Assn} {c : Expr} {body : Block}
    (hdef : Defined I c)
    (hbody : ∀ (g : Nat) (s : State), I s → Truthy c s → Ok I Rt (execBlock g body s)) :
    ∀ (g : Nat) (s : State), I s →
      Ok (fun s => I s ∧ Falsy c s) Rt (whileLoop g c body s) := by
  intro g
  induction g with
  | zero => intro s _; rw [whileLoop_zero]; trivial
  | succ g ih =>
    intro s hI
    rw [whileLoop_succ]
    obtain ⟨v, hv⟩ := hdef s hI
    cases hc : evalExpr g c s with
    | exn e s1 => simp [Ok]
    | timeout s1 => simp [Ok]
    | ok cv s1 =>
      have hag := evalP_agrees hv hc
      rw [hag.1, hag.2]
      simp only []
      by_cases ht : v.truthy s.heap = true
      · rw [if_pos ht]
        have hb := hbody g s hI ⟨v, hv, ht⟩
        cases hr : execBlock g body s with
        | exn e s2 => simp [Ok]
        | timeout s2 => simp [Ok]
        | ok sig s2 =>
          rw [hr] at hb
          cases sig with
          | normal => simpa using ih s2 hb
          | cont => exact absurd hb (by simp [Ok])
          | brk => exact absurd hb (by simp [Ok])
          | ret w => exact hb
      · rw [if_neg ht]
        simp only [Bool.not_eq_true] at ht
        exact ⟨hI, ⟨v, hv, ht⟩⟩

/-- **Soundness of the program logic.**

If `{P} b {Q} / {Rt}` is derivable, then for *every* fuel budget and every state
satisfying `P`, running `b` either establishes `Q`, or returns a value
establishing `Rt`, or raises, or runs out of fuel -- and in particular it never
breaks or continues out of `b`. -/
theorem H.sound {P Q : Assn} {Rt : Value → Assn} {b : Block} (d : H P b Q Rt) :
    ∀ (f : Nat) (s : State), P s → Ok Q Rt (execBlock f b s) := by
  induction d with
  | nil => intro f s hP; simpa [Ok] using hP
  | @cons P Q R Rt st rest _ _ ih1 ih2 =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_cons]
      simp only [M.run_bind]
      have h1 : Ok Q Rt (execStmt f st s) := by
        have := ih1 (f + 1) s hP
        rwa [execBlock_singleton] at this
      cases hst : execStmt f st s with
      | exn e s1 => simp [Ok]
      | timeout s1 => simp [Ok]
      | ok sig s1 =>
        rw [hst] at h1
        cases sig with
        | normal => simpa using ih2 f s1 h1
        | cont => exact absurd h1 (by simp [Ok])
        | brk => exact absurd h1 (by simp [Ok])
        | ret v => exact h1
  | conseq hpre _ hpost hret ih =>
    intro f s hP'
    exact Ok.imp hpost hret _ (ih f s (hpre s hP'))
  | pass =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g => rw [execStmt_pass]; simpa [Ok] using hP
  | @assign P Q Rt x e h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        rw [execStmt_assign]
        simp only [M.run_bind]
        cases he : evalExpr g e s with
        | exn er s1 => simp [Ok]
        | timeout s1 => simp [Ok]
        | ok v1 s1 =>
          obtain ⟨hQ, hs1⟩ := h g s s1 v1 hP he
          rw [hs1]
          rcases bindAll_name g x v1 s with hb | hb
          · simp only [hb]; simpa [Ok] using hQ
          · simp only [hb]; simp [Ok]
  | @augAssign P Q Rt x op e h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        obtain ⟨v, hv, hQ⟩ := h s hP
        -- Unpack what `evalP` says about `x op e`.
        simp only [evalP] at hv
        cases hx : s.lookupName x with
        | none => rw [hx] at hv; simp at hv
        | some a =>
          cases hpe : evalP s e with
          | none => rw [hx, hpe] at hv; simp at hv
          | some b =>
            rw [hx, hpe] at hv
            simp only [] at hv
            cases hk : binOpK op a b with
            | none => rw [hk] at hv; simp at hv
            | some k =>
              cases k with
              | err t m => rw [hk] at hv; simp at hv
              | errV t as => rw [hk] at hv; simp at hv
              | val w =>
                rw [hk] at hv
                simp only [Option.some.injEq] at hv
                subst hv
                rw [execStmt_augAssign]
                simp only [M.run_bind]
                rcases readTarget_name g x s with hrt | hrt
                · simp only [hrt, lookupOrRaise_of_eq hx]
                  cases he : evalExpr g e s with
                  | exn er s1 => simp [Ok]
                  | timeout s1 => simp [Ok]
                  | ok b1 s1 =>
                    have hag := evalP_agrees hpe he
                    simp only [hag.1, hag.2, applyBinOp_val hk]
                    rcases bindTarget_name g x w s with hb | hb
                    · simp only [hb]; simpa [Ok] using hQ
                    · simp only [hb]; simp [Ok]
                · simp only [hrt]; simp [Ok]
  | @ifS P Q Rt c thn els hdef _ _ ihthen ihelse =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        obtain ⟨v, hv⟩ := hdef s hP
        rw [execStmt_ifS]
        simp only [M.run_bind]
        cases hc : evalExpr g c s with
        | exn er s1 => simp [Ok]
        | timeout s1 => simp [Ok]
        | ok cv s1 =>
          have hag := evalP_agrees hv hc
          rw [hag.1, hag.2]
          simp only [getHeap_ok]
          by_cases ht : v.truthy s.heap = true
          · rw [if_pos ht]
            exact ihthen g s ⟨hP, ⟨v, hv, ht⟩⟩
          · rw [if_neg ht]
            simp only [Bool.not_eq_true] at ht
            exact ihelse g s ⟨hP, ⟨v, hv, ht⟩⟩
  | @whileS Rt I c body hdef _ ihbody =>
    intro f s hI
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        rw [execStmt_whileS]
        exact while_sound hdef (fun g' s' hI' ht' => ihbody g' s' ⟨hI', ht'⟩) g s hI
  | @assertS P Rt c h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        obtain ⟨v, hv, ht⟩ := h s hP
        rw [execStmt_assertS]
        simp only [M.run_bind]
        cases hc : evalExpr g c s with
        | exn er s1 => simp [Ok]
        | timeout s1 => simp [Ok]
        | ok cv s1 =>
          have hag := evalP_agrees hv hc
          rw [hag.1, hag.2]
          simp only [getHeap_ok, if_pos ht]
          simpa [Ok] using hP
  | @ret P Q Rt e h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        rw [execStmt_ret]
        simp only [M.run_bind]
        cases he : evalExpr g e s with
        | exn er s1 => simp [Ok]
        | timeout s1 => simp [Ok]
        | ok v1 s1 =>
          obtain ⟨hRt, hs1⟩ := h g s s1 v1 hP he
          rw [hs1]
          simpa [Ok] using hRt
  | @retNone P Q Rt h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g => rw [execStmt_retNone]; simpa [Ok] using h s hP
  | @funcDef P Q Rt name params body hnd h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        rw [execStmt_funcDef]
        rcases evalDefaults_none g params hnd s with hd | hd
        · simp only [M.run_bind, hd, currentEnv_ok, M.run_modify, M.run_pure]
          simpa [Ok] using h s hP
        · simp only [M.run_bind, hd]; simp [Ok]

/-- The form soundness is usually used in: a derivation plus an actual run. -/
theorem H.correct {P Q : Assn} {Rt : Value → Assn} {b : Block} (d : H P b Q Rt) {f : Nat}
    {s s' : State} (hP : P s) (hrun : execBlock f b s = .ok .normal s') : Q s' := by
  have := d.sound f s hP
  rwa [hrun] at this

/-- Whole-program correctness: a derivation from the initial state's
precondition transfers to `runProgram`. -/
theorem H.correct_program {P Q : Assn} {Rt : Value → Assn} {prog : Program}
    (d : H P prog Q Rt) {f : Nat} {s' : State} (hP : P (default : State))
    (hrun : runProgram f prog = .ok .normal s') : Q s' :=
  d.correct hP hrun

/-! ## Procedure calls

A call rule has to say three things: what the callee may assume about its
arguments, what it promises about its result, and -- the part a frame-free logic
has never had to say -- what it may not touch.

The third is `InFrame`.  A call runs the body in a fresh frame and restores the
caller's frame afterwards, so what the caller sees is unchanged exactly when the
body left the globals, the heap and the output alone.  `H.frame` carries that
assertion across a body that was verified without knowing about it, which is why
the loop of `mulNonneg` can be reused verbatim inside a function.

Frames here are snapshot values without identity, which is also the source of
the closure divergence noted in the README.  If frames are given heap identity
later, `InFrame` is the statement that changes: it would have to talk about
frame addresses, and possibly about aliasing between them.
-/

/-- Two states agree everywhere outside the current frame. -/
def Untouched (s₀ s : State) : Prop :=
  s.globals = s₀.globals ∧ s.heap = s₀.heap ∧ s.out = s₀.out

/-- Putting the caller's frame back on top of an untouched state gives the
caller's state back.  This is the whole content of "the call had no effect". -/
theorem untouched_restore {s₀ s : State} (h : Untouched s₀ s) :
    ({ s with frame := s₀.frame } : State) = s₀ := by
  obtain ⟨hg, hh, ho⟩ := h
  cases s₀ with
  | mk g fr hp o =>
    cases s with
    | mk g' fr' hp' o' => simp_all

/-- `InFrame s₀ s`: `s` is inside a function frame with no `global` declaration
in force, and agrees with `s₀` outside that frame.

This is the assertion a call threads through the callee's body: "the caller's
state is still untouched".  It survives assignment, so `H.frame` can carry it
across a whole verified block. -/
def InFrame (s₀ s : State) : Prop :=
  (∃ fr, s.frame = some fr ∧ fr.globalDecls = []) ∧ Untouched s₀ s

theorem InFrame.plainScope {s₀ s : State} (h : InFrame s₀ s) : s.plainScope := by
  obtain ⟨⟨fr, hfr, hgd⟩, _⟩ := h
  intro fr' hfr'
  rw [hfr] at hfr'
  cases hfr'
  exact hgd

theorem InFrame.untouched {s₀ s : State} (h : InFrame s₀ s) : Untouched s₀ s := h.2

/-- Assigning to a variable stays inside the frame. -/
theorem InFrame.setVar {s₀ s : State} (h : InFrame s₀ s) (x : String) (v : Value) :
    InFrame s₀ (s.setVar x v) := by
  obtain ⟨⟨fr, hfr, hgd⟩, hg, hh, ho⟩ := h
  refine ⟨⟨{ fr with locals := aset fr.locals x v }, ?_, hgd⟩, ?_, ?_, ?_⟩
  · simp [State.setVar, hfr, hgd]
  · rw [State.setVar_globals_of_frame hfr hgd]; exact hg
  · simpa using hh
  · simpa using ho

/-- What a function promises: a precondition on its arguments, and a
postcondition relating the arguments to the result. -/
structure Contract where
  /-- What the arguments must satisfy. -/
  pre : List Value → Prop
  /-- What the returned value then satisfies. -/
  post : List Value → Value → Prop

/-- A specification environment: a contract for each of a list of names. -/
abbrev SpecEnv := List (String × Contract)

/-- `CallSpec G fv c`: called from a state whose globals satisfy `G`, with
arguments satisfying `c.pre`, the value `fv` either fails to return -- raising or
running out of fuel -- or returns a value satisfying `c.post`, leaving the state
exactly as it was.

`G` is a property of the *globals* rather than of the whole state because a
contract has to survive being used one frame down: entering a callee's frame
changes `frame` and nothing else, so the globals are what the callee of a callee
can still rely on.  It is what a function that itself calls other functions
needs -- `G` is where "and `mulNonneg` is still bound to the function I mean"
lives. -/
def CallSpec (G : List (String × Value) → Prop) (fv : Value) (c : Contract) : Prop :=
  ∀ (f : Nat) (args : List Value) (s s' : State) (v : Value),
    G s.globals → c.pre args → callValue f fv args [] s = .ok v s' → c.post args v ∧ s' = s

/-- `Holds Γ G`: whenever the globals satisfy `G`, every name of `Γ` resolves to
a value that meets its contract.  This is the hypothesis the body of a calling
function is verified under. -/
def Holds (Γ : SpecEnv) (G : List (String × Value) → Prop) : Prop :=
  ∀ nm c, (nm, c) ∈ Γ → ∀ gl, G gl → ∃ fv, resolveGlobal gl nm = some fv ∧ CallSpec G fv c

/-! ### Unfolding a call -/

/-- The frame the interpreter builds for a call: the bound parameters, the
environment the function captured at `def` time, and no `global`
declarations. -/
def callFrame (locals env : List (String × Value)) : Frame :=
  { locals := locals, captured := env, globalDecls := [] }

/-- The state a callee's body starts in. -/
def State.enterFrame (s : State) (fr : Frame) : State := { s with frame := some fr }

@[simp] theorem evalKwargs_nil (f : Nat) (s : State) : evalKwargs f [] s = .ok [] s := by
  cases f <;> rfl

theorem evalExpr_callName (f : Nat) (g : String) (args : List Expr) (s : State) :
    evalExpr (f + 1) (.call (.name g) args []) s =
      (do
        let fv ← evalExpr f (.name g)
        let avs ← evalExprs f args
        let kvs ← evalKwargs f []
        callValue f fv avs kvs) s := rfl

theorem callValue_func (f : Nat) (name : String) (params : List String)
    (defaults : List Value) (body : Block) (env : List (String × Value))
    (args : List Value) (kwargs : List (String × Value)) (s : State) :
    callValue (f + 1) (.func name params defaults body env) args kwargs s =
      (do
        let locals ← bindParams name params defaults args kwargs
        let caller ← (fun s => Res.ok s.frame s)
        M.modify fun s => s.enterFrame (callFrame locals env)
        let r ← M.attempt (execBlock f body)
        M.modify fun s => { s with frame := caller }
        match r with
        | .error e => M.throwValue e
        | .ok sig =>
          match sig with
          | .ret v => pure v
          | _ => pure Value.none) s := rfl

@[simp] theorem enterFrame_globals (s : State) (fr : Frame) :
    (s.enterFrame fr).globals = s.globals := rfl

@[simp] theorem enterFrame_frame (s : State) (fr : Frame) :
    (s.enterFrame fr).frame = some fr := rfl

@[simp] theorem callFrame_globalDecls (locals env : List (String × Value)) :
    (callFrame locals env).globalDecls = [] := rfl

@[simp] theorem callFrame_locals (locals env : List (String × Value)) :
    (callFrame locals env).locals = locals := rfl

@[simp] theorem callFrame_captured (locals env : List (String × Value)) :
    (callFrame locals env).captured = env := rfl

/-- Entering a call frame is exactly what `InFrame` describes. -/
theorem inFrame_enterFrame (s : State) (locals env : List (String × Value)) :
    InFrame s (s.enterFrame (callFrame locals env)) :=
  ⟨⟨callFrame locals env, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem callValue_builtin (f : Nat) (nm : String) (args : List Value)
    (kwargs : List (String × Value)) (s : State) :
    callValue (f + 1) (.builtin nm) args kwargs s = callBuiltin nm args kwargs s := rfl

/-! ### The rules -/

/-- **The procedure rule.**  A `CallSpec` for a user function, from a derivation
about its body.

`hbind` supplies, for each admissible argument list, the frame the interpreter
builds -- so it also discharges "the parameters really do bind" -- together with
a derivation for the body.  That derivation starts from "the state *is* that
frame" and has to establish two things on returning: the postcondition, and
`Untouched s₀`, which is to say that the caller's globals, heap and output are
as they were.  `H.frame` is what supplies the second one, for a body that was
verified without it. -/
theorem CallSpec.ofBody {G : List (String × Value) → Prop} {name : String}
    {params : List String} {body : Block} {env : List (String × Value)} {c : Contract}
    (hbind : ∀ (args : List Value) (s : State), G s.globals → c.pre args →
      ∃ locals, bindParams name params [] args [] s = .ok locals s ∧
        H (fun t => t = s.enterFrame (callFrame locals env))
          body (fun _ => False) (fun v t => c.post args v ∧ Untouched s t)) :
    CallSpec G (.func name params [] body env) c := by
  intro f args s s' v hgl hpre hr
  cases f with
  | zero => simp at hr
  | succ g =>
    obtain ⟨locals, hb, d⟩ := hbind args s hgl hpre
    rw [callValue_func] at hr
    -- bind the parameters
    obtain ⟨locals', s1, hb', hr⟩ := bind_cases hr
    rw [hb] at hb'
    simp only [Res.ok.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    -- remember the caller's frame
    obtain ⟨caller, s2, hc, hr⟩ := bind_cases hr
    simp only [Res.ok.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    -- install the callee's frame
    obtain ⟨u, s3, hm, hr⟩ := bind_cases hr
    simp only [M.run_modify, Res.ok.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    -- run the body
    obtain ⟨res, s4, ha, hr⟩ := bind_cases hr
    have hs := d.sound g _ rfl
    cases hex : execBlock g body (s.enterFrame (callFrame locals env)) with
    | timeout s5 => rw [M.attempt, hex] at ha; simp at ha
    | exn e s5 =>
      rw [M.attempt, hex] at ha
      simp only [Res.ok.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      obtain ⟨u2, s6, hm2, hr⟩ := bind_cases hr
      simp only [M.run_modify, Res.ok.injEq] at hm2
      obtain ⟨-, rfl⟩ := hm2
      simp at hr
    | ok sig s5 =>
      rw [hex] at hs
      rw [M.attempt, hex] at ha
      simp only [Res.ok.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      obtain ⟨u2, s6, hm2, hr⟩ := bind_cases hr
      simp only [M.run_modify, Res.ok.injEq] at hm2
      obtain ⟨-, rfl⟩ := hm2
      cases sig with
      | normal => exact absurd hs (by simp [Ok])
      | brk => exact absurd hs (by simp [Ok])
      | cont => exact absurd hs (by simp [Ok])
      | ret w =>
        obtain ⟨hpost, hunt⟩ := hs
        simp only [M.run_pure, Res.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨hpost, untouched_restore hunt⟩

/-- **A call in an expression.**  If `g` names a value with a `CallSpec`, then
`g(e₁, …, eₙ)` produces a value satisfying that spec's postcondition -- and, like
every other `EvalTo`, leaves the state alone.

The arguments are described by an `EvalsTo`, so they may contain calls
themselves; `EvalTo.binop` then lets a call appear anywhere inside an argument
expression. -/
theorem EvalTo.callName {P : Assn} {G : List (String × Value) → Prop} (g : String)
    (c : Contract) {argEs : List Expr} {R : State → Value → Prop}
    (hgl : ∀ s, P s → G s.globals)
    (hf : ∀ s, P s → ∃ fv, s.lookupName g = some fv ∧ CallSpec G fv c)
    (hargs : EvalsTo P argEs (fun s avs => c.pre avs ∧ ∀ w, c.post avs w → R s w)) :
    EvalTo P (.call (.name g) argEs []) R := by
  intro f s s' v hP hres
  cases f with
  | zero => simp at hres
  | succ k =>
    rw [evalExpr_callName] at hres
    obtain ⟨fv, s1, h1, hres⟩ := bind_cases hres
    obtain ⟨fv0, hlook, hspec⟩ := hf s hP
    obtain ⟨rfl, hs1⟩ := evalP_agrees (show evalP s (.name g) = some fv0 from hlook) h1
    rw [hs1] at hres
    obtain ⟨avs, s2, h2, hres⟩ := bind_cases hres
    obtain ⟨⟨hpre, hR⟩, hs2⟩ := hargs k s s2 avs hP h2
    rw [hs2] at hres
    obtain ⟨kvs, s3, h3, hres⟩ := bind_cases hres
    rw [evalKwargs_nil] at h3
    simp only [Res.ok.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨hpost, hss⟩ := hspec k avs s s' v (hgl s hP) hpre hres
    exact ⟨hR v hpost, hss⟩

/-- The builtin `abs`, as a contract.  Builtins are not user code, so this is
proved by unfolding `callBuiltin` rather than by `CallSpec.ofBody`; it is here
because the worked example calls it. -/
def absContract : Contract where
  pre := fun args => ∃ a : Int, args = [.int a]
  post := fun args v => ∀ a : Int, args = [.int a] → v = .int (a.natAbs : Int)

theorem absContract_spec (G : List (String × Value) → Prop) :
    CallSpec G (.builtin "abs") absContract := by
  intro f args s s' v _ hpre hr
  obtain ⟨a, rfl⟩ := hpre
  cases f with
  | zero => simp at hr
  | succ g =>
    rw [callValue_builtin] at hr
    have hcb : callBuiltin "abs" [Value.int a] [] s
        = .ok (.int (if a < 0 then -a else a)) s := rfl
    rw [hcb] at hr
    simp only [Res.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨?_, rfl⟩
    intro b hb
    simp only [List.cons.injEq, and_true] at hb
    cases hb
    congr 1
    omega

end SnakeFight
