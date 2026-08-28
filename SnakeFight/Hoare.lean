import SnakeFight.Pure

/-!
# A Hoare logic for the imperative core, proved sound against the interpreter

Assertions are Lean predicates on machine states (a shallow embedding), and the
judgement `H P b Q` is partial correctness: *if* the block `b` starts in a state
satisfying `P` and finishes normally, the final state satisfies `Q`.  Soundness
(`H.sound`) is proved directly against `execBlock`, the function the CLI runs --
there is no separate "paper" semantics that could disagree with the
implementation.

Three things are worth pointing out.

**Type obligations are explicit.**  Python has no static types, so `x < n` may
raise `TypeError` instead of producing a bool.  Every rule that inspects an
expression therefore carries a `Defined` side condition: the precondition must
imply that `evalP` -- the effect-free evaluator of `SnakeFight.Pure` -- actually
commits to a value.  In practice this means invariants have to say "`i` and `n`
are ints", which is exactly the information a Python reader supplies mentally.

**`break` is ruled out rather than modelled.**  The soundness statement (`Ok`)
says a verified block may finish normally, return, raise, or run out of fuel,
but may *not* `break` or `continue` out of itself.  Since no rule derives
`break`, that is automatic, and it is what makes the usual `while` rule sound: a
`break` would otherwise let control leave the loop in a state where the negated
guard does not hold.  Extending the logic to `break` means adding a second
postcondition for the abrupt exit, which is a well-understood but noisier
design.

**What is not covered.**  `for`, function calls, `try`, and assignment to
subscripts have no rules: verified blocks are the pure imperative core, and
everything else is still executed by the same interpreter, just not reasoned
about here.
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

/-- What a verified block is permitted to do.

Normal termination must establish `Q`.  Returning, raising and running out of
fuel are outside the scope of partial correctness, so they are allowed
unconditionally.  `break` and `continue` are *forbidden*: a verified block never
transfers control to an enclosing loop. -/
def Ok (Q : Assn) : Res Signal → Prop
  | .ok .normal s => Q s
  | .ok (.ret _) _ => True
  | .ok .brk _ => False
  | .ok .cont _ => False
  | .exn _ _ => True
  | .timeout _ => True

theorem Ok.imp {Q Q' : Assn} (h : ∀ s, Q s → Q' s) : ∀ r, Ok Q r → Ok Q' r := by
  intro r hr
  cases r with
  | ok sig s => cases sig <;> simp_all [Ok]
  | exn e s => trivial
  | timeout s => trivial

/-- The program logic.  `H P b Q` reads "`{P} b {Q}`". -/
inductive H : Assn → Block → Assn → Prop where
  /-- The empty block changes nothing. -/
  | nil {P : Assn} : H P [] P
  /-- Sequencing. -/
  | cons {P Q R : Assn} {s : Stmt} {rest : Block} :
      H P [s] Q → H Q rest R → H P (s :: rest) R
  /-- Strengthen the precondition and weaken the postcondition. -/
  | conseq {P P' Q Q' : Assn} {b : Block} :
      (∀ s, P' s → P s) → H P b Q → (∀ s, Q s → Q' s) → H P' b Q'
  /-- `pass`. -/
  | pass {P : Assn} : H P [.pass] P
  /-- `x = e`, for a simple variable target and an effect-free `e`. -/
  | assign {P Q : Assn} (x : String) (e : Expr)
      (h : ∀ s, P s → ∃ v, evalP s e = some v ∧ Q (s.setVar x v)) :
      H P [.assign [.name x] e] Q
  /-- `x op= e`, which behaves exactly like `x = x op e`. -/
  | augAssign {P Q : Assn} (x : String) (op : BinOp) (e : Expr)
      (h : ∀ s, P s → ∃ v, evalP s (.binop op (.name x) e) = some v ∧ Q (s.setVar x v)) :
      H P [.augAssign (.name x) op e] Q
  /-- `if c: thn else: els`. -/
  | ifS {P Q : Assn} (c : Expr) (thn els : Block)
      (hdef : Defined P c)
      (hthen : H (fun s => P s ∧ Truthy c s) thn Q)
      (helse : H (fun s => P s ∧ Falsy c s) els Q) :
      H P [.ifS c thn els] Q
  /-- `while c: body`, with loop invariant `I`. -/
  | whileS (I : Assn) (c : Expr) (body : Block)
      (hdef : Defined I c)
      (hbody : H (fun s => I s ∧ Truthy c s) body I) :
      H I [.whileS c body] (fun s => I s ∧ Falsy c s)
  /-- `assert c`, which must be provably true. -/
  | assertS {P : Assn} (c : Expr) (h : ∀ s, P s → Truthy c s) :
      H P [.assertS c Option.none] P

@[inherit_doc] notation "{{" P "}} " b " {{" Q "}}" => H P b Q

/-! ## Unfolding lemmas for statements -/

@[simp] theorem execBlock_nil (f : Nat) (s : State) : execBlock f [] s = .ok .normal s := by
  cases f <;> rfl

@[simp] theorem execBlock_zero (st : Stmt) (rest : Block) (s : State) :
    execBlock 0 (st :: rest) s = .timeout s := rfl

@[simp] theorem execStmt_zero (st : Stmt) (s : State) : execStmt 0 st s = .timeout s := rfl

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
theorem while_sound {I : Assn} {c : Expr} {body : Block}
    (hdef : Defined I c)
    (hbody : ∀ (g : Nat) (s : State), I s → Truthy c s → Ok I (execBlock g body s)) :
    ∀ (g : Nat) (s : State), I s → Ok (fun s => I s ∧ Falsy c s) (whileLoop g c body s) := by
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
          | ret v => simp [Ok]
      · rw [if_neg ht]
        simp only [Bool.not_eq_true] at ht
        exact ⟨hI, ⟨v, hv, ht⟩⟩

/-- **Soundness of the program logic.**

If `{P} b {Q}` is derivable, then for *every* fuel budget and every state
satisfying `P`, running `b` either establishes `Q`, or returns, raises, or runs
out of fuel -- and in particular it never breaks or continues out of `b`. -/
theorem H.sound {P Q : Assn} {b : Block} (d : H P b Q) :
    ∀ (f : Nat) (s : State), P s → Ok Q (execBlock f b s) := by
  induction d with
  | nil => intro f s hP; simpa [Ok] using hP
  | @cons P Q R st rest _ _ ih1 ih2 =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_cons]
      simp only [M.run_bind]
      have h1 : Ok Q (execStmt f st s) := by
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
        | ret v => simp [Ok]
  | conseq hpre _ hpost ih =>
    intro f s hP'
    exact Ok.imp hpost _ (ih f s (hpre s hP'))
  | pass =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g => rw [execStmt_pass]; simpa [Ok] using hP
  | @assign P Q x e h =>
    intro f s hP
    cases f with
    | zero => simp [Ok]
    | succ f =>
      rw [execBlock_singleton]
      cases f with
      | zero => simp [Ok]
      | succ g =>
        obtain ⟨v, hv, hQ⟩ := h s hP
        rw [execStmt_assign]
        simp only [M.run_bind]
        cases he : evalExpr g e s with
        | exn er s1 => simp [Ok]
        | timeout s1 => simp [Ok]
        | ok v1 s1 =>
          have hag := evalP_agrees hv he
          rw [hag.1, hag.2]
          simp only []
          rcases bindAll_name g x v s with hb | hb
          · simp only [hb]; simpa [Ok] using hQ
          · simp only [hb]; simp [Ok]
  | @augAssign P Q x op e h =>
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
  | @ifS P Q c thn els hdef _ _ ihthen ihelse =>
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
  | @whileS I c body hdef _ ihbody =>
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
  | @assertS P c h =>
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

/-- The form soundness is usually used in: a derivation plus an actual run. -/
theorem H.correct {P Q : Assn} {b : Block} (d : H P b Q) {f : Nat} {s s' : State}
    (hP : P s) (hrun : execBlock f b s = .ok .normal s') : Q s' := by
  have := d.sound f s hP
  rwa [hrun] at this

/-- Whole-program correctness: a derivation from the initial state's
precondition transfers to `runProgram`. -/
theorem H.correct_program {P Q : Assn} {prog : Program} (d : H P prog Q) {f : Nat}
    {s' : State} (hP : P (default : State)) (hrun : runProgram f prog = .ok .normal s') :
    Q s' :=
  d.correct hP hrun

end SnakeFight
