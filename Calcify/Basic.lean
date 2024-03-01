import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ShowTerm
import Lean.Elab.Tactic.Guard
import Lean

open Lean Elab Tactic Meta


open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax addSuggestion)

def mkCongrArg' (f p : Expr) : MetaM Expr := do
  if let .lam _ _ b _ := f then
    if ! b.hasLooseBVars then
      return ← mkEqRefl b
  if let .lam _ _ (.bvar 0) _ := f then
    return p
  mkCongrArg f p

partial def mkEqTrans' (p₁ p₂ : Expr) : MetaM Expr := do
  if let mkApp6 (.const ``Eq.trans _) _ _ _ _ p₁₁ p₁₂ := p₁ then
    mkEqTrans' p₁₁ (← mkEqTrans' p₁₂ p₂)
  else
    mkEqTrans p₁ p₂

partial def mkEqMPR' (e1 e2 : Expr) : MetaM Expr := do
  -- A mpr applied to an congruence with equality can be turned into transitivities
  if let mkApp6 (.const ``congrArg [_u, _v]) _α _ _a _a'
          (.lam n t (mkApp3 (.const ``Eq _) _β b₁ b₂) bi) p1 := e1 then
    return ← mkEqTrans' (← mkCongrArg' (.lam n t b₁ bi) p1)
          (← mkEqTrans' e2 (← mkCongrArg' (.lam n t b₂ bi) (← mkEqSymm p1)))

  -- Special case of the above, with an eta-contracted congruence
  if let mkApp6 (.const ``congrArg [_u, _v]) _α _ _a _a'
          (mkApp2 (.const ``Eq _) _β _b₁) p1 := e1 then
    return ← mkEqTrans' e2 (← mkEqSymm p1)

   -- A mpr applied to an mpr can be turned into a transitivity
  if let mkApp4 (.const ``Eq.mpr _) _ _ p2 p3 := e2 then
    return ← mkEqMPR' (← mkEqTrans' e1 p2) p3

  mkEqMPR e1 e2


partial def mkOfEqTrue' : Expr → MetaM Expr
  | mkApp2 (.const ``eq_self _) _α a
  => mkEqRefl a

  | mkApp2 (.const ``eq_true []) _P p
  => pure p


  | mkApp6 (.const ``Eq.trans [_u]) _ _ _ _ p1 p2
  => do mkEqMPR' p1 (← mkOfEqTrue' p2)

  | p
  => do mkOfEqTrue p


/--
Takes a proof of `(a = b) = (a' = b')` and returns a proof of `a = a'` and `b' = b`.
-/
def split_eq_true : Expr → MetaM (Expr × Expr × Expr × Expr × Expr × Expr)
  | mkApp6 (.const ``congrFun [u, _v]) β _
      (mkApp2 (.const ``Eq _) _α a)
      (mkApp2 (.const ``Eq _) _α2 a')
      (mkApp6 (.const ``congrArg _) _α3 _ _a _a' (.app (.const ``Eq _) _) p1)
      b
  => return (a, p1, a', b, mkApp2 (.const ``Eq.refl [u]) β b, b)
  | mkApp6 (.const ``congrArg [u, v]) β _
      b b'
      (mkApp2 (.const ``Eq _) α a)
      p2
  => return (a, mkApp2 (.const ``Eq.refl [v]) α a, a,
             b', mkApp4 (.const ``Eq.symm [u]) β b b' p2, b)
  | mkApp6 (.const ``congrArg [_u, _v]) _α _
      a a'
      (.lam _ _ (mkApp3 (.const ``Eq [v]) β (.bvar 0) b) _)
      p2
  => return (a, p2, a',
             b, mkApp2 (.const ``Eq.refl [v]) β b, b)
  | mkApp8 (.const ``congr [u, _v]) β (.sort 0)
      (mkApp2 (.const ``Eq _) _α a)
      (mkApp2 (.const ``Eq _) _α2 a')
      b b'
      (mkApp6 (.const ``congrArg _) _α3 _ _a _a' (.app (.const ``Eq _) _) p1)
      p2
  => return (a, p1, a', b', mkApp4 (.const ``Eq.symm [u]) β b b' p2, b)
  | e
  => throwError m!"Expected proof of `(a = b) = (a' = b')`, but got:\n{e}"

partial def simplify' : Expr → MetaM Expr
  | mkApp2 (.const ``of_eq_true _) _ p
  => do mkOfEqTrue' (← simplify' p)

  -- eliminate id application, and hope for the best
  | mkApp4 (.const ``Eq.mpr us) α β (mkApp2 (.const ``id _) _ p) p2
  => simplify' (mkApp4 (.const ``Eq.mpr us) α β p p2)

  -- replace congrFun with congrArg
  | mkApp6 (.const ``congrFun [_u, _v]) _ _ f₁ _ p1 x
  => do simplify' (← mkCongrArg (.lam "f" (←inferType f₁) (.app (.bvar 0) x) .default) p1)

  -- take congr apart
  | mkApp8 (.const ``congr [_u, _v]) _α _β _f₁ f₂ x₁ _x₂ p1 p2
  => do
    let eqf ← simplify' (← mkCongrFun (← simplify' p1) x₁)
    let eqx ← simplify' (← mkCongrArg f₂ (← simplify' p2))
    mkEqTrans' eqf eqx

  -- push congrArg into trans
  | mkApp6 (.const ``congrArg [_u, _v]) _α _β _a _a' f
    (mkApp6 (.const ``Eq.trans _) _ _ _ _ p1 p2)
  => do simplify' (← mkEqTrans' (← mkCongrArg f p1) (← mkCongrArg f p2))

  -- simplify under mpr
  | mkApp4 (.const ``Eq.mpr _) _ _ p₁ p₂
  => do
    mkEqMPR' (← simplify' p₁) (← simplify' p₂)

  -- simplify under trans
  | mkApp6 (.const ``Eq.trans _) _α _a _b _c p1 p2
  => do mkEqTrans' (← simplify' p1) (← simplify' p2)

  | e => pure e

def getCalcSteps : Expr → Array (TSyntax `calcStep) → MetaM (Array (TSyntax `calcStep))
  | mkApp6 (.const ``Eq.trans _) _ _ rhs _ proof p2, acc => do
    let step ← `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← delabToRefinableSyntax proof))
    getCalcSteps p2 (acc.push step)
  | proof, acc => do
    let some (_, _, rhs) := (← inferType proof).eq? | throwError "Expected proof of equality"
    let step ← `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← delabToRefinableSyntax proof))
    return acc.push step

def delabCalcProof (e : Expr) : MetaM (TSyntax `tactic) := do
    let some (_, lhs, _) := (← inferType e).eq? | throwError "Expected proof of equality"
    let stepStx ← getCalcSteps e #[]
    `(tactic|calc
        $(← delabToRefinableSyntax lhs):term
        $stepStx*)

def delabCalcTerm (e : Expr) : MetaM (TSyntax `term) := do
    let some (_, lhs, _) := (← inferType e).eq? | throwError "Expected proof of equality"
    let stepStx ← getCalcSteps e #[]
    `(term|calc
        $(← delabToRefinableSyntax lhs):term
        $stepStx*)

def delabProof : Expr → MetaM (TSyntax `tactic)
  | mkApp4 (.const ``Eq.mpr _) _ _ p1 (.mvar _) => do
    let calcTerm ← delabCalcTerm p1
    `(tactic|apply $(mkIdent ``Eq.mpr) <| $calcTerm)

  | mkApp4 (.const ``Eq.mpr _) _ _ p1 p2 => do
    let calcTerm ← delabCalcTerm p1
    let restProof ← delabToRefinableSyntax p2
    `(tactic|exact $(mkIdent ``Eq.mpr) $calcTerm $restProof)

  | e => delabCalcProof e


elab (name := calcifyTac) tk:"calcify " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  evalTactic t
  let proof ← instantiateMVars (mkMVar goalMVar)
  let proof ← simplify' proof
  check proof
  -- let proofStx ← delabToRefinableSyntax proof
  let tactic ← delabProof proof

  /-
  let goal ← instantiateMVars (← goalMVar.getType)
  let testMVar ← mkFreshExprSyntheticOpaqueMVar goal
  withRef tk do
    Lean.Elab.Term.runTactic testMVar.mvarId! (← `(term|by {$tactic}))
  -/

  addSuggestion tk tactic (origSpan? := ← getRef)


/--
info: Try this: calc
  0 + n
  _ = n := (Nat.zero_add n)
  _ = 1 * n := (Eq.symm (Nat.one_mul n))
  _ = 1 * 1 * n := congrArg (fun x => x * n) (Eq.symm (Nat.mul_one 1))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * 1 * n := by
  calcify simp


/--
info: Try this: calc
  0 + n
  _ = n := (Nat.zero_add n)
  _ = 1 * n := (Eq.symm (Nat.one_mul n))
  _ = 1 * 1 * n := congrArg (fun x => x * n) (Eq.symm (Nat.mul_one 1))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * 1 * n := by
  calcify simp

/--
info: Try this: calc
  0 + n
  _ = n := Nat.zero_add n
-/
#guard_msgs in
example (n : Nat) : 0 + n = n := by
  calcify simp

/--
info: Try this: calc
  n
  _ = 1 * n := Eq.symm (Nat.one_mul n)
-/
#guard_msgs in
example (n : Nat) : n = 1 * n := by
  calcify simp

/--
info: Try this: calc
  0 + n
  _ = n := (Nat.zero_add n)
  _ = 1 * n := Eq.symm (Nat.one_mul n)
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * n := by
  calcify simp [Nat.zero_add, Nat.one_mul]

/--
info: Try this: calc
  0 + n
  _ = n := (Nat.zero_add n)
  _ = n * 1 := (Eq.symm (Nat.mul_one n))
  _ = 1 * n * 1 := congrArg (fun _a => _a * 1) (Eq.symm (Nat.one_mul n))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * n * 1 := by
  calcify rw [Nat.zero_add, Nat.one_mul, Nat.mul_one]

/--
info: Try this: calc
  0 + n
  _ = n := (Nat.zero_add n)
  _ = 0 + n := (Eq.symm (Nat.zero_add n))
  _ = 0 + n * 1 := congrArg (fun _a => 0 + _a) (Eq.symm (Nat.mul_one n))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 0 + (n * 1) := by
  calcify rw [Nat.mul_one, Nat.zero_add]

/--
info: Try this: apply
  Eq.mpr <|
    calc
      P (0 + 1 * n * 1)
      _ = P (0 + n * 1) := (congrArg (fun x => P (0 + x * 1)) (Nat.one_mul n))
      _ = P (0 + n) := (congrArg (fun x => P (0 + x)) (Nat.mul_one n))
      _ = P n := congrArg P (Nat.zero_add n)
-/
#guard_msgs in
example (n : Nat) (P : Nat → Prop) (h : P n): P (0 + 1 * n * 1) := by
  calcify simp
  exact h

/--
info: Try this: exact
  Eq.mpr
    (calc
      P (0 + 1 * n * 1)
      _ = P (0 + n * 1) := (congrArg (fun x => P (0 + x * 1)) (Nat.one_mul n))
      _ = P (0 + n) := (congrArg (fun x => P (0 + x)) (Nat.mul_one n))
      _ = P n := congrArg P (Nat.zero_add n))
    h
-/
#guard_msgs in
example (n : Nat) (P : Nat → Prop) (h : P n): P (0 + 1 * n * 1) := by
  calcify simp [h]
