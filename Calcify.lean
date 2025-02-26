import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ShowTerm
import Lean.Elab.Tactic.Guard
import Lean

open Lean Elab Tactic Meta

open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax addSuggestion)


-- copied from std4/Std/Lean/Meta/Basic.lean
/-- Solve a goal by synthesizing an instance. -/
-- FIXME: probably can just be `g.inferInstance` once leanprover/lean4#2054 is fixed
private def Lean.MVarId.synthInstance (g : MVarId) : MetaM Unit := do
  g.assign (← Lean.Meta.synthInstance (← g.getType))

-- NB: Pattern matching on terms using `mkAppN` is not good practice, as
-- it generates very large and inefficient code.

partial def mkEqTrans' (p₁ p₂ : Expr) : MetaM Expr := do
  match_expr p₁ with
  | Eq.trans _ _ _ _ p₁₁ p₁₂ => mkEqTrans' p₁₁ (← mkEqTrans' p₁₂ p₂)
  | _ => mkEqTrans p₁ p₂

partial def mkHEqTrans' (p₁ p₂ : Expr) : MetaM Expr := do
  match_expr p₁ with
  | HEq.trans _ _ _ _ p₁₁ p₁₂ => mkHEqTrans' p₁₁ (← mkHEqTrans' p₁₂ p₂)
  | _ => mkHEqTrans p₁ p₂

partial def mkCongrArg' (f p : Expr) : MetaM Expr := do
  -- The function is constant? This becomes refl
  if let .lam _ _ b _ := f then
    if ! b.hasLooseBVars then
      return ← mkEqRefl b

  -- The function is the identity? Short-circuit
  if let .lam _ _ (.bvar 0) _ := f then
    return p

  -- Push congr into transitivity
  match_expr p with
  | Eq.trans _ _ _ _ p₁ p₂ => do
    return ← mkEqTrans' (← mkCongrArg' f p₁) (← mkCongrArg' f p₂)
  | _ => mkCongrArg f p

-- congrFun is a special case of congrArg
def mkCongrFun' (h x : Expr) : MetaM Expr := do
  let some (α, _f₁, _f₂) := (← inferType h).eq? | throwError "Expected proof of equality"
  mkCongrArg' (.lam `f α (.app (.bvar 0) x) .default) h

-- congr can be written as a composition of congrFun and congrArg
def mkCongr' (x₁ f₂ : Expr) (p1 p2 : Expr) : MetaM Expr := do
    mkEqTrans' (← mkCongrFun' p1 x₁) (← mkCongrArg' f₂ p2)


def mkEqOfHEq' (h : Expr) : MetaM Expr := do
  match_expr h with
  | HEq.refl _ x => mkEqRefl x
  | heq_of_eq _ _ _ h => pure h
  | _ => mkEqOfHEq h

def mkHEqOfEq' (h : Expr) : MetaM Expr := do
  match_expr h with
  | Eq.refl _ x => mkHEqRefl x
  | eq_of_heq _ _ _ h => pure h
  | _ => mkAppM ``heq_of_eq #[h]

def mkFunExt' (p : Expr) : MetaM Expr := do
  if let .lam n t (mkApp6 (.const ``Eq.trans _) _ _ _ _ p1 p2) bi := p then
    return ← mkEqTrans'
      (← mkFunExt' (.lam n t p1 bi))
      (← mkFunExt' (.lam n t p2 bi))
  mkFunExt p

partial def mkEqSymm' (h : Expr) : MetaM Expr := do
  match_expr h with
  | Eq.symm _ _ _ h => pure h
  | Eq.trans _ _ _ _ p₁ p₂ => mkEqTrans' (← mkEqSymm' p₂) (← mkEqSymm' p₁)
  | congrArg _ _ _ _ f p1 => mkCongrArg' f (← mkEqSymm' p1)
  | _ => mkEqSymm h

def mkPropExt' (e : Expr) : MetaM Expr := do
  match_expr e with
  | Iff.refl p => mkEqRefl p
  | Iff.of_eq _ _ p => pure p
  | _ => mkPropExt e

partial def mkEqMPR' (e1 e2 : Expr) : MetaM Expr := do
  match_expr e1 with
  | congrArg _ _ _ _ f p1 => do
    -- A mpr applied to an congruence with equality can be turned into transitivities
    if let .lam n t (mkApp3 (.const ``Eq _) _β b₁ b₂) bi := f then
      return ← mkEqTrans' (← mkCongrArg' (.lam n t b₁ bi) p1)
            (← mkEqTrans' e2
            (← mkCongrArg' (.lam n t b₂ bi) (← mkEqSymm' p1)))
    -- same with HEq
    if let .lam n t (mkApp4 (.const ``HEq _) _β₁ b₁ _β₂ b₂) bi := f then
      return ← mkHEqTrans' (← mkHEqOfEq' (← mkCongrArg' (.lam n t b₁ bi) p1))
            (← mkHEqTrans' e2
            (← mkHEqOfEq' (← mkCongrArg' (.lam n t b₂ bi) (← mkEqSymm' p1))))
    -- same with Iff
    if let .lam n t (mkApp2 (.const ``Iff _) b₁ b₂) bi := f then
      return ← mkIffOfEq (
            ← mkEqTrans' (← mkCongrArg' (.lam n t b₁ bi) p1)
            (← mkEqTrans' (← mkPropExt' e2)
            (← mkCongrArg' (.lam n t b₂ bi) (← mkEqSymm' p1))))

    -- Special case of the above, with an eta-contracted congruence
    match_expr f with
    | Eq _β _b₁ => return ← mkEqTrans' e2 (← mkEqSymm' p1)
    | Iff _ => return ← mkIffOfEq (← mkEqTrans' (← mkPropExt' e2) (← mkEqSymm' p1))
    | _ => pure ()
  | _ => pure ()

   -- A mpr applied to an mpr can be turned into a transitivity
  match_expr e2 with
  | Eq.mpr _ _ p2 p3 => return ← mkEqMPR' (← mkEqTrans' e1 p2) p3
  | _ => pure ()

  mkEqMPR e1 e2

def mkEqNDRec' (motive h1 h2 : Expr) : MetaM Expr := do
  -- TODO: Eq.mpr (congrArg …) is just Eq.ndrec, is it?
  -- So maybe the mkEqMPR handling above should be moved here
  mkEqMPR' (← mkCongrArg motive (← mkEqSymm' h2)) h1

/-
The following four functions push `ite_congr` past transitivity.
It is quite ugly and hairy, and should be generalized to arbitrary `congr`
lemmas.
-/

partial def mkIteCongr1 (goal : MVarId) (p : Expr) : MetaM Unit := do
  match_expr p with
  | Eq.refl _ _ => goal.refl
  | Eq.trans _ _ _ _ p1 p2 => do
    let [goal1, goal2, _] ← goal.applyConst `Eq.trans | throwError "Could not apply trans"
    mkIteCongr1 goal1 p1
    mkIteCongr1 goal2 p2
  | _ => do
    -- logInfo m!"here at {p}\n{goal}"
    let e ← mkConstWithFreshMVarLevels ``ite_congr
    let (mvars, _) ← forallMetaTelescopeReducing (← inferType e)
    assert! mvars.size == 12
    let _ ← isDefEq (mkMVar goal) (mkAppN e mvars)
    let _ ← isDefEq mvars[9]! p
    mvars[8]!.mvarId!.synthInstance
    (← mvars[10]!.mvarId!.intro1).2.refl
    (← mvars[11]!.mvarId!.intro1).2.refl
    -- logInfo m!"{mvars}"

partial def mkIteCongr2 (goal : MVarId) (p : Expr) : MetaM Unit := do
  if let .lam n t b bi := p then
    match_expr b with
    | Eq.refl _ _ => do
      goal.refl
      return
    | Eq.trans _ _ _ _ p1 p2 => do
      let [goal1, goal2, _] ← goal.applyConst `Eq.trans | throwError "Could not apply trans"
      mkIteCongr2 goal1 (.lam n t p1 bi)
      mkIteCongr2 goal2 (.lam n t p2 bi)
      return
    | _ =>
      unless b.hasLooseBVars do
        -- Rewriting isn't actually contextual, use simple congr
        let some (_, lhs, _rhs) := (← goal.getType).eq?
          | throwError "Expected equality goal, got{indentExpr (← goal.getType)}"
        match_expr lhs with
        | ite α c inst _t e =>
          let u ← getLevel α
          let _ ← isDefEq (mkMVar goal)
            (← mkCongrFun' (← mkCongrArg' (mkApp3 (.const ``ite [u]) α c inst) b) e)
        | _ => pure ()
      pure ()

  let e ← mkConstWithFreshMVarLevels ``ite_congr
  let (mvars, _) ← forallMetaTelescopeReducing (← inferType e)
  assert! mvars.size == 12
  let _ ← isDefEq (mkMVar goal) (mkAppN e mvars)
  mvars[9]!.mvarId!.refl
  mvars[8]!.mvarId!.synthInstance
  _ ← isDefEq mvars[10]! p
  (← mvars[11]!.mvarId!.intro1).2.refl

partial def mkIteCongr3 (goal : MVarId) (p : Expr) : MetaM Unit := do
  if let .lam n t b bi := p then
    match_expr b with
    | Eq.refl _ _ => do
      goal.refl
      return
    | Eq.trans _ _ _ _ p1 p2 => do
      let [goal1, goal2, _] ← goal.applyConst `Eq.trans | throwError "Could not apply trans"
      mkIteCongr3 goal1 (.lam n t p1 bi)
      mkIteCongr3 goal2 (.lam n t p2 bi)
      return
    | _ =>
      unless b.hasLooseBVars do
        -- Rewriting isn't actually contextual, use simple congr
        let some (_, lhs, _rhs) := (← goal.getType).eq?
          | throwError "Expected equality goal, got{indentExpr (← goal.getType)}"
        match_expr lhs with
        | ite α c inst t _e =>
          let u ← getLevel α
          let _ ← isDefEq (mkMVar goal)
            (← mkCongrArg' (mkApp4 (.const ``ite [u]) α c inst t) b)
        | _ => pure ()

  let e ← mkConstWithFreshMVarLevels ``ite_congr
  let (mvars, _) ← forallMetaTelescopeReducing (← inferType e)
  assert! mvars.size == 12
  let _ ← isDefEq (mkMVar goal) (mkAppN e mvars)
  mvars[9]!.mvarId!.refl
  mvars[8]!.mvarId!.synthInstance
  (← mvars[10]!.mvarId!.intro1).2.refl
  _ ← isDefEq mvars[11]! p

def mkIteCongr (goal p1 p2 p3 : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar goal
  let [goal1, goal2, _] ← mvar.mvarId!.applyConst `Eq.trans | throwError "Could not apply trans"
  mkIteCongr1 goal1 p1
  let [goal2, goal3, _] ← goal2.applyConst `Eq.trans| throwError "Could not apply trans"
  mkIteCongr2 goal2 p2
  mkIteCongr3 goal3 p3
  instantiateMVars mvar

partial def mkOfEqTrue' (p : Expr) : MetaM Expr := do
  match_expr p with
  | eq_self _α a => mkEqRefl a
  | iff_self a => pure <| mkApp (mkConst ``Iff.refl) a
  | eq_true _P p => pure p
  | Eq.trans _ _ _ _ p1 p2 => do mkEqMPR' p1 (← mkOfEqTrue' p2)
  | _ => do mkOfEqTrue p

partial def simplify (e : Expr) : MetaM Expr := do
  lambdaTelescope e fun xs e => do
    let e := e.headBeta
    let e' ← match_expr e with

    -- eliminate id application, and hope for the best
    | id _ p => simplify p

    -- Use the smart constructors above
    | congr _α _β _f₁ f₂ x₁ _x₂ p1 p2 => do mkCongr' x₁ f₂ (← simplify p1) (← simplify p2)
    | of_eq_true _ p                  => do mkOfEqTrue' (← simplify p)
    | congrFun _ _ _ _ p1 x           => do mkCongrFun' (← simplify p1) x
    | congrArg _α _β _a _a' f p       => do mkCongrArg' f (← simplify p)
    | funext _ _ _ _ p                => do mkFunExt' (← simplify p)
    | Eq.mpr _ _ p₁ p₂                => do mkEqMPR' (← simplify p₁) (← simplify p₂)
    | Eq.refl _ _                     => pure e
    | Eq.symm _ _ _ h                 => do mkEqSymm' (← simplify h)
    | Eq.trans _α _a _b _c p1 p2      => do mkEqTrans' (← simplify p1) (← simplify p2)
    | ite_congr _α _b _c _x _y _u _v _i1 _i2 p1 p2 p3 =>
      mkIteCongr (← inferType e) (← simplify p1) (← simplify p2) (← simplify p3)
    | HEq.refl _ _                    => pure e
    | HEq.trans _α _β _γ _a _b _c p1 p2  => do mkHEqTrans' (← simplify p1) (← simplify p2)
    | eq_of_heq _α _a _b h            => do mkEqOfHEq' (← simplify h)
    | heq_of_eq _α _a _b h            => do mkHEqOfEq' (← simplify h)
    | _                               =>
      -- This can have extra arguments
      if e.isAppOf ``Eq.ndrec && e.getAppNumArgs ≥ 6 then
        let xs := e.getAppArgs
        let motive := xs[2]!
        let m := xs[3]!
        let h ← simplify xs[5]!
        if h.isAppOf ``Eq.refl then
          return ← simplify (mkAppN m xs[6:])

        -- beta-reduce through Eq.ndrec
        -- (TODO: Could do more arguments in one go)
        if e.getAppNumArgs > 6 then
          let arg := xs[6]!
          if let .lam n d motiveType bi := motive then
          if motiveType.isForall && !motiveType.bindingDomain!.hasLooseBVars then
          let motive' := .lam n d (motiveType.bindingBody!.instantiate1 arg) bi
          let m' := m.beta #[arg]
          let e' := mkAppN (← mkEqNDRec motive' m' h) xs[7:]
          return ← simplify e'

        return ← simplify (mkAppN (← mkEqNDRec' motive m h) xs[6:])

      -- Let's look through auxLemmas which are created by some tactics
      if let some e' ← delta? e (· matches .num (.str _ "_auxLemma") _) then
        return ← simplify e'

      -- unless e.getAppFn.isFVar do logInfo m!"Unrecognized: {e}"
      trace[calcify] "unrecognized:{indentExpr e}"
      pure e
    unless e == e' do
      trace[calcify] "simplify:{indentExpr e}\n==>{indentExpr e'}"
    mkLambdaFVars xs e'

open Lean.Parser.Tactic

partial def getCalcProof (proof : Expr) : MetaM Term :=
  match_expr proof with
  | Eq.symm _ _ _ h => do
    let h ← getCalcProof h
    `($(h).$(mkIdent `symm))
  /-
  Too bad we don't have congrArg in the Eq namespace
  | congrArg _ _ _ _ f h => do
    let h ← getCalcProof h
    let f ← delabToRefinableSyntax f
    `($(h).$(mkIdent `congrArg) $f)
  -/
  | _ => delabToRefinableSyntax proof

partial def getCalcSteps (proof : Expr) (acc : Array (TSyntax ``calcStep)) :
    MetaM (Array (TSyntax ``calcStep)) :=
  match_expr proof with
  | Eq.trans _ _ rhs _ proof p2 => do
    let step ← `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← getCalcProof proof))
    getCalcSteps p2 (acc.push step)
  | _ => do
    let type ← whnf (← inferType proof)
    let some (_, _, rhs) := type.eq? | throwError "Expected proof of equality, got {type}"
    let step ← `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← getCalcProof proof))
    return acc.push step

def delabCalcProof (e : Expr) : MetaM (TSyntax `tactic) := do
    let type ← whnf (← inferType e)
    let some (_, lhs, _) := type.eq? | throwError "Expected proof of equality, got {type}"
    let stepStx ← getCalcSteps e #[]
    `(tactic|calc
        $(← delabToRefinableSyntax lhs):term
        $stepStx*)

def delabOfIffOfEqCalcProof (e : Expr) : MetaM (TSyntax `tactic) := do
    let type ← whnf (← inferType e)
    let some (_, lhs, rhs) := type.eq? | throwError "Expected proof of equality, got {type}"
    let stepStx ← getCalcSteps e #[]
    let finalStep ← `(calcStep|_ ↔ $(← delabToRefinableSyntax rhs) := $(mkIdent ``Iff.rfl))
    let stepStx := stepStx.push finalStep
    `(tactic|calc
        $(← delabToRefinableSyntax lhs):term
        $stepStx*)

def delabCalcTerm (e : Expr) : MetaM (TSyntax `term) := do
    let type ← whnf (← inferType e)
    let some (_, lhs, _) := type.eq? | throwError "Expected proof of equality, got {type}"
    let stepStx ← getCalcSteps e #[]
    `(term|calc
    $(← delabToRefinableSyntax lhs):term
    $stepStx*)

def delabMPRCalc (p1 p2 : Expr) : MetaM (TSyntax ``tacticSeq) := do
    let t ← delabCalcProof p1
    if p2.isMVar then
      `(tacticSeq|conv => tactic => $t:tactic)
    else
      let restProof ← delabToRefinableSyntax p2
      `(tacticSeq|conv => tactic => $t:tactic
                  refine $restProof)

def delabOfEqTrueCalc (p : Expr) : MetaM (TSyntax ``tacticSeq) := do
  let t ← delabCalcProof p
  `(tacticSeq|apply $(mkIdent ``of_eq_true)
              $t)

def delabCalcSeq (p : Expr) : MetaM (TSyntax ``tacticSeq) := do
  let t ← delabCalcProof p
  `(tacticSeq|$t:tactic)

def delabTrivial (p : Expr) : MetaM (TSyntax ``tacticSeq) := do
`(tacticSeq|exact $(← delabToRefinableSyntax p))

def delabProof (e : Expr) : MetaM (TSyntax ``tacticSeq) := do
  match_expr e with
  | True.intro => delabTrivial e
  | Iff.refl _ => delabTrivial e
  | Eq.mpr _ _ p1 p2 => delabMPRCalc p1 p2
  | Iff.of_eq _ _ p =>
    let t ← delabOfIffOfEqCalcProof p
    `(tacticSeq|$t:tactic)
  | of_eq_true h p =>
    if h.isEq then
      delabCalcSeq e
    else
      delabOfEqTrueCalc p
  | _ => do
    delabCalcSeq e

elab (name := calcifyTac) tk:"calcify " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  evalTactic t
  let proof ← instantiateMVars (mkMVar goalMVar)
  let proof ← simplify proof
  check proof
  let tactic ← delabProof proof

  /-
  let goal ← instantiateMVars (← goalMVar.getType)
  let testMVar ← mkFreshExprSyntheticOpaqueMVar goal
  withRef tk do
    Lean.Elab.Term.runTactic testMVar.mvarId! (← `(term|by $tactic))
  -/

  addSuggestion tk tactic (origSpan? := ← getRef)

initialize registerTraceClass `calcify
