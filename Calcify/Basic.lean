import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ShowTerm
import Lean.Elab.Tactic.Guard
import Lean

open Lean Elab Tactic Meta

open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax addSuggestion)

-- NB: Pattern matching on terms using `mkAppN` is not good practice, as
-- it generates very large and inefficient code.

partial def mkEqTrans' (p₁ p₂ : Expr) : MetaM Expr := do
  match_expr p₁ with
  | Eq.trans _ _ _ _ p₁₁ p₁₂ => mkEqTrans' p₁₁ (← mkEqTrans' p₁₂ p₂)
  | _ => mkEqTrans p₁ p₂


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
  mkCongrArg' (.lam "f" α (.app (.bvar 0) x) .default) h

-- congr can be written as a composition of congrFun and congrArg
def mkCongr' (x₁ f₂ : Expr) (p1 p2 : Expr) : MetaM Expr := do
    mkEqTrans' (← mkCongrFun' p1 x₁) (← mkCongrArg' f₂ p2)

def mkFunExt' (p : Expr) : MetaM Expr := do
  if let .lam n t (mkApp6 (.const ``Eq.trans _) _ _ _ _ p1 p2) bi := p then
    return ← mkEqTrans'
      (← mkFunExt' (.lam n t p1 bi))
      (← mkFunExt' (.lam n t p2 bi))
  mkFunExt p

partial def mkEqMPR' (e1 e2 : Expr) : MetaM Expr := do
  match_expr e1 with
  | congrArg _ _ _ _ f p1 => do
    -- A mpr applied to an congruence with equality can be turned into transitivities
    if let .lam n t (mkApp3 (.const ``Eq _) _β b₁ b₂) bi := f then
      return ← mkEqTrans' (← mkCongrArg' (.lam n t b₁ bi) p1)
            (← mkEqTrans' e2 (← mkCongrArg' (.lam n t b₂ bi) (← mkEqSymm p1)))

    -- Special case of the above, with an eta-contracted congruence
    match_expr f with
    | Eq _β _b₁ => return ← mkEqTrans' e2 (← mkEqSymm p1)
    | _ => pure ()
  | _ => pure ()

   -- A mpr applied to an mpr can be turned into a transitivity
  match_expr e2 with
  | Eq.mpr _ _ p2 p3 => return ← mkEqMPR' (← mkEqTrans' e1 p2) p3
  | _ => pure ()

  mkEqMPR e1 e2

partial def mkOfEqTrue' (p : Expr) : MetaM Expr := do
  match_expr p with
  | eq_self _α a => mkEqRefl a
  | eq_true _P p => pure p
  | Eq.trans _ _ _ _ p1 p2 => do mkEqMPR' p1 (← mkOfEqTrue' p2)
  | _ => do mkOfEqTrue p

partial def simplify (e : Expr) : MetaM Expr := do
  lambdaTelescope e fun xs e => do
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
    | Eq.trans _α _a _b _c p1 p2      => do mkEqTrans' (← simplify p1) (← simplify p2)
    | _                               => pure e
    mkLambdaFVars xs e'


partial def getCalcSteps (proof : Expr) (acc : Array (TSyntax `calcStep)) :
    MetaM (Array (TSyntax `calcStep)) :=
  match_expr proof with
  | Eq.trans _ _ rhs _ proof p2 => do
    let step ← `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← delabToRefinableSyntax proof))
    getCalcSteps p2 (acc.push step)
  | _ => do
    let some (_, _, rhs) := (← inferType proof).eq? | throwError "Expected proof of equality"
    let step ← `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← delabToRefinableSyntax proof))
    return acc.push step

open Lean.Parser.Tactic in
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

open Lean.Parser.Tactic in
def delabProof (e : Expr) : MetaM (TSyntax ``tacticSeq) :=
  match_expr e with
  | Eq.mpr _ _ p1 p2 => do
    let t ← delabCalcProof p1
    if p2.isMVar then
      `(tacticSeq|conv => tactic => $t:tactic)
    else
      let restProof ← delabToRefinableSyntax p2
      `(tacticSeq|conv => tactic => $t:tactic
                  refine $restProof)
  | _ => do
    let t ← delabCalcProof e
    `(tacticSeq|$t:tactic)

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
info: Try this: conv =>
    tactic =>
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
info: Try this:
  conv =>
    tactic =>
      calc
        P (0 + 1 * n * 1)
        _ = P (0 + n * 1) := (congrArg (fun x => P (0 + x * 1)) (Nat.one_mul n))
        _ = P (0 + n) := (congrArg (fun x => P (0 + x)) (Nat.mul_one n))
        _ = P n := congrArg P (Nat.zero_add n)
  refine h
-/
-- wait for https://github.com/leanprover/lean4/issues/3571
-- #guard_msgs in
example (n : Nat) (P : Nat → Prop) (h : P n): P (0 + 1 * n * 1) := by
  calcify simp [h]


-- Rewriting under binders works:

/--
info: Try this: calc
    List.map (fun x => (0 + 1) * (0 + x)) xs
    _ = List.map (fun x => 1 * (0 + x)) xs :=
      (congrArg (fun x => List.map x xs) (funext fun n => congrArg (fun x => x * (0 + n)) (Nat.zero_add 1)))
    _ = List.map (fun x => 1 * x) xs :=
      (congrArg (fun x => List.map x xs) (funext fun n => congrArg (HMul.hMul 1) (Nat.zero_add n)))
    _ = List.map (fun x => x) xs := (congrArg (fun x => List.map x xs) (funext fun n => Nat.one_mul n))
    _ = xs := List.map_id' xs
-/
#guard_msgs in
example xs : List.map (fun n => (0 + 1) * (0 + n)) xs = xs := by
  calcify simp


-- But contextual rewriting using congruence rules are not supported well.
-- One could add ad-hoc support for common congruence rules (`ite_congr`, `dite_congr`), but that
-- is not elegant.
-- It might also be possible generically push such congruence rules past `Eq.trans`,
-- but it will be quite hairy.

/--
info: Try this: conv =>
    tactic =>
      calc
        P (if 0 + 1 * x = 0 then x + (2 * x + n) else 0 + n)
        _ = P (if x = 0 then n else n) :=
          (congrArg P
            (ite_congr (congrArg (fun x => x = 0) (Eq.trans (congrArg (HAdd.hAdd 0) (Nat.one_mul x)) (Nat.zero_add x)))
              (fun a =>
                Eq.trans (congr (congrArg HAdd.hAdd a) (Eq.trans (congrArg (fun x => 2 * x + n) a) (Nat.zero_add n)))
                  (Nat.zero_add n))
              fun a => Nat.zero_add n))
        _ = P n := congrArg P (ite_self n)
-/
#guard_msgs in
example (x n : Nat) (P : Nat → Prop) (hP : P n): P (if 0 + (1 * x) = 0 then x + ((2 * x) + n) else 0 + n) := by
  calcify (simp (config := {contextual := true}))
  exact hP

@[congr]
theorem List.map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]

/--
info: Try this: calc
    List.map (fun n => f n) xs
    _ = List.map (fun x => x) xs :=
      (List.map_congr fun x a => Eq.trans ((fun n a => h n a) x (of_eq_true (eq_true a))) (Nat.one_mul x))
    _ = xs := List.map_id' xs
-/
#guard_msgs in
example xs (f : Nat → Nat) (h : ∀ n, n ∈ xs → f n = 1 * n) :
    List.map (fun n => f n) xs = xs := by
  calcify simp (config := {contextual := true}) [h]
