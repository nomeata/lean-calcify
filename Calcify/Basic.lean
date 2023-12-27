import Std.Tactic.TryThis
import Std.Tactic.ShowTerm
import Std.Tactic.GuardMsgs
import Lean

open Lean Elab Tactic Meta

namespace Tmp
@[match_pattern] def mApp (f a : Expr) : Expr := .app f a
@[match_pattern] def mAppB (f a b : Expr) := mApp (mApp f a) b
@[match_pattern] def mApp2 (f a b : Expr) := mAppB f a b
@[match_pattern] def mApp3 (f a b c : Expr) := mApp (mAppB f a b) c
@[match_pattern] def mApp4 (f a b c d : Expr) := mAppB (mAppB f a b) c d
@[match_pattern] def mApp5 (f a b c d e : Expr) := mApp (mApp4 f a b c d) e
@[match_pattern] def mApp6 (f a b c d e₁ e₂ : Expr) := mAppB (mApp4 f a b c d) e₁ e₂
@[match_pattern] def mApp7 (f a b c d e₁ e₂ e₃ : Expr) := mApp3 (mApp4 f a b c d) e₁ e₂ e₃
@[match_pattern] def mApp8 (f a b c d e₁ e₂ e₃ e₄ : Expr) := mApp4 (mApp4 f a b c d) e₁ e₂ e₃ e₄
@[match_pattern] def mApp9 (f a b c d e₁ e₂ e₃ e₄ e₅ : Expr) := mApp5 (mApp4 f a b c d) e₁ e₂ e₃ e₄ e₅
@[match_pattern] def mApp10 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ : Expr) := mApp6 (mApp4 f a b c d) e₁ e₂ e₃ e₄ e₅ e₆
end Tmp
open Tmp


open Std.Tactic.TryThis (delabToRefinableSyntax addSuggestion)

def CalcProof := Expr × Array (Expr × Expr)


instance : Append CalcProof where
  append | (lhs, steps), (_lhs', steps') => (lhs, steps ++ steps')

def delabCalcProof : CalcProof → MetaM (TSyntax `tactic)
  | (lhs, steps) => do
  let stepStx ← steps.mapM fun (proof, rhs) => do
    `(calcStep|_ = $(← delabToRefinableSyntax rhs) := $(← delabToRefinableSyntax proof))
  `(tactic|calc
      $(← delabToRefinableSyntax lhs):term
      $stepStx*)

/--
Takes a proof of `(a = b) = (a' = b')` and returns a proof of `a = a'` and `b' = b`.
-/
def split_eq_true : Expr → MetaM (Expr × Expr × Expr × Expr × Expr × Expr)
  | mApp6 (.const ``congrFun [u, _v]) β _
      (mApp2 (.const ``Eq _) _α a)
      (mApp2 (.const ``Eq _) _α2 a')
      (mApp6 (.const ``congrArg _) _α3 _ _a _a' (.app (.const ``Eq _) _) p1)
      b
  => return (a, p1, a', b, mApp2 (.const ``Eq.refl [u]) β b, b)
  | mApp6 (.const ``congrArg [u, v]) β _
      b b'
      (mApp2 (.const ``Eq _) α a)
      p2
  => return (a, mApp2 (.const ``Eq.refl [v]) α a, a, b', mApp4 (.const ``Eq.symm [u]) β b b' p2, b)
  | mApp8 (.const ``congr [u, _v]) β (.sort 0)
      (mApp2 (.const ``Eq _) _α a)
      (mApp2 (.const ``Eq _) _α2 a')
      b b'
      (mApp6 (.const ``congrArg _) _α3 _ _a _a' (.app (.const ``Eq _) _) p1)
      p2
  => return (a, p1, a', b', mApp4 (.const ``Eq.symm [u]) β b b' p2, b)
  | e
  => throwError m!"Expected proof of `(a = b) = (a' = b')`, but got:\n{e}"

partial def simplify : Expr → Expr → Expr → MetaM CalcProof
  | lhs, rhs,
    mApp2 (.const ``of_eq_true _) _P (mApp2 (.const ``eq_self us) α a)
  => simplify lhs rhs (mApp2 (.const ``Eq.refl us) α a)
  | _lhs, _rhs,
    mApp2 (.const ``of_eq_true _) _P
      (mApp6 (.const ``Eq.trans _) _α _a _b _c
        p
        (mApp2 (.const ``eq_self _us) _α' _a'))
  => do
    let (a, p1, a', b, p2, b') ← split_eq_true p
    let cp1 ← simplify a a' p1
    let cp2 ← simplify b b' p2
    return cp1 ++ cp2
  | _lhs, _rhs, mApp6 (.const ``Eq.trans [_u]) _α a b c p1 p2
  => do
    let cp1 ← simplify a b p1
    let cp2 ← simplify b c p2
    return cp1 ++ cp2
  | _lhs, _rhs,
    mApp4 (.const ``Eq.symm [u]) α _rhs' _lhs'
      (mApp6 (.const ``Eq.trans _) _α a b c p1 p2)
  => do
    let cp1 ← simplify c b (mApp4 (.const ``Eq.symm [u]) α b c p2)
    let cp2 ← simplify b a (mApp4 (.const ``Eq.symm [u]) α a b p1)
    return cp1 ++ cp2
  | lhs, _rhs, mApp2 (.const ``Eq.refl _) _ _
  => return (lhs, #[])
  | lhs, rhs, proof
  => return (lhs, #[(proof, rhs)])

elab (name := calcifyTac) tk:"calcify " t:tacticSeq : tactic => withMainContext do
  let goalMVar ← getMainGoal
  evalTactic t
  let goal ← instantiateMVars (← goalMVar.getType)
  let goal ← whnf goal
  let proof ← instantiateMVars (mkMVar goalMVar)

  let .app (.app (.app (.const ``Eq _) _α) lhs) rhs := goal
    | logWarning $ m!"Goal is not an equality:\n{goal}\n"

  let cp ← simplify lhs rhs proof
  let ts ← delabCalcProof cp

  let testMVar ← mkFreshExprSyntheticOpaqueMVar goal
  withRef tk do
    Lean.Elab.Term.runTactic testMVar.mvarId! (← `(term|by {$ts}))

  addSuggestion tk ts (origSpan? := ← getRef)



/--
info: Try this: calc
  0 + n
  _ = n := (Nat.zero_add n)
  _ = 1 * n := (Eq.symm (Nat.one_mul n))
  _ = 1 * 1 * n := Eq.symm (congrFun (congrArg HMul.hMul (Nat.mul_one 1)) n)
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
  0 + 1 * n
  _ = 0 + n := (congrArg (HAdd.hAdd 0) (Nat.one_mul n))
  _ = n := Nat.zero_add n
-/
#guard_msgs in
example (n : Nat) : 0 + 1 * n = n := by
  calcify simp

/--
error: type mismatch
  Eq.refl (0 + n = n)
has type
  (0 + n = n) = (0 + n = n) : Prop
but is expected to have type
  (0 + (0 + n) = 0 + n) = (0 + n = 0 + n) : Prop
---
info: Try this: calc
  0 + n
  _ = n := Eq.mpr (id (Nat.zero_add n ▸ Eq.refl (0 + n = n))) (Eq.refl n)
-/
-- #guard_msgs in
example (n : Nat) : 0 + n = 1 * n := by
  calcify show_term rw [Nat.zero_add, Nat.one_mul]
