import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ShowTerm
import Lean.Elab.Tactic.Guard
import Lean

open Lean Elab Tactic Meta


open Lean.Meta.Tactic.TryThis (delabToRefinableSyntax addSuggestion)

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

partial def simplify : Expr → Expr → Expr → MetaM CalcProof
  | lhs, rhs,
    mkApp2 (.const ``of_eq_true _) _P (mkApp2 (.const ``eq_self us) α a)
  => simplify lhs rhs (mkApp2 (.const ``Eq.refl us) α a)
  | _lhs, _rhs,
    mkApp2 (.const ``of_eq_true _) _P
      (mkApp6 (.const ``Eq.trans _) _α _a _b _c
        p
        (mkApp2 (.const ``eq_self _us) _α' _a'))
  => do
    let (a, p1, a', b, p2, b') ← split_eq_true p
    let cp1 ← simplify a a' p1
    let cp2 ← simplify b b' p2
    return cp1 ++ cp2
  | _lhs, _rhs, mkApp6 (.const ``Eq.trans [_u]) _α a b c p1 p2
  => do
    let cp1 ← simplify a b p1
    let cp2 ← simplify b c p2
    return cp1 ++ cp2
  | _lhs, _rhs,
    mkApp4 (.const ``Eq.symm [u]) α _rhs' _lhs'
      (mkApp6 (.const ``Eq.trans _) _α a b c p1 p2)
  => do
    let cp1 ← simplify c b (mkApp4 (.const ``Eq.symm [u]) α b c p2)
    let cp2 ← simplify b a (mkApp4 (.const ``Eq.symm [u]) α a b p1)
    return cp1 ++ cp2
  | lhs, _rhs, mkApp2 (.const ``Eq.refl _) _ _
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
  _ = 1 * 1 * n := Eq.symm (congrArg (fun x => x * n) (Nat.mul_one 1))
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

set_option pp.explicit true
/--
info: Try this: calc
  @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 0 n
  _ = @HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n :=
    @Eq.mpr
      (@Eq Nat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 0 n)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n))
      (@Eq Nat n (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n))
      (@id
        (@Eq Prop
          (@Eq Nat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 0 n)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n))
          (@Eq Nat n (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n)))
        (@congrArg Nat Prop (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 0 n) n
          (fun _a => @Eq Nat _a (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n)) (Nat.zero_add n)))
      (@Eq.mpr (@Eq Nat n (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n)) (@Eq Nat n n)
        (@id (@Eq Prop (@Eq Nat n (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n)) (@Eq Nat n n))
          (@congrArg Nat Prop (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 1 n) n (fun _a => @Eq Nat n _a)
            (Nat.one_mul n)))
        (@Eq.refl Nat n))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * n := by
  calcify rw [Nat.zero_add, Nat.one_mul]
