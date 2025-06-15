import Calcify


axiom testSorry : α

def α : Type := testSorry
noncomputable instance : Mul α := testSorry

@[grind _=_] theorem assoc {a b c : α} : (a * b) * c = a * (b * c) := testSorry

-- set_option trace.calcify true

/--
info: Try this: calc
    a1 * (a2 * (a3 * (a4 * (a5 * (a6 * a7)))))
    _ = a1 * a2 * (a3 * (a4 * (a5 * (a6 * a7)))) := assoc.symm
    _ = a1 * a2 * (a3 * a4 * (a5 * (a6 * a7))) := (congrArg (HMul.hMul (a1 * a2)) (Eq.symm assoc))
    _ = a1 * a2 * (a3 * a4) * (a5 * (a6 * a7)) := assoc.symm
    _ = a1 * a2 * a3 * a4 * (a5 * (a6 * a7)) := (congrArg (fun x => x * (a5 * (a6 * a7))) (Eq.symm assoc))
    _ = b1 * b2 * (b3 * b4) * (a5 * (a6 * a7)) := (congrArg (fun x => x * (a5 * (a6 * a7))) w)
    _ = b1 * b2 * b3 * b4 * (a5 * (a6 * a7)) := (congrArg (fun x => x * (a5 * (a6 * a7))) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * (a5 * a6 * a7) := (congrArg (HMul.hMul (b1 * b2 * b3 * b4)) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * (a5 * a6) * a7 := assoc.symm
    _ = b1 * b2 * b3 * (b4 * (a5 * a6)) * a7 := (congrArg (fun x => x * a7) assoc)
    _ = b1 * b2 * b3 * c1 * a7 := congrArg (fun x => b1 * b2 * b3 * x * a7) h
-/
#guard_msgs(pass trace, all) in
example {a1 : α}
    (w : (((a1 * a2) * a3) * a4) = ((b1 * b2) * (b3 * b4)))
    (h : (b4 * (a5 * a6)) = c1) :
    a1 * (a2 * (a3 * (a4 * (a5 * (a6 * a7))))) = (b1 * b2 * b3 * c1 * a7) := by
  calcify grind

opaque g : Nat → Nat

@[simp] def f (a : Nat) :=
  match a with
  | 0 => 10
  | x+1 => g (f x)

@[simp] def foo (a : Nat) :=
  match a with
  | 0 => 10
  | 1 => 10
  | a+2 => g (foo a)


grind_pattern f.eq_2 => f (x + 1)
grind_pattern foo.eq_3 => foo (a_2 + 2)

/--
info: Try this: calc
    a
    _ = foo (c + 1) := a✝.symm
    _ = foo (b + 2) :=
      (congrArg foo
        (Lean.Grind.Nat.eq_of_le_of_le (c + 1) (b + 2)
          (Lean.Grind.Nat.ro_lo_1 (c + 1) c (b + 2) 1 1 (Nat.le_refl (c + 1))
            (Lean.Grind.Nat.le_lo c (b + 1) (b + 2) 1 (Lean.Grind.Nat.le_of_eq_1 c (b + 1) a✝¹)
              (Lean.Grind.Nat.ro_lo_2 (b + 1) b (b + 2) 1 2 Lean.Grind.rfl_true (Nat.le_refl (b + 1))
                (Nat.le_refl (b + 2)))))
          (Lean.Grind.Nat.ro_lo_1 (b + 2) b (c + 1) 2 2 (Nat.le_refl (b + 2))
            (Lean.Grind.Nat.lo_lo b (b + 1) (c + 1) 1 1 (Nat.le_refl (b + 1))
              (Lean.Grind.Nat.le_lo (b + 1) c (c + 1) 1 (Lean.Grind.Nat.le_of_eq_2 c (b + 1) a✝¹)
                (Nat.le_refl (c + 1)))))))
    _ =
        foo
          (Nat.Linear.Expr.denote (Lean.RArray.leaf b)
            (((Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.num 1)).add (Nat.Linear.Expr.num 1))) :=
      (congrArg (fun x => foo x)
        (Eq.symm
          (Nat.Linear.Expr.eq_of_toNormPoly_eq (Lean.RArray.leaf b)
            (((Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.num 1)).add (Nat.Linear.Expr.num 1))
            ((Nat.Linear.Expr.var 0).add (Nat.Linear.Expr.num 2)) (Eq.refl true))))
    _ = g (foo b) := foo.eq_3 b
-/
#guard_msgs in
example : foo (c + 1) = a → c = b + 1 → a = g (foo b) := by
  intros
  calcify grind
