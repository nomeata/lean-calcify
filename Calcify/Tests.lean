import Calcify.Basic

section issue9

axiom coe  : Nat → Int
axiom cast_mul : (m n : Nat) → coe (m * n) = coe m * coe n
axiom Gamma : Int → Int
axiom fact: Nat → Nat
axiom Gamma_nat_eq_factorial (n : Nat) : Gamma (coe n + 1) = coe (fact n)


/--
info: Try this: calc
    Gamma (coe n + 1) * Gamma (coe n + 1)
    _ = coe (fact n) * Gamma (coe n + 1) := (congrArg (fun x => x * Gamma (coe n + 1)) (Gamma_nat_eq_factorial n))
    _ = coe (fact n) * coe (fact n) := (congrArg (fun x => coe (fact n) * x) (Gamma_nat_eq_factorial n))
    _ = coe (fact n * fact n) := (cast_mul (fact n) (fact n)).symm
    _ = coe (fact n) * coe (fact n) := cast_mul (fact n) (fact n)
-/
#guard_msgs in
example (n : Nat) : Gamma (coe n + 1) * Gamma (coe n + 1) = coe (fact n) * coe (fact n) := by
  calcify simp only [← cast_mul, Gamma_nat_eq_factorial]

end issue9

section issue10

/--
info: Try this: ⏎
  apply of_eq_true
  calc
    True ∧ True
    _ = True := and_self True
-/
#guard_msgs in
example : True ∧ True := by
  calcify simp


/--
info: Try this: calc
    True ∧ True ∧ True
    _ = (True ∧ True) := (congrArg (fun x => True ∧ x) (and_self True))
    _ = True := (and_self True)
    _ ↔ True := Iff.rfl
-/
#guard_msgs in
example : (True ∧ True ∧ True) ↔ True := by
  calcify simp

/--
info: Try this: calc
    True ∧ False ∧ True
    _ = (True ∧ False) := (congrArg (fun x => True ∧ x) (and_true False))
    _ = False := (and_false True)
    _ = (False ∧ True) := (and_true False).symm
    _ ↔ False ∧ True := Iff.rfl
-/
#guard_msgs in
example : (True ∧ False ∧ True) ↔ (False ∧ True) := by
  calcify simp

/--
info: Try this: calc
    True ∧ True ∧ True
    _ = (True ∧ True) := (congrArg (fun x => True ∧ x) (and_self True))
    _ = True := and_self True
-/
#guard_msgs in
example : (True ∧ True ∧ True) = True := by
  calcify simp

/-- info: Try this: exact Iff.refl True -/
#guard_msgs in
example : True ↔ True := by
  calcify simp

/-- info: Try this: exact True.intro -/
#guard_msgs in
example : True := by
   calcify simp


end issue10
