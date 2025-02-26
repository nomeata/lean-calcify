import Calcify

/--
info: Try this: calc
    0 + n
    _ = n := (Nat.zero_add n)
    _ = 1 * n := (Nat.one_mul n).symm
    _ = 1 * 1 * n := congrArg (fun x => x * n) (Eq.symm (Nat.mul_one 1))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * 1 * n := by
  calcify simp


/--
info: Try this: calc
    0 + n
    _ = n := (Nat.zero_add n)
    _ = 1 * n := (Nat.one_mul n).symm
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
    _ = 1 * n := (Nat.one_mul n).symm
-/
#guard_msgs in
example (n : Nat) : n = 1 * n := by
  calcify simp

/--
info: Try this: calc
    0 + n
    _ = n := (Nat.zero_add n)
    _ = 1 * n := (Nat.one_mul n).symm
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * n := by
  calcify simp [Nat.zero_add, Nat.one_mul]

/--
info: Try this: calc
    0 + n
    _ = n := (Nat.zero_add n)
    _ = n * 1 := (Nat.mul_one n).symm
    _ = 1 * n * 1 := congrArg (fun _a => _a * 1) (Eq.symm (Nat.one_mul n))
-/
#guard_msgs in
example (n : Nat) : 0 + n = 1 * n * 1 := by
  calcify rw [Nat.zero_add, Nat.one_mul, Nat.mul_one]

/--
info: Try this: calc
    0 + n
    _ = n := (Nat.zero_add n)
    _ = 0 + n := (Nat.zero_add n).symm
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
info: Try this: ⏎
  conv =>
    tactic =>
      calc
        P (0 + 1 * n * 1)
        _ = P (0 + n * 1) := (congrArg (fun x => P (0 + x * 1)) (Nat.one_mul n))
        _ = P (0 + n) := (congrArg (fun x => P (0 + x)) (Nat.mul_one n))
        _ = P n := congrArg P (Nat.zero_add n)
  refine h
-/
#guard_msgs in
example (n : Nat) (P : Nat → Prop) (h : P n): P (0 + 1 * n * 1) := by
  calcify simp [h]


-- Rewriting under binders works:

/--
info: Try this: calc
    List.map (fun x => (0 + 1) * (0 + x)) xs
    _ = List.map (fun x => 1 * (0 + x)) xs :=
      (congrArg (fun x => List.map x xs) (funext fun n => congrArg (fun x => x * (0 + n)) (Nat.zero_add 1)))
    _ = List.map (HMul.hMul 1) xs :=
      (congrArg (fun x => List.map x xs) (funext fun n => congrArg (HMul.hMul 1) (Nat.zero_add n)))
    _ = List.map (fun x => x) xs := (congrArg (fun x => List.map x xs) (funext fun n => Nat.one_mul n))
    _ = id xs := congrArg (fun x => x xs) List.map_id_fun'
-/
#guard_msgs in
example xs : List.map (fun n => (0 + 1) * (0 + n)) xs = xs := by
  calcify simp


-- But contextual rewriting using congruence rules are not supported well.
-- We have ad-hoc support for `ite_congr` (see above), but it is far from elegant.
-- Maybe it could be implemented fully generically, but it would be quite hairy I fear.

/--
info: Try this: calc
    if 0 + 1 * x = 0 then x + (2 * x + n) else 0 + n
    _ = if 0 + x = 0 then x + (2 * x + n) else 0 + n :=
      (ite_congr (congrArg (fun x => 0 + x = 0) (Nat.one_mul x)) (fun a => Eq.refl (x + (2 * x + n))) fun a =>
        Eq.refl (0 + n))
    _ = if x = 0 then x + (2 * x + n) else 0 + n :=
      (ite_congr (congrArg (fun x => x = 0) (Nat.zero_add x)) (fun a => Eq.refl (x + (2 * x + n))) fun a =>
        Eq.refl (0 + n))
    _ = if x = 0 then 0 + (2 * x + n) else 0 + n :=
      (ite_congr (Eq.refl (x = 0)) (fun a => congrArg (fun x_1 => x_1 + (2 * x + n)) a) fun a => Eq.refl (0 + n))
    _ = if x = 0 then 0 + (2 * 0 + n) else 0 + n :=
      (ite_congr (Eq.refl (x = 0)) (fun a => congrArg (fun x => 0 + (2 * x + n)) a) fun a => Eq.refl (0 + n))
    _ = if x = 0 then 0 + n else 0 + n := (congrArg (fun x_1 => if x = 0 then 0 + x_1 else 0 + n) (Nat.zero_add n))
    _ = if x = 0 then n else 0 + n := (congrArg (fun x_1 => if x = 0 then x_1 else 0 + n) (Nat.zero_add n))
    _ = if x = 0 then n else n := (congrArg (fun x_1 => if x = 0 then n else x_1) (Nat.zero_add n))
    _ = n := ite_self n
-/
#guard_msgs in
example (x n : Nat) : (if 0 + (1 * x) = 0 then x + ((2 * x) + n) else 0 + n) = n := by
  calcify (simp (config := {contextual := true}))

/--
info: Try this: conv =>
    tactic =>
      calc
        P (if 0 + 1 * x = 0 then x + (2 * x + n) else 0 + n)
        _ = P (if 0 + x = 0 then x + (2 * x + n) else 0 + n) :=
          (congrArg P
            (ite_congr (congrArg (fun x => 0 + x = 0) (Nat.one_mul x)) (fun a => Eq.refl (x + (2 * x + n))) fun a =>
              Eq.refl (0 + n)))
        _ = P (if x = 0 then x + (2 * x + n) else 0 + n) :=
          (congrArg P
            (ite_congr (congrArg (fun x => x = 0) (Nat.zero_add x)) (fun a => Eq.refl (x + (2 * x + n))) fun a =>
              Eq.refl (0 + n)))
        _ = P (if x = 0 then 0 + (2 * x + n) else 0 + n) :=
          (congrArg P
            (ite_congr (Eq.refl (x = 0)) (fun a => congrArg (fun x_1 => x_1 + (2 * x + n)) a) fun a => Eq.refl (0 + n)))
        _ = P (if x = 0 then 0 + (2 * 0 + n) else 0 + n) :=
          (congrArg P
            (ite_congr (Eq.refl (x = 0)) (fun a => congrArg (fun x => 0 + (2 * x + n)) a) fun a => Eq.refl (0 + n)))
        _ = P (if x = 0 then 0 + n else 0 + n) :=
          (congrArg (fun x_1 => P (if x = 0 then 0 + x_1 else 0 + n)) (Nat.zero_add n))
        _ = P (if x = 0 then n else 0 + n) := (congrArg (fun x_1 => P (if x = 0 then x_1 else 0 + n)) (Nat.zero_add n))
        _ = P (if x = 0 then n else n) := (congrArg (fun x_1 => P (if x = 0 then n else x_1)) (Nat.zero_add n))
        _ = P n := congrArg P (ite_self n)
-/
#guard_msgs in
example (x n : Nat) (P : Nat → Prop) (hP : P n): P (if 0 + (1 * x) = 0 then x + ((2 * x) + n) else 0 + n) := by
  calcify (simp (config := {contextual := true}))
  exact hP

@[congr]
private theorem List.map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]

/--
info: Try this: calc
    List.map (fun n => f n) xs
    _ = List.map (fun x => x) xs :=
      (List.map_congr fun x a => Eq.trans ((fun n a => h n a) x (of_eq_true (eq_true a))) (Nat.one_mul x))
    _ = id xs := congrArg (fun x => x xs) List.map_id_fun'
-/
#guard_msgs in
example xs (f : Nat → Nat) (h : ∀ n, n ∈ xs → f n = 1 * n) :
    List.map (fun n => f n) xs = xs := by
  calcify simp (config := {contextual := true}) [h]
