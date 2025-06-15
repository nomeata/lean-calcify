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

/--
info: Try this: calc
    a1 * (a2 * (a3 * (a4 * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * a12))))))))))
    _ = a1 * a2 * (a3 * (a4 * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * a12))))))))) := assoc.symm
    _ = a1 * a2 * (a3 * a4 * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * a12)))))))) :=
      (congrArg (HMul.hMul (a1 * a2)) (Eq.symm assoc))
    _ = a1 * a2 * (a3 * a4) * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * a12))))))) := assoc.symm
    _ = a1 * a2 * (a3 * a4) * (a5 * a6 * (a7 * (a8 * (a9 * (a10 * (a11 * a12)))))) :=
      (congrArg (HMul.hMul (a1 * a2 * (a3 * a4))) (Eq.symm assoc))
    _ = a1 * a2 * (a3 * a4) * (a5 * a6 * (a7 * a8 * (a9 * (a10 * (a11 * a12))))) :=
      (congrArg (fun x => a1 * a2 * (a3 * a4) * (a5 * a6 * x)) (Eq.symm assoc))
    _ = a1 * a2 * (a3 * a4) * (a5 * a6 * (a7 * a8) * (a9 * (a10 * (a11 * a12)))) :=
      (congrArg (HMul.hMul (a1 * a2 * (a3 * a4))) (Eq.symm assoc))
    _ = a1 * a2 * (a3 * a4) * (a5 * a6 * (a7 * a8)) * (a9 * (a10 * (a11 * a12))) := assoc.symm
    _ = a1 * a2 * a3 * a4 * (a5 * a6 * (a7 * a8)) * (a9 * (a10 * (a11 * a12))) :=
      (congrArg (fun x => x * (a5 * a6 * (a7 * a8)) * (a9 * (a10 * (a11 * a12)))) (Eq.symm assoc))
    _ = a1 * a2 * a3 * a4 * (a5 * a6) * (a7 * a8) * (a9 * (a10 * (a11 * a12))) :=
      (congrArg (fun x => x * (a9 * (a10 * (a11 * a12)))) (Eq.symm assoc))
    _ = a1 * a2 * a3 * a4 * a5 * a6 * (a7 * a8) * (a9 * (a10 * (a11 * a12))) :=
      (congrArg (fun x => x * (a7 * a8) * (a9 * (a10 * (a11 * a12)))) (Eq.symm assoc))
    _ = a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * (a9 * (a10 * (a11 * a12))) :=
      (congrArg (fun x => x * (a9 * (a10 * (a11 * a12)))) (Eq.symm assoc))
    _ = a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * (a9 * a10 * (a11 * a12)) :=
      (congrArg (HMul.hMul (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8)) (Eq.symm assoc))
    _ = a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * (a9 * a10) * (a11 * a12) := assoc.symm
    _ = a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * (a11 * a12) :=
      (congrArg (fun x => x * (a11 * a12)) (Eq.symm assoc))
    _ = a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 := assoc.symm
    _ = b1 * (b2 * (b3 * (b4 * (b5 * (b6 * (b7 * (b8 * (b9 * (b10 * b11))))))))) := x✝
    _ = b1 * b2 * (b3 * (b4 * (b5 * (b6 * (b7 * (b8 * (b9 * (b10 * b11)))))))) := assoc.symm
    _ = b1 * b2 * b3 * (b4 * (b5 * (b6 * (b7 * (b8 * (b9 * (b10 * b11))))))) := assoc.symm
    _ = b1 * b2 * b3 * (b4 * b5 * (b6 * (b7 * (b8 * (b9 * (b10 * b11)))))) :=
      (congrArg (HMul.hMul (b1 * b2 * b3)) (Eq.symm assoc))
    _ = b1 * b2 * b3 * (b4 * b5 * (b6 * b7 * (b8 * (b9 * (b10 * b11))))) :=
      (congrArg (fun x => b1 * b2 * b3 * (b4 * b5 * x)) (Eq.symm assoc))
    _ = b1 * b2 * b3 * (b4 * b5 * (b6 * b7) * (b8 * (b9 * (b10 * b11)))) :=
      (congrArg (HMul.hMul (b1 * b2 * b3)) (Eq.symm assoc))
    _ = b1 * b2 * b3 * (b4 * b5 * (b6 * b7)) * (b8 * (b9 * (b10 * b11))) := assoc.symm
    _ = b1 * b2 * b3 * (b4 * b5) * (b6 * b7) * (b8 * (b9 * (b10 * b11))) :=
      (congrArg (fun x => x * (b8 * (b9 * (b10 * b11)))) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * b5 * (b6 * b7) * (b8 * (b9 * (b10 * b11))) :=
      (congrArg (fun x => x * (b6 * b7) * (b8 * (b9 * (b10 * b11)))) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * b5 * b6 * b7 * (b8 * (b9 * (b10 * b11))) :=
      (congrArg (fun x => x * (b8 * (b9 * (b10 * b11)))) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * b5 * b6 * b7 * (b8 * b9 * (b10 * b11)) :=
      (congrArg (HMul.hMul (b1 * b2 * b3 * b4 * b5 * b6 * b7)) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * b5 * b6 * b7 * (b8 * b9) * (b10 * b11) := assoc.symm
    _ = b1 * b2 * b3 * b4 * b5 * b6 * b7 * b8 * b9 * (b10 * b11) :=
      (congrArg (fun x => x * (b10 * b11)) (Eq.symm assoc))
    _ = b1 * b2 * b3 * b4 * b5 * b6 * b7 * b8 * b9 * b10 * b11 := assoc.symm
    _ = c1 * (c2 * (c3 * (c4 * (c5 * (c6 * (c7 * (c8 * (c9 * c10)))))))) := x✝¹
    _ = c1 * c2 * (c3 * (c4 * (c5 * (c6 * (c7 * (c8 * (c9 * c10))))))) := assoc.symm
    _ = c1 * c2 * c3 * (c4 * (c5 * (c6 * (c7 * (c8 * (c9 * c10)))))) := assoc.symm
    _ = c1 * c2 * c3 * (c4 * c5 * (c6 * (c7 * (c8 * (c9 * c10))))) :=
      (congrArg (HMul.hMul (c1 * c2 * c3)) (Eq.symm assoc))
    _ = c1 * c2 * c3 * (c4 * c5 * (c6 * c7 * (c8 * (c9 * c10)))) :=
      (congrArg (fun x => c1 * c2 * c3 * (c4 * c5 * x)) (Eq.symm assoc))
    _ = c1 * c2 * c3 * (c4 * c5 * (c6 * c7) * (c8 * (c9 * c10))) :=
      (congrArg (HMul.hMul (c1 * c2 * c3)) (Eq.symm assoc))
    _ = c1 * c2 * c3 * (c4 * c5 * (c6 * c7)) * (c8 * (c9 * c10)) := assoc.symm
    _ = c1 * c2 * c3 * (c4 * c5) * (c6 * c7) * (c8 * (c9 * c10)) :=
      (congrArg (fun x => x * (c8 * (c9 * c10))) (Eq.symm assoc))
    _ = c1 * c2 * c3 * c4 * c5 * (c6 * c7) * (c8 * (c9 * c10)) :=
      (congrArg (fun x => x * (c6 * c7) * (c8 * (c9 * c10))) (Eq.symm assoc))
    _ = c1 * c2 * c3 * c4 * c5 * c6 * c7 * (c8 * (c9 * c10)) :=
      (congrArg (fun x => x * (c8 * (c9 * c10))) (Eq.symm assoc))
    _ = c1 * c2 * c3 * c4 * c5 * c6 * c7 * c8 * (c9 * c10) := assoc.symm
    _ = c1 * c2 * c3 * c4 * c5 * c6 * c7 * c8 * c9 * c10 := assoc.symm
    _ = d1 * (d2 * (d3 * (d4 * (d5 * (d6 * (d7 * (d8 * d9))))))) := x✝²
    _ = d1 * d2 * (d3 * (d4 * (d5 * (d6 * (d7 * (d8 * d9)))))) := assoc.symm
    _ = d1 * d2 * d3 * (d4 * (d5 * (d6 * (d7 * (d8 * d9))))) := assoc.symm
    _ = d1 * d2 * d3 * (d4 * d5 * (d6 * (d7 * (d8 * d9)))) := (congrArg (HMul.hMul (d1 * d2 * d3)) (Eq.symm assoc))
    _ = d1 * d2 * d3 * (d4 * d5) * (d6 * (d7 * (d8 * d9))) := assoc.symm
    _ = d1 * d2 * d3 * d4 * d5 * (d6 * (d7 * (d8 * d9))) :=
      (congrArg (fun x => x * (d6 * (d7 * (d8 * d9)))) (Eq.symm assoc))
    _ = d1 * d2 * d3 * d4 * d5 * (d6 * d7 * (d8 * d9)) :=
      (congrArg (HMul.hMul (d1 * d2 * d3 * d4 * d5)) (Eq.symm assoc))
    _ = d1 * d2 * d3 * d4 * d5 * (d6 * d7) * (d8 * d9) := assoc.symm
    _ = d1 * d2 * d3 * d4 * d5 * d6 * d7 * (d8 * d9) := (congrArg (fun x => x * (d8 * d9)) (Eq.symm assoc))
    _ = d1 * d2 * d3 * d4 * d5 * d6 * d7 * d8 * d9 := assoc.symm
    _ = e1 * (e2 * (e3 * (e4 * (e5 * (e6 * (e7 * e8)))))) := x✝³
    _ = e1 * e2 * (e3 * (e4 * (e5 * (e6 * (e7 * e8))))) := assoc.symm
    _ = e1 * e2 * (e3 * e4 * (e5 * (e6 * (e7 * e8)))) := (congrArg (HMul.hMul (e1 * e2)) (Eq.symm assoc))
    _ = e1 * e2 * (e3 * e4) * (e5 * (e6 * (e7 * e8))) := assoc.symm
    _ = e1 * e2 * e3 * e4 * (e5 * (e6 * (e7 * e8))) := (congrArg (fun x => x * (e5 * (e6 * (e7 * e8)))) (Eq.symm assoc))
    _ = e1 * e2 * e3 * e4 * (e5 * e6 * (e7 * e8)) := (congrArg (HMul.hMul (e1 * e2 * e3 * e4)) (Eq.symm assoc))
    _ = e1 * e2 * e3 * e4 * (e5 * e6) * (e7 * e8) := assoc.symm
    _ = e1 * e2 * e3 * e4 * e5 * e6 * (e7 * e8) := (congrArg (fun x => x * (e7 * e8)) (Eq.symm assoc))
    _ = e1 * e2 * e3 * e4 * e5 * e6 * e7 * e8 := assoc.symm
    _ = f1 * (f2 * (f3 * (f4 * (f5 * (f6 * f7))))) := x✝⁴
    _ = f1 * f2 * (f3 * (f4 * (f5 * (f6 * f7)))) := assoc.symm
    _ = f1 * f2 * f3 * (f4 * (f5 * (f6 * f7))) := assoc.symm
    _ = f1 * f2 * f3 * (f4 * f5 * (f6 * f7)) := (congrArg (HMul.hMul (f1 * f2 * f3)) (Eq.symm assoc))
    _ = f1 * f2 * f3 * (f4 * f5) * (f6 * f7) := assoc.symm
    _ = f1 * f2 * f3 * f4 * f5 * (f6 * f7) := (congrArg (fun x => x * (f6 * f7)) (Eq.symm assoc))
    _ = f1 * f2 * f3 * f4 * f5 * f6 * f7 := assoc.symm
    _ = g1 * (g2 * (g3 * (g4 * (g5 * g6)))) := x✝⁵
    _ = g1 * g2 * (g3 * (g4 * (g5 * g6))) := assoc.symm
    _ = g1 * g2 * (g3 * g4 * (g5 * g6)) := (congrArg (HMul.hMul (g1 * g2)) (Eq.symm assoc))
    _ = g1 * g2 * (g3 * g4) * (g5 * g6) := assoc.symm
    _ = g1 * g2 * g3 * g4 * (g5 * g6) := (congrArg (fun x => x * (g5 * g6)) (Eq.symm assoc))
    _ = g1 * g2 * g3 * g4 * g5 * g6 := assoc.symm
    _ = h1 * (h2 * (h3 * (h4 * h5))) := x✝⁶
    _ = h1 * h2 * (h3 * (h4 * h5)) := assoc.symm
    _ = h1 * h2 * (h3 * h4 * h5) := (congrArg (HMul.hMul (h1 * h2)) (Eq.symm assoc))
    _ = h1 * h2 * (h3 * h4) * h5 := assoc.symm
    _ = h1 * h2 * h3 * h4 * h5 := (congrArg (fun x => x * h5) (Eq.symm assoc))
    _ = i1 * (i2 * (i3 * i4)) := x✝⁷
    _ = i1 * i2 * (i3 * i4) := assoc.symm
    _ = i1 * i2 * i3 * i4 := assoc.symm
    _ = j1 * (j2 * j3) := x✝⁸
    _ = j1 * j2 * j3 := assoc.symm
    _ = k1 * k2 := x✝⁹
    _ = l1 := x✝¹⁰
-/
#guard_msgs(pass trace, all) in
example {a1 : α}
  (_ : (((((((((((a1 * a2) * a3) * a4) * a5) * a6) * a7) * a8) * a9) * a10) * a11) * a12) = b1 * (b2 * (b3 * (b4 * (b5 * (b6 * (b7 * (b8 * (b9 * (b10 * b11))))))))))
  (_ : ((((((((((b1 * b2) * b3) * b4) * b5) * b6) * b7) * b8) * b9) * b10) * b11) = c1 * (c2 * (c3 * (c4 * (c5 * (c6 * (c7 * (c8 * (c9 * c10)))))))))
  (_ : (((((((((c1 * c2) * c3) * c4) * c5) * c6) * c7) * c8) * c9) * c10) = d1 * (d2 * (d3 * (d4 * (d5 * (d6 * (d7 * (d8 * d9))))))))
  (_ : ((((((((d1 * d2) * d3) * d4) * d5) * d6) * d7) * d8) * d9) = e1 * (e2 * (e3 * (e4 * (e5 * (e6 * (e7 * e8)))))))
  (_ : (((((((e1 * e2) * e3) * e4) * e5) * e6) * e7) * e8) = f1 * (f2 * (f3 * (f4 * (f5 * (f6 * f7))))))
  (_ : ((((((f1 * f2) * f3) * f4) * f5) * f6) * f7) = g1 * (g2 * (g3 * (g4 * (g5 * g6)))))
  (_ : (((((g1 * g2) * g3) * g4) * g5) * g6) = h1 * (h2 * (h3 * (h4 * h5))))
  (_ : ((((h1 * h2) * h3) * h4) * h5) = i1 * (i2 * (i3 * i4)))
  (_ : (((i1 * i2) * i3) * i4) = j1 * (j2 * j3))
  (_ : ((j1 * j2) * j3) = k1 * k2)
  (_ : (k1 * k2) = l1) : a1 * (a2 * (a3 * (a4 * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * a12)))))))))) = l1 := by calcify grind
