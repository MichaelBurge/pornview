Definition DecidableEq (t : Type) := forall (x y : t), {x = y} + {x <> y}.
Definition DecidableEqA elt eqA := forall (x y : elt), {eqA x y} + {~ eqA x y}.