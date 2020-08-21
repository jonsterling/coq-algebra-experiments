From algebra Require Import Foundation.
From algebra.rings Require Ring Ideal RingHom.
From algebra Require Category.

Import Ring.Exports Ideal.Exports RingHom.Exports Category.Exports.

Section Quotient.
  Variable A : [Ring].
  Variable I : [Ideal: A].

  Local Open Scope ring_scope.

  Definition is_quotient (A_I : [Ring]) (e : [Ring] A A_I) : Prop :=
    ∀ B (f : [Ring] A B),
      (∀ x : A, I x → f x = 0)
      → exists! f_I : [Ring] A_I B, f_I ∘ e = f.

  Definition eqrel : EqRel A.
    unshelve econstructor.
    - move=> x y.
      exact: I (x + Ring.neg y).
    - split.
      + move=> x.
        autorewrite with ring.
        apply: Subgroup.zero.
      + move=> x y H.
        have: I (Ring.neg (x + Ring.neg y)).
        * by apply: Subgroup.neg.
        * by rewrite Ring.addC; autorewrite with ring.
      + move=> x y z H0 H1.
        replace (x + Ring.neg z) with (x + Ring.neg y + (y + Ring.neg z)).
        * by apply: Subgroup.add.
        * by rewrite
            -[(x + _) + _] Ring.addA
            [(Ring.neg y + (_ + _))] Ring.addA
            [Ring.neg y + y] Ring.addC Ring.negI Ring.addL.
  Defined.
End Quotient.
