From algebra Require Import Foundation.
From algebra Require Category.
From algebra.rings Require Ring RingHom Ideal.

Import Ring.Exports RingHom.Exports Ideal.Exports Category.Exports.

Open Scope type_scope.
Open Scope ring_scope.

Definition kernel {A B : [Ring]} : [Ring] A B → Ideal.type A.
  move=> f.
  unshelve econstructor.
  - unshelve econstructor.
    + move=> x.
      exact: (f x = 0).
    + split => *; try autorewrite with ring; try done.
      * rewrite RingHom.neg -Ring.neg0; by congruence.
      * rewrite RingHom.add -[0] Ring.addL; by congruence.
    - constructor => x y //=.
      autorewrite with ring => ->.
      by autorewrite with ring.
Defined.
