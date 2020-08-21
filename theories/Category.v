From algebra Require Import Foundation.

Set Primitive Projections.
Set Universe Polymorphism.

Declare Scope cat.

Module Class.
  Section Laws.
    Context {O : Type} {H : O → O → Type}.
    Variable (idn : ∀ x, H x x) (seq : ∀ {x y z}, H x y → H y z → H x z).
    Record laws : Prop :=
      {seqL : ∀ {x y} (f : H x y), seq (idn _) f = f;
       seqR : ∀ {x y} (f : H x y), seq f (idn _) = f;
       seqA : ∀ {w x y z} (f : H w x) (g : H x y) (h : H y z), seq (seq f g) h = seq f (seq g h)}.
  End Laws.

  Record axioms (O : Type) (H : O → O → Type) :=
    Class
      {idn : ∀ x, H x x;
       seq : ∀ x y z, H x y → H y z → H x z;
       _laws : laws idn seq}.
End Class.

Record type := Pack {ob; hom; class : Class.axioms ob hom}.

Module Coercions.
  Coercion ob : type >-> Sortclass.
  Coercion hom : type >-> Funclass.
End Coercions.


Definition make_class :
  ∀ (O : Type)
    (H : O → O → Type)
    (idn : ⟨ "idn" ∷ ∀ {x}, H x x ⟩)
    (seq : ⟨ "seq" ∷ ∀ {x y z}, H x y → H y z → H x z ⟩),
    Class.laws (!idn) (!seq)
    → Class.axioms O H.
Proof.
  move=> O H [idn] [seq].
  econstructor; eauto.
Defined.

Import Coercions.

Section Operations.
  Context {𝒞 : type}.
  Definition idn := Class.idn _ _ (class 𝒞).
  Definition seq {x y z} (f : 𝒞 x y) (g : 𝒞 y z) := Class.seq _ _ (class 𝒞) _ _ _ f g.
  Definition cmp {x y z} (g : 𝒞 y z) (f : 𝒞 x y) := seq f g.
End Operations.

Module Notations.
  Infix "≫" := seq (at level 60).
  Infix "∘" := cmp (at level 60).
End Notations.

Import Notations.

Section Laws.
  Context {𝒞 : type}.

  Local Definition laws := Class._laws 𝒞 (hom 𝒞) (class 𝒞).
  Local Hint Resolve laws : core.

  Section UnitsLaws.
    Context {x y : 𝒞} {f : 𝒞 x y}.

    Fact seqL : idn _ ≫ f = f.
    Proof. by rewrite /seq /idn Class.seqL. Qed.

    Fact seqR : f ≫ idn _ = f.
    Proof. by rewrite /seq /idn Class.seqR. Qed.

    Fact cmpL : idn _ ∘ f = f.
    Proof. by rewrite /cmp seqR. Qed.

    Fact cmpR : f ∘ idn _ = f.
    Proof. by rewrite /cmp seqL. Qed.
  End UnitsLaws.

  Fact seqA : ∀ {w x y z} (f : 𝒞 w x) (g : 𝒞 x y) (h : 𝒞 y z), (f ≫ g) ≫ h = f ≫ (g ≫ h).
  Proof. move=> *; by rewrite /seq (Class.seqA _ _ laws). Qed.

  Local Fact unfold_cmp : ∀ x y z (f : 𝒞 x y) (g : 𝒞 y z), g ∘ f = f ≫ g.
  Proof. done. Qed.
End Laws.

Hint Rewrite @unfold_cmp @seqL @seqR @seqA : cat.

Definition to_tuple : type → {ob : Type & {hom : ob → ob → Type & {idn : ∀ x, hom x x & ∀ x y z, hom x y → hom y z → hom x z}}}.
Proof.
  move=> [? ? []]; econstructor; eauto.
Defined.


Lemma extensionality : ∀ 𝒞 𝒟, to_tuple 𝒞 = to_tuple 𝒟 → 𝒞 = 𝒟.
Proof.
  move=> [obC homC [idnC seqC clC]] [obD homD [idnD seqD clD]] Q.
  proj_eq Q obC obD.
  proj_eq Q homC homD.
  proj_eq Q idnC idnD.
  proj_eq Q seqC seqD.
  replace clC with clD; auto.
Qed.

Instance cat_ext : ExtLaw type _ :=
  {ext_law := extensionality}.

Module Exports.
  Export Notations.
  Export Coercions.
End Exports.

Ltac make :=
  unshelve apply: Pack.

Ltac axioms :=
  unshelve apply: make_class.

Example TYPE : type.
make.
- exact Type.
- move=> A B.
  exact (A → B).
- axioms.
  + axiom "idn"; auto.
  + axiom "seq"; auto.
  + abstract (split; auto).
Defined.

Example Op (𝒞 : type) : type.
make.
- exact: 𝒞.
- move=> x y.
  exact: (𝒞 y x).
- axioms.
  + axiom "idn"; apply: idn.
  + axiom "seq" => *; apply: seq; eauto.
  + abstract (split => *//=; by autorewrite with cat).
Defined.
