Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope cat.

(** * Categorical sense for `injective on objects` *)
Section InjectiveOnObjects.
  Variable (C C' : category).
  Variable (F : C ⟶ C').

  Definition is_inj_on_objects' : UU
    := ∏ a b : C, z_iso (F a) (F b) -> z_iso a b.

  Proposition isaprop_is_inj_on_objects'
    : isaprop is_inj_on_objects'.
  Proof.
    repeat (apply impred_isaprop; intros).
    apply isaproptotal2.
  Abort.

  Definition is_inj_on_objects : UU
    := ∏ (a b : C) (f : a --> b), is_z_isomorphism (#F f) -> is_z_isomorphism f.

  Proposition isaprop_is_inj_on_objects
    : isaprop is_inj_on_objects.
  Proof.
    repeat (apply impred_isaprop; intros).
    apply isaprop_is_z_isomorphism.
  Qed.
End InjectiveOnObjects.

Arguments is_inj_on_objects' {C C'} F.
Arguments is_inj_on_objects {C C'} F.

Proposition is_inj_on_objects'_isInjective
  {C C' : category} (F : C ⟶ C')
  (HC : is_univalent C)
  (HsetC : isaset (ob C)) (HsetC' : isaset (ob C'))
  : is_inj_on_objects' F -> isInjective F.
Proof.
  intros H a b.
  use isweq_iso.
  - intros p. apply HC. apply H. apply idtoiso. exact p.
  - intros p. cbn. apply HsetC.
  - intros p. cbn. apply HsetC'.
Qed.

Proposition is_inj_on_objects_isInjective
  {C C' : category} (F : C ⟶ C')
  (HC : is_univalent C)
  (ff : fully_faithful F)
  (HsetC : isaset (ob C)) (HsetC' : isaset (ob C'))
  : is_inj_on_objects F -> isInjective F.
Proof.
  intros H a b. use isweq_iso.
  - intros p. apply HC. destruct (idtoiso p) as [Ff HFf].
    exists (fully_faithful_inv_hom ff _ _ Ff).
    apply H.
    exact (transportb is_z_isomorphism (functor_on_fully_faithful_inv_hom _ _ _) HFf).
  - intros p. simpl. apply HsetC.
  - intros p. simpl. apply HsetC'.
Qed.


Section DisplayedFunctorInjectiveOnObjects.
  Variable (C : category)
    (D D' : disp_cat C).

  disp_functor
