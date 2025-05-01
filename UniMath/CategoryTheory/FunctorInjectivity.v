Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

(** * Categorical sense for `injective on objects` *)
Section InjectiveOnObjects.
  Variable (C C' : category).
  Variable (F : C ⟶ C').

  Definition is_inj_on_objects : UU
    := ∏ (a b : C), isweq (functor_on_z_iso F (a := a) (b := b)).

  Proposition isaprop_is_inj_on_objects
    : isaprop is_inj_on_objects.
  Proof.
    repeat (apply impred_isaprop; intros).
    apply isapropiscontr.
  Qed.
End InjectiveOnObjects.

Arguments is_inj_on_objects {C C'} F.

Proposition is_inj_on_objects_isInjective
  {C C' : category} (F : C ⟶ C')
  (HC : is_univalent C) (HC' : is_univalent C')
  (HsetC' : isaset (ob C'))
  : is_inj_on_objects F -> isInjective F.
Proof.
  intros H a b.
  use weqhomot.
  - refine ((invweq (make_weq _ (HC' (F a) (F b)))) ∘ _ ∘ (make_weq _ (HC a b)))%weq.
    exact (make_weq _ (H a b)).
  - intros p. apply HsetC'.
Qed.


Section DisplayedFunctorInjectiveOnObjects.
  Variable (C C': category)
    (D : disp_cat C) (D' : disp_cat C')
    (F : C ⟶ C') (FF : disp_functor F D D').

  Definition disp_functor_is_inj_on_objects : UU
    := ∏ (a : C) (xx yy : D a), isweq (disp_functor_on_z_iso_disp FF (xx := xx) (yy := yy) (f := idtoiso (idpath a))).

  Proposition isaprop_disp_functor_is_inj_on_objects
    : isaprop disp_functor_is_inj_on_objects.
  Proof.
    repeat (apply impred_isaprop; intros); apply isapropiscontr.
  Qed.

  Definition disp_functor_is_inj_on_objects' : UU
    := ∏ (a : C), isInjective (disp_functor_on_objects (x := a) FF).

End DisplayedFunctorInjectiveOnObjects.

Arguments disp_functor_is_inj_on_objects {C C' D D' F} FF.
Arguments disp_functor_is_inj_on_objects' {C C' D D' F} FF.

Lemma functor_on_z_iso_idtoiso
  {C C' : category} (F : C ⟶ C')
  : ∏ a : C, functor_on_z_iso F (idtoiso (idpath a)) = idtoiso (idpath (F a)).
Proof.
  intros a. use subtypePath.
  { intro; apply isaprop_is_z_isomorphism. }
  cbn. apply functor_id.
Qed.

Proposition disp_functor_is_inj_on_objects_to_disp_functor_is_inj_on_objects'
  {C C': category}
  {D : disp_cat C} {D' : disp_cat C'}
  {F : C ⟶ C'} (FF : disp_functor F D D')
  (HD : is_univalent_disp D) (HD' : is_univalent_disp D')
  (HsetD' : ∏ a, isaset (D' a))
  : disp_functor_is_inj_on_objects FF -> disp_functor_is_inj_on_objects' FF.
Proof.
  intros H a xx yy.
  use weqhomot.
  - refine (_ ∘ (invweq (make_weq _ (HD' (F a) (F a) (idpath _) (FF a xx) (FF a yy)))) ∘ _ ∘ (make_weq _ (HD a a (idpath _) xx yy)) ∘ _)%weq.
    1,3: rewrite idpath_transportf; apply idweq.
    rewrite <- functor_on_z_iso_idtoiso.
    exact (make_weq _ (H a xx yy)).
  - intros p. apply HsetD'.
Qed.
