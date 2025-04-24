(*******************************************************************************

The bicategory of subcategorical comprehension categories

To construct this, we will make use of displayed bicategories,
as we will build on top of the bicategory of full comprehension categories.

A subcategorical comprehension category is a comprehension category,
whose comprehension functor χ is a subcategory inclusion, ie. full, faithful, and injective on objects.\
Full and faithful will be given by the base of full comprehension categories.

Contents
1. The bicategory of subcategorical comprehension categories
2. The univalence of the bicategory of subcategorical comprehension categories
3. Builders and accessors

 *******************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.DispCatTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FibTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.CompCat.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FullCompCat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.

Local Open Scope cat.


(** * The bicategory of subcategorical comprehension categories *)
Definition is_subcategorical (C : full_comp_cat) : UU
  := ∏ x : C, isInjective (disp_functor_on_objects (x := x) (comp_cat_comprehension C)).

Proposition isaprop_is_subcategorical (C : full_comp_cat)
  : isaprop (is_subcategorical C).
Proof.
  apply impred_isaprop; intros x.
  apply impred_isaprop; intros T.
  apply impred_isaprop; intros T'.
  apply isapropisweq.
Qed.

Definition disp_bicat_subcat_comp_cat
  : disp_bicat bicat_full_comp_cat.
Proof.
  use disp_subbicat.
  - exact is_subcategorical.
  - exact (λ _ _ _ _ _, unit).
  - exact (λ _ _, tt).
  - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
Defined.

Definition bicat_subcat_comp_cat : bicat
  := total_bicat disp_bicat_subcat_comp_cat.

(** * Univalence of the bicategory of subcategorical comprehension categories *)
Definition disp_univalent_2_1_disp_bicat_subcat_comp_cat
  : disp_univalent_2_1 disp_bicat_subcat_comp_cat.
Proof.
  apply disp_subbicat_univalent_2_1. intros. apply isapropunit.
Qed.

Definition disp_univalent_2_0_disp_bicat_subcat_comp_cat
  : disp_univalent_2_0 disp_bicat_subcat_comp_cat.
Proof.
  apply disp_subbicat_univalent_2_0.
  - apply is_univalent_2_bicat_full_comp_cat.
  - intros. apply isaprop_is_subcategorical.
  - intros. apply isapropunit.
Qed.

Definition disp_univalent_2_disp_bicat_subcat_comp_cat
  : disp_univalent_2 disp_bicat_subcat_comp_cat.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_subcat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_subcat_comp_cat.
Qed.

Definition is_univalent_2_1_bicat_subcat_comp_cat
  : is_univalent_2_1 bicat_subcat_comp_cat.
Proof.
  apply total_is_univalent_2_1.
  - exact is_univalent_2_1_bicat_full_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_subcat_comp_cat.
Qed.

Definition is_univalent_2_0_bicat_subcat_comp_cat
  : is_univalent_2_0 bicat_subcat_comp_cat.
Proof.
  apply total_is_univalent_2_0.
  - exact is_univalent_2_0_bicat_full_comp_cat.
  - exact disp_univalent_2_0_disp_bicat_subcat_comp_cat.
Qed.

Definition is_univalent_2_bicat_subcat_comp_cat
  : is_univalent_2 bicat_subcat_comp_cat.
Proof.
  apply total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_subcat_comp_cat.
  - exact is_univalent_2_bicat_full_comp_cat.
Qed.

(** * Builders and accessors *)
Definition subcat_comp_cat : UU := bicat_subcat_comp_cat.

Definition make_subcat_comp_cat 
  (C  : full_comp_cat)
  (HC : is_subcategorical C)
  : subcat_comp_cat
  := C ,, HC ,, tt.

Coercion subcat_comp_cat_to_full_comp_cat (C : subcat_comp_cat) : full_comp_cat := pr1 C.

Definition subcat_comp_cat_subcategorical (C : subcat_comp_cat)
  : is_subcategorical C
  := pr12 C.

Definition subcat_comp_cat_functor (C₁ C₂ : subcat_comp_cat) : UU := C₁ --> C₂.

Definition make_subcat_comp_cat_functor {C₁ C₂ : subcat_comp_cat}
  (F : full_comp_cat_functor C₁ C₂)
  : subcat_comp_cat_functor C₁ C₂
  := F ,, tt ,, tt.

Coercion subcat_comp_cat_functor_to_full_comp_cat_functor {C₁ C₂ : subcat_comp_cat}
  (F : subcat_comp_cat_functor C₁ C₂)
  : full_comp_cat_functor C₁ C₂
  := pr1 F.

Definition subcat_comp_cat_nat_trans
  {C₁ C₂ : subcat_comp_cat}
  (F G : subcat_comp_cat_functor C₁ C₂)
  : UU
  := F ==> G.

Coercion subcat_comp_cat_nat_trans_to_full_comp_cat_nat_trans
  {C₁ C₂ : subcat_comp_cat}
  {F G : subcat_comp_cat_functor C₁ C₂}
  (τ : subcat_comp_cat_nat_trans F G)
  : full_comp_cat_nat_trans F G
  := pr1 τ.

Definition make_subcat_comp_cat_nat_trans
  {C₁ C₂ : subcat_comp_cat}
  {F G : subcat_comp_cat_functor C₁ C₂}
  (τ : full_comp_cat_nat_trans F G)
  : subcat_comp_cat_nat_trans F G
  := τ ,, tt ,, tt.
