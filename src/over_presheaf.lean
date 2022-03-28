import category_theory.functor_category
import category_theory.types
import category_theory.over
import category_theory.elements
import category_theory.limits.shapes.products

universes v₀ u₀ v₁ u₁

namespace heq

lemma congr_fun {α β₀ β₁ : Type*} {f₀ : α → β₀} {f₁ : α → β₁} (hβ : β₀ = β₁) (hf : f₀ == f₁)
  (a : α) : f₀ a == f₁ a := by { subst hβ, subst hf }

protected lemma funext {α β₀ β₁ : Type*} {f₀ : α → β₀} {f₁ : α → β₁} (hβ : β₀ = β₁)
  (hf : Π a, f₀ a == f₁ a) : f₀ == f₁ :=
by { subst hβ, apply heq_of_eq, funext, exact eq_of_heq (hf _), }

end heq

namespace category_theory

variables {C : Type u₀} [category.{v₀} C] {P : C ⥤ Type u₀}

namespace category_of_elements

/-- Explicit, typed construction of an object in category of elements -/
@[simps] def obj_mk (X : C) (p : P.obj X) : P.elements := ⟨ X , p ⟩

/-- Explicit, typed construction of a hom in category of elements -/
@[reducible] def hom_mk {X Y : C} {pX : P.obj X} {pY : P.obj Y} (h : X ⟶ Y) (hcomm : P.map h pX = pY) :
  obj_mk X pX ⟶ obj_mk Y pY := ⟨ h , hcomm ⟩

end category_of_elements

namespace presheaf_elements

open category_of_elements

variables {F : P.elements ⥤ Type u₀} {X Y Z : C} {p : P.obj X}

lemma map_hom_mk_id_heq_map_id
  {X : C} {p : P.obj X} {F : P.elements ⥤ Type u₀} :
  (F.map (hom_mk (𝟙 X) rfl) : F.obj ⟨ X , p ⟩ ⟶ F.obj ⟨ X , P.map (𝟙 X) p⟩)
    == F.map (𝟙 ⟨ X , p ⟩) :=
by { dsimp only [hom_mk, obj_mk, category_theory.category_of_elements], congr', {simp}, {simp} }

lemma map_hom_mk_id_heq_map_id_apply
  {X : C} {p : P.obj X} {F : P.elements ⥤ Type u₀} (f : F.obj ⟨ X , p ⟩) :
  F.map (hom_mk (𝟙 X) rfl) f == F.map (𝟙 _) f :=
heq.congr_fun (by simpa) map_hom_mk_id_heq_map_id f

lemma map_hom_mk_comp_heq_map_comp {X Y Z : C} {p : P.obj X} {F : P.elements ⥤ Type u₀}
  {h₀ : X ⟶ Y} {h₁ : Y ⟶ Z} :
  (F.map (hom_mk (h₀ ≫ h₁) rfl) : F.obj ⟨ X , p ⟩ ⟶ F.obj ⟨ Z , P.map (h₀ ≫ h₁) p ⟩)
    == F.map ((hom_mk h₀ rfl : obj_mk X p ⟶ obj_mk Y (P.map h₀ p)) ≫ hom_mk h₁ rfl) :=
by { congr'; simp }

lemma map_hom_mk_comp_heq_map_comp_apply {X Y Z : C} {p : P.obj X} {F : P.elements ⥤ Type u₀}
  {h₀ : X ⟶ Y} {h₁ : Y ⟶ Z} (f : F.obj ⟨ X , p ⟩) :
  F.map (hom_mk (h₀ ≫ h₁) rfl) f == F.map (hom_mk h₀ rfl ≫ hom_mk h₁ rfl) f :=
heq.congr_fun (by simp) map_hom_mk_comp_heq_map_comp f

variable (F)

/--
  Given a presheaf on the category of elements `F : P.elements ⥤ Type`
  construct a presheaf `category_theory.presheaf_elements.functor_obj_left F : C ⥤ Type`
  by taking sums on objects.
  This process is functorial by `category_theory.presheaf_elements.to_presheaf`
-/
@[simps] def to_presheaf_obj : C ⥤ Type u₀ :=
{ obj := λ X, Σ p : P.obj X, F.obj ⟨ X , p ⟩,
  map := λ X Y h, λ ⟨ p , f ⟩, ⟨ P.map h p , F.map (hom_mk h rfl) f ⟩,
  map_id' := λ X, funext $ λ ⟨ p , f ⟩,
  by { ext, { simp [to_presheaf_obj._match_1] },
    { apply heq.trans (map_hom_mk_id_heq_map_id_apply f), simpa }},
  map_comp' := λ X Y Z h₀ h₁, funext $ λ ⟨ p , f ⟩,
  by { ext , { simp [to_presheaf_obj._match_1] },
    { apply heq.trans (map_hom_mk_comp_heq_map_comp_apply f), simpa }}}

variables {F} {G : P.elements ⥤ Type u₀}

/--
  Given a natural transformation of presheaves on the category of elements
  construct a natural transformation between the induced presheaves.
  Part of the definition `category_theory.presheaf_elements.to_presheaf`
-/
@[simps] def to_presheaf_map (α : F ⟶ G) : to_presheaf_obj F ⟶ to_presheaf_obj G :=
{ app := λ X ⟨ p , f ⟩, ⟨ p , nat_trans.app α _ f ⟩,
  naturality' := λ X Y h, funext $ λ ⟨ p , f ⟩, by { ext,
    { simp [to_presheaf_map._match_1, to_presheaf_obj] },
    { apply heq_of_eq, exact congr_fun
      (@nat_trans.naturality _ _ _ _ _ _ α ⟨ X , p ⟩ ⟨ Y , P.map h p ⟩ ⟨ h , rfl ⟩) f }}}

/--
  A functor that takes presheaves on the category of elements `P.elements ⥤ Type`
  and constructs presheaves `C ⥤ Type` by taking sums on objects.
  This forms an equivalence of categories between presheaves on the category of elements.
  See `category_theory.presheaf_elements.equivalence`
-/
@[simps] def to_presheaf : (P.elements ⥤ Type u₀) ⥤ C ⥤ Type u₀ :=
{ obj := to_presheaf_obj,
  map := λ _ _, to_presheaf_map }

/--
  The functor `category_theory.presheaf_elements.to_presheaf` but as a functor to the
  over category `over P`.
  See `category_theory.presheaf_elements.equivalence`
-/
@[simps] def to_presheaf_over : (P.elements ⥤ Type u₀) ⥤ over P :=
{ obj := λ F, over.mk ({ app := λ X, sigma.fst } : to_presheaf_obj F ⟶ P),
  map := λ F G α, over.hom_mk (to_presheaf_map α) }.

section inverse_obj

variables (Q : over P)

@[simp] def inverse_obj_obj : P.elements → Type u₀ :=
λ ⟨ X , p ⟩, { q : Q.left.obj X // Q.hom.app X q = p }

@[simp] def inverse_obj_map : Π (X Y : P.elements) (h : X ⟶ Y),
  inverse_obj_obj Q X ⟶ inverse_obj_obj Q Y :=
λ ⟨ X , pX ⟩ ⟨ Y , pY ⟩ ⟨ h , hcomm ⟩ ⟨ qX , hqX ⟩,
  ⟨ Q.left.map h qX , by { convert hcomm, rw ← hqX, exact congr_fun (Q.hom.naturality h) qX } ⟩

lemma inverse_obj_map_comp : Π (X Y Z : P.elements) (f : X ⟶ Y) (g : Y ⟶ Z),
  inverse_obj_map Q X Z (f ≫ g) = inverse_obj_map Q X Y f ≫ (inverse_obj_map Q Y Z g) :=
λ ⟨ X , pX ⟩ ⟨ Y , pY ⟩ ⟨ Z , pZ ⟩ ⟨ f , fcomm ⟩ ⟨ g , gcomm ⟩, funext $ λ ⟨ qX , hqX ⟩,
by { dsimp only [category_theory.category_of_elements], simp }

@[simps] def inverse_obj : P.elements ⥤ Type u₀ :=
{ obj := inverse_obj_obj Q,
  map := λ _ _, inverse_obj_map Q _ _,
  map_id' := λ ⟨ X , p ⟩, funext $ λ ⟨ q , hq ⟩,
    by { dsimp only [category_theory.category_of_elements], simp },
  map_comp' := λ _ _ _, inverse_obj_map_comp _ _ _ _ }

end inverse_obj

section inverse_map

variables {Q₀ Q₁ : over P} (ν : Q₀ ⟶ Q₁)

def inverse_map : (inverse_obj Q₀ ⟶ inverse_obj Q₁) :=
{ app := _,
  naturality' := _ }

end inverse_map

def inverse : over P ⥤ P.elements ⥤ Type u₀ :=
{ obj := inverse_obj,
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry }

def equivalence : (P.elements ⥤ Type u₀) ≌ over P :=
{ functor := to_presheaf_over,
  inverse := inverse,
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry }

end presheaf_elements

end category_theory
