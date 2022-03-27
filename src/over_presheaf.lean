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

@[simps] def obj_mk (X : C) (p : P.obj X) : P.elements := ⟨ X , p ⟩

@[reducible] def hom_mk {X Y : C} {pX : P.obj X} {pY : P.obj Y} (h : X ⟶ Y) (hcomm : P.map h pX = pY) :
  obj_mk X pX ⟶ obj_mk Y pY := ⟨ h , hcomm ⟩




end category_of_elements

namespace presheaves_elements

namespace equivalence_over

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
begin
  dsimp only [hom_mk, category_theory.category_of_elements],
  congr',
  { simp },
  { simp },
  { simpa },
end

lemma map_hom_mk_comp_heq_map_comp_apply {X Y Z : C} {p : P.obj X} {F : P.elements ⥤ Type u₀}
  {h₀ : X ⟶ Y} {h₁ : Y ⟶ Z} (f : F.obj ⟨ X , p ⟩) :
  F.map (hom_mk (h₀ ≫ h₁) rfl) f == F.map (hom_mk h₀ rfl ≫ hom_mk h₁ rfl) f :=
heq.congr_fun (by simp) map_hom_mk_comp_heq_map_comp f

variable (F)

@[simps] def functor_map_obj (F : P.elements ⥤ Type u₀) : C ⥤ Type u₀ :=
{ obj := λ X, Σ p : P.obj X, F.obj ⟨ X , p ⟩,
  map := λ X Y h, λ ⟨ p , f ⟩, ⟨ P.map h p , F.map (hom_mk h rfl) f ⟩,
  map_id' := λ X, funext $ λ ⟨ p , f ⟩,
  by { ext, { simp [functor_map_obj._match_1] },
    { apply heq.trans (map_hom_mk_id_heq_map_id_apply f), simpa }},
  map_comp' := λ X Y Z h₀ h₁, funext $ λ ⟨ p , f ⟩,
  by { ext , { simp [functor_map_obj._match_1] },
    { apply heq.trans (map_hom_mk_comp_heq_map_comp_apply f), simpa }}}

def functor_map : P.elements ⥤ Type u₀ → over P :=
λ F, over.mk (
{ app := sorry,
  naturality' := sorry } : functor_map_obj F ⟶ P)

protected def functor : P.elements ⥤ Type u₀ ⥤ over P :=
{ obj := sorry,
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry }

end equivalence_over

def equivalence_over : (P.elements ⥤ Type u₀) ≌ over P :=
{ functor := sorry,
  inverse := sorry,
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry }

end presheaves_elements
end category_theory
