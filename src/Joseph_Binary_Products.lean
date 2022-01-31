import category_theory.category.Cat
import category_theory.limits.constructions.pullbacks


-- TODO category_theory/limits defines instance category Type u ✓
-- TODO Find has_pullback ✓ category_theory/limit/shapes/pullback
-- TODO Cat of Cats has pullback
-- TODO Show that category of elements of a functor into Set is the pullback
--      in the category of

universes u v

open category_theory
open category_theory.limits

-- GOAL show Cat of Cats has pullbacks



namespace Cat

/-- The product of two categories is a category (category_theory.products.basic) -/
def prod (C D : Cat.{v u}) : Cat.{v u} :=
{ α := (C.α × D.α) }

/-- The product of two categories as a cone over the pair diagram -/
def prod_cone_pair (C D : Cat.{v u}) : cone (pair C D) :=
{ X := prod C D,
  π := map_pair (category_theory.prod.fst _ _) (category_theory.prod.snd _ _) }

variables {C D E : Cat.{v u}}

/-- Existence part of the universal property of products -/
def prod_map (f : E ⟶ C) (g : E ⟶ D) : (E ⟶ prod C D) :=
{
  obj := λ z, ⟨ f.obj z , g.obj z ⟩,
  map := λ _ _ h, ⟨ f.map h , g.map h ⟩,
}

lemma eq_to_hom_fst {X Y : C × D} (h : X = Y) :
  prod.fst (eq_to_hom h) = eq_to_hom (congr_arg prod.fst h) :=
by cases h; refl

lemma eq_to_hom_snd {X Y : C × D} (h : X = Y) :
  prod.snd (eq_to_hom h) = eq_to_hom (congr_arg prod.snd h) :=
by cases h; refl

-- lemma eq_to_hom_snd' {X Y : C} {Z W : D} (hXY : X = Y) (hZW : Z = W) :
--   (@eq_to_hom (C × D) _ ⟨ X , Z ⟩ ⟨ Y , W ⟩ (prod.ext hXY hZW)).snd = eq_to_hom hZW :=
-- by cases hXY; cases hZW; refl

namespace is_limit_prod_cone_pair

/-- Existence part of the universal property of products -/
def lift (c : cone (pair C D)) :
  c.X ⟶ (prod_cone_pair C D).X :=
prod_map (c.π.app walking_pair.left) (c.π.app walking_pair.right)

lemma fac (c : cone (pair C D)) (j : walking_pair) :
  lift c ≫ (prod_cone_pair C D).π.app j = c.π.app j :=
category_theory.functor.ext (by intro _; cases j; refl) (by intros; cases j;
  {simpa only [eq_to_hom_refl, category.comp_id, category.id_comp]})

/-- Uniqueness part of the universal property of products -/
lemma uniq
  (c : cone (pair C D)) (F : c.X ⟶ prod C D)
  (h : ∀ (j : discrete walking_pair), F ≫ (prod_cone_pair C D).π.app j = c.π.app j) :
  F = lift c :=
category_theory.functor.ext
begin
  intro,
  apply prod.ext,
  { dsimp only [lift, prod_map, category_theory.limits.binary_fan.π_app_left],
    rw ← (congr_arg functor.obj (h walking_pair.left)),
    refl },
  { dsimp only [lift, prod_map, category_theory.limits.binary_fan.π_app_right],
    rw ← (congr_arg functor.obj (h walking_pair.right)),
    refl },
end
begin
  intros i j ϕ,
  apply prod.ext,
  { convert functor.congr_hom (h walking_pair.left) ϕ,
    simpa only [prod_comp_fst, eq_to_hom_fst] },
  { convert functor.congr_hom (h walking_pair.right) ϕ,
    simpa only [prod_comp_snd, eq_to_hom_snd] },
end

end is_limit_prod_cone_pair

/-- The product of categories C × D forms 1-product in the category of categories -/
def is_limit_prod_cone_pair {C D : Cat.{v u}} :
  is_limit (@prod_cone_pair C D) :=
{
  lift := is_limit_prod_cone_pair.lift,
  fac' := is_limit_prod_cone_pair.fac,
  uniq' := is_limit_prod_cone_pair.uniq,
}

instance has_limit_pair {C D : Cat.{v u}} : has_limit (pair C D) :=
⟨⟨⟨ prod_cone_pair C D , is_limit_prod_cone_pair ⟩⟩⟩

instance has_binary_products : has_binary_products Cat.{v u} :=
has_binary_products_of_has_limit_pair _

-- instance : has_limits Cat.{v u} := sorry

-- instance has_equalizers : has_equalizers Cat.{v u} := sorry

-- instance has_pullbacks : has_pullbacks Cat.{v u} :=
-- by apply_instance


end Cat
