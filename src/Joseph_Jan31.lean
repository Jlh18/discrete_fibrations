import category_theory.category.Cat
import category_theory.limits.constructions.pullbacks


-- TODO category_theory/limits defines instance category Type u ✓
-- TODO Find has_pullback ✓ category_theory/limit/shapes/pullback
-- TODO Cat of Cats has pullback
-- TODO Show that category of elements of a functor into Set is the pullback
--      in the category of

/-!
# The category of categories is complete

This file contains constructions of all 1-limits
in the category `Cat` of all categories, treated as a 1-category.

-- TODO sketch the proof

## Implementation notes

It is better to refer to morphisms in Cat using ⟶ (\hom)
rather than ⥤ (\functor) for lean to infer instances.
-/


universes u v

open category_theory
open category_theory.limits
open category_theory.prod
-- GOAL show Cat of Cats has pullbacks



namespace Cat

/-- The product of two categories is a category (category_theory.products.basic) -/
def prod (C D : Cat.{v u}) : Cat.{v u} :=
{ α := (C.α × D.α) }

/-- The product of two categories as a cone over the pair diagram -/
def prod_cone_pair (C D : Cat.{v u}) : cone (pair C D) :=
{ X := prod C D,
  π := map_pair (fst _ _) (snd _ _) }

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
  { dsimp only [lift, prod_map, limits.binary_fan.π_app_left],
    rw ← (congr_arg functor.obj (h walking_pair.left)),
    refl },
  { dsimp only [lift, prod_map, limits.binary_fan.π_app_right],
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

/-- The product of categories (as a cone over the pair diagram) is a 1-limit -/
def is_limit_prod_cone_pair :
  is_limit (prod_cone_pair C D) :=
{
  lift := is_limit_prod_cone_pair.lift,
  fac' := is_limit_prod_cone_pair.fac,
  uniq' := is_limit_prod_cone_pair.uniq,
}

/-- The product of categories C × D forms 1-product in the category of categories -/
def limit_cone_prod_cone_pair : limit_cone (pair C D) :=
{
  cone := prod_cone_pair C D,
  is_limit := is_limit_prod_cone_pair
}

instance has_limit_pair : has_limit (pair C D) :=
⟨⟨ limit_cone_prod_cone_pair ⟩⟩

instance has_binary_products : has_binary_products Cat.{v u} :=
has_binary_products_of_has_limit_pair _

variables (F G : C ⟶ D)

-- THIS SEEMS A BIT DODGY!!
/-- The equalizer category of two functors (as a subcategory of the source category C) -/
def equalizer : Cat.{v u} :=
{ α := { c : C // ∃ (hc : F.obj c = G.obj c),
  (∀ (d : C) (f : c ⟶ d) (hd : G.obj d = F.obj d),
  F.map f = eq_to_hom hc ≫ G.map f ≫ eq_to_hom hd) }
}

/-- The map embedding the equalizer of two functors into the source category -/
def fork_ι : equalizer F G ⟶ C := full_subcategory_inclusion _

lemma fork_condition : fork_ι F G ≫ F = fork_ι F G ≫ G :=
category_theory.functor.ext (λ ⟨ _ , h , _ ⟩, h ) $
λ ⟨ c , _ , hc2 ⟩ ⟨ d , hd1 , hd2 ⟩ f ,
calc (fork_ι F G ≫ F).map f = F.map f : rfl
                             ... = _  : hc2 d f hd1.symm

/-- The equalizer of two functors as a cone over the parallel pair diagram (called a fork) -/
def fork : fork F G :=
fork.of_ι (fork_ι F G) (fork_condition _ _)

variables {F G}

namespace is_limit_fork

-- def lift (c : category_theory.limits.fork F G) : c.X ⟶ (fork F G).X :=
-- {
--   obj := λ x, ⟨ c.ι.obj x , congr_arg (λ F', functor.obj F' x) c.condition ,
--     (λ y f hy,
--     begin
--       have h0 := congr_arg (λ F', functor.obj F' x) c.condition,
--       have h'' := congr_arg (λ F' : c.X ⥤ D, F'.map) c.condition,

--     end) ⟩,
--   map := sorry
-- }


end is_limit_fork

/-- The equalizer of two functors (as a cone/fork) is a limit -/
def is_limit_fork :
  is_limit (fork F G) :=
fork.is_limit.mk (fork F G) sorry sorry sorry

def limit_cone_parallel_pair : limit_cone (parallel_pair F G) :=
{
  cone := fork F G,
  is_limit := is_limit_fork
}

instance has_limit_parallel_pair : has_limit (parallel_pair F G) :=
⟨⟨ limit_cone_parallel_pair ⟩⟩

instance has_equalizers : has_equalizers Cat.{v u} :=
has_equalizers_of_has_limit_parallel_pair _

end Cat

-- instance : has_limits Cat.{v u} := sorry

-- instance has_equalizers : has_equalizers Cat.{v u} := sorry

-- instance has_pullbacks : has_pullbacks Cat.{v u} :=
-- by apply_instance
