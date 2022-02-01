import category_theory.category.Cat
import category_theory.limits.constructions.pullbacks
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.pi.basic

-- TODO Show that category of elements of a functor into Set is pullback
--      in the category of categories

/-!
# The category of (small) categories is complete

This file contains constructions of all (small) 1-limits
in the category `Cat` of all categories, treated as a 1-category.
We use the result `limits_from_equalizers_and_products`.
We construct binary products, dependent products, fiber products/pullbacks,
and equalizers in the category of Categories.

## Implementation notes

`Cat.{v u}` in general (i.e. not small) does not have all small limits.
If it were then it would be closed under products,
which could have index `I : max v u` as big as the morphisms (functors).
However the product category `Π i : I, C i : Type (max v u)`
is too large to be an object in `Cat.{v u}`.

It is better to refer to morphisms in `Cat` using `⟶ (\hom)`
rather than `⥤ (\functor)` for lean to infer instances.
-/


universes u v w

namespace category_theory

open category_theory.limits
open category_theory.prod

/-- The natural transformation between two functors out of discrete I,
specified by its components. -/
def map_pi {I : Type w} {C : Type u} [category.{v} C] {F G : discrete I ⥤ C}
  (on_obj : Π i : I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := on_obj }

namespace Cat

section prod

/-- The product of two categories is a category (category_theory.products.basic) -/
def prod (C D : Cat.{v u}) : Cat.{v u} :=
{ α := (C.α × D.α) }

/-- The product of two categories as a cone over the pair diagram -/
def prod_cone (C D : Cat.{v u}) : cone (pair C D) :=
{ X := prod C D,
  π := map_pair (fst _ _) (snd _ _) }

variables {C D E : Cat.{v u}}

/-- Existence part of the universal property of products -/
def prod_map (f : E ⟶ C) (g : E ⟶ D) : (E ⟶ prod C D) :=
{ obj := λ z, ⟨ f.obj z , g.obj z ⟩,
  map := λ _ _ h, ⟨ f.map h , g.map h ⟩ }

-- not my work, due to Xu Junyan on Zulip.
-- A sensible lemma for refactoring a map into the limit
-- I imitate this strategy later on.
lemma self_eq_prod_map (F : E ⟶ prod C D) : F = prod_map (F ≫ fst _ _) (F ≫ snd _ _) :=
functor.hext (λ x, prod.ext rfl rfl)
(λ x y f, heq_of_eq (prod.ext rfl rfl))

lemma prod_map_fst {F : E ⟶ C} (G : E ⟶ D) :
  prod_map F G ≫ fst _ _ = F :=
by { cases F, refl }

lemma prod_map_snd {F : E ⟶ C} (G : E ⟶ D) :
  prod_map F G ≫ snd _ _ = G :=
by { cases G, refl }

namespace is_limit_prod_cone

/-- Existence part of the universal property of products -/
def lift (c : cone (pair C D)) :
  c.X ⟶ (prod_cone C D).X :=
prod_map (c.π.app walking_pair.left) (c.π.app walking_pair.right)

lemma fac (c : cone (pair C D)) (j : walking_pair) :
  lift c ≫ (prod_cone C D).π.app j = c.π.app j :=
walking_pair.cases_on j (prod_map_fst _) (prod_map_snd _)
-- this proof used to be 2 lines long, using functor.ext
-- thanks to Xu Junyan on Zulip who changed prod_map_fst and prod_map_snd for this golf

/-- Uniqueness part of the universal property of products -/
lemma uniq
  (c : cone (pair C D)) (F : c.X ⟶ prod C D)
  (h : ∀ (j : discrete walking_pair), F ≫ (prod_cone C D).π.app j = c.π.app j) :
  F = lift c :=
by { rw self_eq_prod_map F, congr; convert h _; refl }
-- this proof used to be 18 lines long, using functor.ext
-- thanks to Xu Junyan on Zulip who made self_eq_prod_map for this golf

end is_limit_prod_cone

/-- The product of categories (as a cone over the pair diagram) is a 1-limit -/
def is_limit_prod_cone :
  is_limit (prod_cone C D) :=
{ lift := is_limit_prod_cone.lift,
  fac' := is_limit_prod_cone.fac,
  uniq' := is_limit_prod_cone.uniq }

/-- The product of categories C × D forms 1-product in the category of categories -/
def limit_cone_prod_cone : limit_cone (pair C D) :=
{ cone := prod_cone C D,
  is_limit := is_limit_prod_cone }

instance has_limit_pair : has_limit (pair C D) :=
⟨⟨ limit_cone_prod_cone ⟩⟩

instance has_binary_products : has_binary_products Cat.{v u} :=
has_binary_products_of_has_limit_pair _

end prod

section equalizer

variables {C D E : Cat.{v u}} (F G : C ⟶ D)

-- /-- The equalizer category of two functors (as a subcategory of the source category C)
-- def equalizer.str' : category.{v} { c : C // F.obj c = G.obj c } :=
-- {
--   hom := λ x y,
--     { f : x.1 ⟶ y.1 // @cast _
--       (G.obj x.val ⟶ G.obj y.val) (by rw [x.2, y.2]) (F.map f) == G.map f },
--   id := λ x, ⟨ 𝟙 x , by { cases x with _ hx, dsimp,
--     simp only [category_theory.functor.map_id], rw hx } ⟩,
--   comp := λ x y z f g, ⟨ f.1 ≫ g.1 ,
--     begin
--       cases f with f hf,
--       cases g with g hg,
--       dsimp,
--       simp only [category_theory.functor.map_comp],
      -- calc F.map f ≫ F.map g == @cast _ (G.obj x.1 ⟶ G.obj z.1)
      --   (by {rw [x.2, z.2], }) (F.map f ≫ F.map g) : (cast_heq _ _).symm
      --                    ... == cast _ (F.map f) ≫ cast _ (F.map g) : heq_of_eq _
      --                    ... == cast hf.symm (F.map f) ≫ G.map g : heq_of_eq _
      --                    ... == G.map f ≫ G.map g : by rw (cast_heq _ _)
      -- apply heq_of_cast_eq
      --   (by {rw x.2 , rw z.2} : (F.obj x.val ⟶ F.obj z.val)
      --     = (G.obj x.val ⟶ G.obj z.val)),

    --   sorry,

    -- end  ⟩
  -- comp := λ x y z f g, ⟨ f.1 ≫ g.1 ,
  -- begin
  --   have hf := f.2, simp only [subtype.val_eq_coe] at hf,
  --   have hg := g.2, simp only [subtype.val_eq_coe] at hg,
  --   dsimp,
  --   simp only [category_theory.category.assoc,
  --     category_theory.functor.map_comp, hf, hg],
  --   dsimp,
  --   simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
  -- end
  -- ⟩,
-- }

/-- The equalizer category of two functors (as a subcategory of the source category C) -/
def equalizer.str' : category.{v} { c : C // F.obj c = G.obj c } :=
{
  hom := λ x y,
    { f : x.1 ⟶ y.1 // F.map f = eq_to_hom x.2 ≫ G.map f ≫ eq_to_hom y.2.symm },
  id := λ x, ⟨ 𝟙 x , by dsimp; simp only [category_theory.category.id_comp,
    category_theory.eq_to_hom_refl, eq_self_iff_true,
    category_theory.eq_to_hom_trans, category_theory.functor.map_id] ⟩,
  comp := λ x y z f g, ⟨ f.1 ≫ g.1 ,
  begin
    have hf := f.2, simp only [subtype.val_eq_coe] at hf,
    have hg := g.2, simp only [subtype.val_eq_coe] at hg,
    dsimp,
    simp only [category_theory.category.assoc,
      category_theory.functor.map_comp, hf, hg],
    dsimp,
    simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
  end ⟩,
}

/-- The equalizer category of two functors (as an object in Cat) -/
def equalizer : Cat.{v u} :=
{
  α := { c : C // F.obj c = G.obj c },
  str := equalizer.str' _ _
}

/-- The map embedding the equalizer of two functors into the source category -/
def fork_ι : equalizer F G ⟶ C :=
{
  obj := subtype.val,
  map := λ _ _, subtype.val,
}
lemma fork_condition : fork_ι F G ≫ F = fork_ι F G ≫ G :=
category_theory.functor.ext (λ ⟨ _ , h ⟩, h ) $
λ x y f , f.2

/-- The equalizer of two functors as a cone over the parallel pair diagram (called a fork) -/
def fork : fork F G :=
fork.of_ι (fork_ι F G) (fork_condition _ _)

variables {F G}

namespace is_limit_fork

/-- Existence part of the universal property of equalizers -/
def lift (c : category_theory.limits.fork F G) : c.X ⟶ (fork F G).X :=
{
  obj := λ x, ⟨ c.ι.obj x , congr_arg (λ F', functor.obj F' x) c.condition ⟩,
  map := λ x y f, ⟨ c.ι.map f , by convert functor.congr_hom c.condition f ⟩,
}

-- lemma self_eq_lift (c : category_theory.limits.fork F G) :
--   c.π = lift c :=
-- functor.hext (λ x, prod.ext rfl rfl)
-- (λ x y f, heq_of_eq (prod.ext rfl rfl))

lemma eq_to_hom.val {x y : equalizer F G} (h : x = y) :
  (@eq_to_hom (equalizer F G) _ _ _ h).val = eq_to_hom (by rw h) :=
by cases h; refl

lemma fac (c : category_theory.limits.fork F G) :
  is_limit_fork.lift c ≫ (fork F G).ι = c.ι :=
functor.hext (λ _, rfl) (λ x y f, by { apply heq_of_eq, dsimp only [(≫)], simpa })

/-- Uniqueness part of the universal property of equalizers -/
lemma uniq (c : category_theory.limits.fork F G) (m : c.X ⟶ (fork F G).X)
  (h : ∀ (j : walking_parallel_pair), m ≫ (fork F G).π.app j = c.π.app j) :
  m = is_limit_fork.lift c :=
category_theory.functor.ext
  ( λ x, subtype.ext $ -- just check the C objects
  calc (m.obj x).1 = (fork F G).ι.obj (m.obj x) : rfl
               ... = (m ≫ (fork F G).ι).obj x : rfl
               ... = (m ≫ (fork F G).π.app walking_parallel_pair.zero).obj x : rfl
               ... = (c.π.app walking_parallel_pair.zero).obj x :
                 by rw (h walking_parallel_pair.zero)
               ... = ((lift c).obj x).1 : rfl )
  ( λ x y f, subtype.ext $ -- just check the C morphisms
  calc (m.map f).1 = (fork F G).ι.map (m.map f) : rfl
               ... = (m ≫ (fork F G).ι).map f : rfl
               ... = (m ≫ (fork F G).π.app walking_parallel_pair.zero).map f : rfl
               ... = eq_to_hom _ ≫ (c.π.app walking_parallel_pair.zero).map f ≫ eq_to_hom _ :
                 functor.congr_hom (h walking_parallel_pair.zero) f
               ... = (eq_to_hom _ ≫ (lift c).map f ≫ eq_to_hom _).1 :
                 by congr; simpa only [eq_to_hom.val] )

end is_limit_fork

open is_limit_fork

/-- The equalizer of two functors (as a cone/fork) is a limit -/
def is_limit_fork : is_limit (fork F G) :=
fork.is_limit.mk (fork F G) lift fac uniq

/-- The equalizer of two functors (as a cone/fork) is a limit -/
def limit_cone_parallel_pair : limit_cone (parallel_pair F G) :=
{
  cone := fork F G,
  is_limit := is_limit_fork
}

instance has_limit_parallel_pair : has_limit (parallel_pair F G) :=
⟨⟨ limit_cone_parallel_pair ⟩⟩

instance has_equalizers : has_equalizers Cat.{v u} :=
has_equalizers_of_has_limit_parallel_pair _

end equalizer

def pi {I : Type u} (F : discrete I ⥤ Cat.{u u}) : Cat.{u u} :=
{ α := Π i : I, F.obj i }

namespace pi

variables {C : Cat.{u u}} {I : Type u} {F : discrete I ⥤ Cat.{u u}}

def lift (legs : Π i : I, C ⟶ F.obj i) : C ⟶ pi F :=
{ obj := λ x i, (legs i).obj x,
  map := λ _ _ f i, (legs i).map f }

lemma self_eq_lift (G : C ⟶ pi F) : G = lift (λ i, G ≫ pi.eval _ _) :=
by {cases G, refl}

variable (F)

def cone : cone F :=
{ X := pi F ,
  π := map_pi $ pi.eval _ }

namespace is_limit_cone

variable {F}

def lift (c : limits.cone F) : c.X ⟶ (cone F).X :=
lift (λ i, c.π.app i)

lemma fac (c : limits.cone F) (i : discrete I) :
  lift c ≫ (cone F).π.app i = c.π.app i :=
by { rw self_eq_lift (lift c), apply functor.hext; { intros, refl } }

lemma uniq (c : limits.cone F) (m : c.X ⟶ (cone F).X)
  (h : ∀ (j : discrete I), m ≫ (cone F).π.app j = c.π.app j) :
  m = is_limit_cone.lift c :=
by { unfold lift, simp_rw ← h, apply functor.hext; { intros, refl } }

end is_limit_cone

def is_limit_cone : is_limit (cone F) :=
{ lift := is_limit_cone.lift,
  fac' := is_limit_cone.fac,
  uniq' := is_limit_cone.uniq }

def limit_cone : limit_cone F :=
{ cone := cone F,
  is_limit := is_limit_cone F }

instance : has_products Cat.{u u} := λ I,
{ has_limit := λ F, ⟨⟨ limit_cone F ⟩⟩ }

end pi

lemma has_limits : has_limits.{u} Cat.{u u} :=
limits_from_equalizers_and_products

instance : has_pullbacks Cat.{u u} :=
@has_limits.has_limits_of_shape _ _ has_limits _ _

end Cat
end category_theory
