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
We construct dependent products, fiber products/pullbacks,
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

/-- The natural transformation between two functors out of discrete I,
specified by its components. -/
def map_pi {I : Type w} {C : Type u} [category.{v} C] {F G : discrete I ⥤ C}
  (on_obj : Π i : I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := on_obj }

namespace Cat

section equalizer

variables {C D E : Cat.{v u}} (F G : C ⟶ D)

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

/-- Existence part of the universal property of equalizers -/
def lift {H : E ⟶ C} (hobj : ∀ e : E, (H ≫ F).obj e = (H ≫ G).obj e)
  (hmap : ∀ {x y : E} (f : x ⟶ y), F.map (H.map f)
    = eq_to_hom (hobj _) ≫ G.map (H.map f) ≫ eq_to_hom (hobj _).symm) :
  E ⟶ equalizer F G :=
{
  obj := λ x, ⟨ H.obj x , hobj x ⟩,
  map := λ _ _ f, ⟨ H.map f , hmap f ⟩,
}

-- lemma self_eq_lift {H : E ⟶ equalizer F G} :
--   H = @lift _ _ _ (H ≫ fork_ι _ _) (λ e, _) _ := sorry

-- lemma self_eq_lift (c : category_theory.limits.fork F G) :
--   c.π = lift c :=
-- functor.hext (λ x, prod.ext rfl rfl)
-- (λ x y f, heq_of_eq (prod.ext rfl rfl))

namespace is_limit_fork

/-- Existence part of the universal property of equalizers -/
def lift (c : category_theory.limits.fork F G) : c.X ⟶ (fork F G).X :=
lift ( λ e, congr_arg (λ F', functor.obj F' e) c.condition )
  ( λ _ _ f, by convert functor.congr_hom c.condition f )

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
fork.is_limit.mk (fork F G) is_limit_fork.lift fac uniq

/-- The equalizer of two functors (as a cone/fork) is a limit -/
def limit_cone_parallel_pair : limit_cone (parallel_pair F G) :=
{
  cone := fork F G,
  is_limit := is_limit_fork
}

/-- The equalizer of two functors -/
instance has_limit_parallel_pair : has_limit (parallel_pair F G) :=
⟨⟨ limit_cone_parallel_pair ⟩⟩

/-- The category of categories has equalizers -/
instance has_equalizers : has_equalizers Cat.{v u} :=
has_equalizers_of_has_limit_parallel_pair _

end equalizer

/-- The dependent product of categories, as an object of Cat.{u u} (note this is small) -/
def pi {I : Type u} (F : discrete I ⥤ Cat.{u u}) : Cat.{u u} :=
{ α := Π i : I, F.obj i }

namespace pi

variables {C : Cat.{u u}} {I : Type u} {F : discrete I ⥤ Cat.{u u}}

/-- Existence in the universal property of products -/
def lift (legs : Π i : I, C ⟶ F.obj i) : C ⟶ pi F :=
{ obj := λ x i, (legs i).obj x,
  map := λ _ _ f i, (legs i).map f }

/-- Any map into the product is equal to the induced map from the
universal property applied to the obvious composition -/
lemma self_eq_lift (G : C ⟶ pi F) : G = lift (λ i, G ≫ pi.eval _ _) :=
by {cases G, refl}
-- inspired by golf due to Xu Junyan for the binary product case

variable (F)

/-- The dependent product of categories, as a cone -/
def cone : cone F :=
{ X := pi F ,
  π := map_pi $ pi.eval _ }

namespace is_limit_cone

variable {F}

/-- Existence in the universal property of products (for cones) -/
def lift (c : limits.cone F) : c.X ⟶ (cone F).X :=
lift (λ i, c.π.app i)

/-- The induced map from the universal property commutes with the diagram -/
lemma fac (c : limits.cone F) (i : discrete I) :
  lift c ≫ (cone F).π.app i = c.π.app i :=
by { rw self_eq_lift (lift c), apply functor.hext; { intros, refl } }
-- thanks to Xu Junyan's golf for the binary product case (by using hext ← ext)

/-- Uniqueness in the universal property of products -/
lemma uniq (c : limits.cone F) (m : c.X ⟶ (cone F).X)
  (h : ∀ (j : discrete I), m ≫ (cone F).π.app j = c.π.app j) :
  m = is_limit_cone.lift c :=
by { unfold lift, simp_rw ← h, apply functor.hext; { intros, refl } }
-- thanks to Xu Junyan's golf for the binary product case (by using hext ← ext)

end is_limit_cone

/-- The product of categories is a limit -/
def is_limit_cone : is_limit (cone F) :=
{ lift := is_limit_cone.lift,
  fac' := is_limit_cone.fac,
  uniq' := is_limit_cone.uniq }

/-- The product of categories is a limit cone -/
def limit_cone : limit_cone F :=
{ cone := cone F,
  is_limit := is_limit_cone F }

/-- The category of small categories has products -/
instance : has_products Cat.{u u} := λ I,
{ has_limit := λ F, ⟨⟨ limit_cone F ⟩⟩ }

end pi

/-- The category of small categories has all small limts -/
lemma has_limits : has_limits.{u} Cat.{u u} :=
limits_from_equalizers_and_products

/-- The category of small categories has pullback -/
instance : has_pullbacks Cat.{u u} :=
@has_limits.has_limits_of_shape _ _ has_limits _ _

end Cat
end category_theory
