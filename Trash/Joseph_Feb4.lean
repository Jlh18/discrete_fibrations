import category_theory.category.Cat
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.pi.basic
import category_theory.punit
import to_mathlib

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

/-
## Declaration

Some of the work in this file is thanks to others.
Where it is *not* stated, it is my own work.
-/

universes u v

open category_theory
open category_theory.limits
open category_theory.prod

namespace category_theory
namespace Cat

/- DEPENDENT PRODUCTS -/

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


/- EQUALIZERS -/

/-- The equalizer category of two functors (as an object in Cat) -/
def equalizer {C D : Cat.{v u}} (F G : C ⟶ D) : Cat.{v u} :=
{ α := { c : C // F.obj c = G.obj c } }

namespace equalizer

variables {C D : Cat.{v u}} (F G : C ⟶ D)

/-- The map embedding the equalizer of two functors into the source category -/
def fork_ι : equalizer F G ⟶ C := equalizer.ι

lemma fork_condition : fork_ι F G ≫ F = fork_ι F G ≫ G :=
functor.hext (λ ⟨ _ , h ⟩, h ) (λ _ _ f , f.2)

/-- The equalizer of two functors as a cone over the parallel pair diagram (called a fork) -/
def fork : fork F G := fork.of_ι (fork_ι F G) (fork_condition _ _)

variables {F G}

namespace is_limit_fork

/-- Existence part of the universal property of equalizers -/
def lift (c : category_theory.limits.fork F G) : c.X ⟶ (fork F G).X :=
equalizer.lift c.ι
  (λ x, by { have h := c.condition, dsimp only [(≫)] at h, rw h })
  (λ _ _ f, by { convert functor.hcongr_hom c.condition f })

lemma fac (c : category_theory.limits.fork F G) :
  is_limit_fork.lift c ≫ (fork F G).ι = c.ι :=
functor.hext (λ _, rfl) (λ _ _ _, heq_of_eq rfl)
-- golf inspired by Xu Junyan's idea for binary products
-- (from 7 lines using ext ← hext)

/-- Uniqueness part of the universal property of equalizers -/
lemma uniq (c : category_theory.limits.fork F G) (m : c.X ⟶ (fork F G).X)
  (h : ∀ (j : walking_parallel_pair), m ≫ (fork F G).π.app j = c.π.app j) :
  m = is_limit_fork.lift c :=
by{ rw equalizer.self_eq_lift m, congr, exact h walking_parallel_pair.zero }
-- golf inspired by Xu Junyan's idea for binary products
-- (from 15 lines using self_eq_lift)

end is_limit_fork

open is_limit_fork

/-- The equalizer of two functors (as a cone/fork) is a limit -/
def is_limit_fork : is_limit (fork F G) :=
fork.is_limit.mk (fork F G) lift fac uniq

/-- The equalizer of two functors (as a cone/fork) is a limit -/
def limit_cone_parallel_pair : limit_cone (parallel_pair F G) :=
{ cone := fork F G,
  is_limit := is_limit_fork }

instance has_limit_parallel_pair : has_limit (parallel_pair F G) :=
⟨⟨ limit_cone_parallel_pair ⟩⟩

end equalizer

instance has_equalizers : has_equalizers Cat.{v u} :=
has_equalizers_of_has_limit_parallel_pair _

/-- The category of small categories has all small limts -/
theorem has_limits : has_limits.{u} Cat.{u u} :=
limits_from_equalizers_and_products



/- BINARY PRODUCTS -/

-- The product of two categories is a category (category_theory.products.basic) -/
def prod (C D : Cat.{v u}) : Cat.{v u} :=
{ α := (C.α × D.α) }

namespace prod

/-- The product of two categories as a cone over the pair diagram -/
def cone (C D : Cat.{v u}) : cone (pair C D) :=
{ X := prod C D,
  π := map_pair (fst _ _) (snd _ _) }

variables {C D E : Cat.{v u}}

/-- Existence part of the universal property of products -/
def lift (f : E ⟶ C) (g : E ⟶ D) : (E ⟶ prod C D) :=
{ obj := λ z, ⟨ f.obj z , g.obj z ⟩,
  map := λ _ _ h, ⟨ f.map h , g.map h ⟩ }

lemma self_eq_lift (F : E ⟶ prod C D) : F = lift (F ≫ fst _ _) (F ≫ snd _ _) :=
functor.hext (λ x, prod.ext rfl rfl)
(λ x y f, by { dsimp [lift, (≫)], cases F.map f, refl })
-- not my work, due to Xu Junyan on Zulip.
-- A sensible lemma for refactoring a map into the limit
-- I imitate this strategy later on.

lemma lift_fst {F : E ⟶ C} (G : E ⟶ D) :
  lift F G ≫ fst _ _ = F :=
by { cases F, refl }

lemma lift_snd {F : E ⟶ C} (G : E ⟶ D) :
  lift F G ≫ snd _ _ = G :=
by { cases G, refl }

namespace is_limit_cone

/-- Existence part of the universal property of products -/
def lift (c : limits.cone (pair C D)) :
  c.X ⟶ (cone C D).X :=
lift (c.π.app walking_pair.left) (c.π.app walking_pair.right)

lemma fac (c : limits.cone (pair C D)) (j : walking_pair) :
  lift c ≫ (cone C D).π.app j = c.π.app j :=
walking_pair.cases_on j (lift_fst _) (lift_snd _)
-- this proof used to be 2 lines long, using functor.ext
-- thanks to Xu Junyan on Zulip who changed prod_map_fst and prod_map_snd for this golf

/-- Uniqueness part of the universal property of products -/
lemma uniq
  (c : limits.cone (pair C D)) (F : c.X ⟶ prod C D)
  (h : ∀ (j : discrete walking_pair), F ≫ (cone C D).π.app j = c.π.app j) :
  F = lift c :=
by { rw self_eq_lift F, congr; convert h _; refl }
-- this proof used to be 18 lines long, using functor.ext
-- thanks to Xu Junyan on Zulip who made self_eq_prod_map for this golf

end is_limit_cone

/-- The product of categories (as a cone over the pair diagram) is a 1-limit -/
def is_limit_cone :
  is_limit (cone C D) :=
{ lift := is_limit_cone.lift,
  fac' := is_limit_cone.fac,
  uniq' := is_limit_cone.uniq }

/-- The product of categories C × D forms 1-product in the category of categories -/
def limit_cone : limit_cone (pair C D) :=
{ cone := cone C D,
  is_limit := is_limit_cone }

/-- Any pair of categories can made into product, that is the limit of the diagram `pair` -/
instance has_limit_pair : has_limit (pair C D) :=
⟨⟨ limit_cone ⟩⟩

end prod

/-- The category of categories has binary products -/
instance : has_binary_products Cat.{v u} :=
has_binary_products_of_has_limit_pair _

def terminal : Cat.{v u} :=
{ α := punit,
  str := { hom := λ _ _, punit,
  -- this punit : Type v should to be thought of as `star ⟶ star`
  id := λ _, punit.star, -- there is only one map from `star → star`
  comp := λ _ _ _ _ _, punit.star } }
  -- the composition of this trivial map with itself is itself

namespace terminal

variables (C : Cat.{v u}) (F : C ⟶ terminal)

/-- Existence in the universal property of the terminal object -/
def lift : C ⟶ terminal :=
{ obj := λ _ , punit.star, -- Note punit.star : punit : Type u
  map := λ _ _ _, punit.star } -- Note punit.star : punit : Type v

/-- Uniqueness in the universal property of the terminal object -/
def uniq : F = lift C :=
functor.hext (λ _, punit.ext) (λ _ _ _, heq_of_eq punit.ext)

instance : unique (C ⟶ Cat.terminal) :=
{ default := lift C,
  uniq := uniq C }

end terminal

instance : has_terminal Cat.{v u} :=
begin refine has_terminal_of_unique terminal, end

/-- The category of categories has finite products -/
instance : has_finite_products Cat.{v u} :=
has_finite_products_of_has_binary_and_terminal

/-- The category of categories has all finite limits -/
theorem has_finite_limits : has_finite_limits Cat.{v u} :=
finite_limits_from_equalizers_and_finite_products

/-- The category of small categories has pullback -/
example : has_pullbacks Cat.{u u} :=
@limits.has_limits_of_shape_of_has_finite_limits _ _
  walking_cospan _ _ has_finite_limits

-- @has_limits.has_limits_of_shape _ _ has_limits _ _

end Cat

namespace Cat

-- def punit : Cat.{u u} := { α := discrete punit }

-- def discrete_punit_level : category.{u} (discrete punit.{u}) := by apply_instance

-- def whats_the_level : category.{u} Cat.punit.{u} := by apply_instance

-- def Cat : Cat.{(max v u) (max v u)+1} := { α := Cat.{v u} }

-- def over_punit : Cat.{u+1 u} := { α := over Cat.punit.{u} }

def type : Cat.{u+1 u+1} := { α := Type u, str := ulift_category_hom }

def under_punit : Cat.{u+1 u+1} :=
{ α := @under (Type u) _ punit,
  str := ulift_category_hom }

-- def {w} elements {C : Cat.{v u}} (F : C ⥤ Type w) : Cat.{v (max u w)} :=
-- { α := functor.elements F }

namespace under_punit

def forget' : @under (Type u) _ punit ⥤ Type u := under.forget punit

def forget : under_punit ⟶ type := ulift_functor_hom (forget')

end under_punit


end Cat

namespace elements

open Cat

variables {C : Cat.{u+1 u+1}} (F : C ⥤ Type u)

def elements : Cat.{u+1 u+1} :=
{ α := functor.elements F }

def π : elements F ⟶ C := category_of_elements.π F

def fiber : C ⟶ type :=
{ obj := F.obj,
  map := λ _ _ f, ulift.up (F.map f) }

def elements_to_over_punit_functor : functor.elements F ⥤ @under (Type u) _ punit :=
{ obj := λ ⟨c, x⟩, under.mk (λ _, x),
  map := λ x y f, under.hom_mk (by {cases x, cases y,
    erw [under.mk_right], erw [under.mk_right], exact F.map f})
    (by {cases y, cases x, cases f with _ hf, dsimp at *, cases hf, refl}) }

/-
          π2
  (c , x) ↦ F c
  Σ F ---> under_punit
 π |         |  forget
   V         V
   C ---> Type u
      F
-/

#check functor.elements




end elements

end category_theory

-- instance has_pullbacks : has_pullbacks Cat.{v u} :=
-- by apply_instance
