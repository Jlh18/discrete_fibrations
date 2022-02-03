import to_mathlib
import category_theory.category.Cat
import category_theory.limits.shapes.equalizers
import category_theory.limits.constructions.equalizers

/-!
# The category of categories has equalizers

This file contains constructions of equalizers
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

universes u v

open category_theory
open category_theory.limits
open category_theory.equalizer

namespace category_theory
namespace Cat
namespace equalizer

variables {C D : Cat.{v u}} (F G : C ⟶ D)

/-- The equalizer category of two functors (as an object in Cat) -/
def equalizer : Cat.{v u} :=
{ α := { c : C // F.obj c = G.obj c } }

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

instance : has_equalizers Cat.{v u} :=
has_equalizers_of_has_limit_parallel_pair _

end Cat
end category_theory
