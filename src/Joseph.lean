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

/-
## Declaration

Some of the work in this file is thanks to others.
Where it is *not* stated, it is my own work.
-/

universes u v w

open category_theory
open category_theory.limits
open category_theory.prod

namespace category_theory

section heq

variables
  {C D E : Type u} [category.{v} C] [category.{v} D] [category.{v} E]
  {F G : C ⥤ D} {x y z : C} (f : x ⟶ y) {g : y ⟶ z}

lemma heq_iff_eq_conj_eq_to_hom
  (h₁ : F.obj x = G.obj x) (h₂ : F.obj y = G.obj y) :
  F.map f = eq_to_hom h₁ ≫ G.map f ≫ eq_to_hom h₂.symm ↔ F.map f == G.map f :=
by { generalize : F.map f = Ff, generalize : G.map f = Gf, clear f,
  generalize_hyp : F.obj x = F₁ at h₁ Ff ⊢, generalize_hyp : F.obj y = F₂ at h₂ Ff ⊢,
  cases h₁, cases h₂, simp }
-- entirely not my work, due to Xu Junyan

namespace functor

variable {f}

lemma map_comp_heq (hx : F.obj x = G.obj x) (hy : F.obj y = G.obj y) (hz : F.obj z = G.obj z)
  (hf : F.map f == G.map f) (hg : F.map g == G.map g) :
  F.map (f ≫ g) == G.map (f ≫ g) :=
begin
  rw [F.map_comp, G.map_comp],
  -- cannot case directly on hf, since types of its source/target are not
  -- definitionally equal.
  -- To make them definitionally equal, must case on x.2 y.2 z.2
  -- In order to case on x.2 and z.2 must generalize these
  -- But f depends on x, and hf depends on f, so must generalize these variables
  -- in reverse order.
  generalize_hyp : F.map f = Ff at ⊢ hf, generalize_hyp : G.map f = Gf at ⊢ hf,
  generalize_hyp : F.map g = Fg at ⊢ hg, generalize_hyp : G.map g = Gg at ⊢ hg,
  generalize_hyp : F.obj x = Fx at ⊢ Ff Gf hx,
  generalize_hyp : F.obj y = Fy at ⊢ Fg Ff hy,
  generalize_hyp : F.obj z = Fz at ⊢ Fg Gg hz,
  -- now able to clear the variables, substitute eqs and heqs
  subst hx, subst hy, subst hz, cases hf, cases hg,
  exact heq_of_eq rfl,
end
-- thanks to Xu Junyan who came up with the proof
-- I extracted this to two lemmas

lemma map_comp_heq' (hobj : ∀ x : C, F.obj x = G.obj x)
  (hmap : ∀ {x y} (f : x ⟶ y), F.map f == G.map f) :
  F.map (f ≫ g) == G.map (f ≫ g) :=
  map_comp_heq (hobj _) (hobj _) (hobj _) (hmap _) (hmap _)

lemma precomp_map_heq (H : E ⥤ C) (hobj : ∀ x : C, F.obj x = G.obj x)
  (hmap : ∀ {x y} (f : x ⟶ y), F.map f == G.map f) {x y : E} (f : x ⟶ y) :
  (H ⋙ F).map f == (H ⋙ G).map f := hmap _

lemma comp_map_heq (H : D ⥤ E) (hobj : ∀ x : C, F.obj x = G.obj x)
  (hmap : ∀ {x y} (f : x ⟶ y), F.map f == G.map f) :
  (F ⋙ H).map f == (G ⋙ H).map f :=
begin
  dsimp,
  obtain ⟨ hx, hy, hf ⟩  := ⟨ hobj x, hobj y, hmap f ⟩,
  generalize_hyp : F.map f = Ff at ⊢ hf,
  generalize_hyp : G.map f = Gf at ⊢ hf,
  generalize_hyp : F.obj x = Fx at ⊢ Ff hx,
  generalize_hyp : G.obj x = Gx at ⊢ Gf hx,
  generalize_hyp : F.obj y = Fy at ⊢ Ff hy,
  generalize_hyp : G.obj y = Gy at ⊢ Gf hy,
  subst hx, subst hy, cases hf,
  exact heq_of_eq rfl,
end
-- similar idea to map_comp_heq

lemma hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f == G.map f :=
by subst h; simp

end functor

end heq

section product

/-- The natural transformation between two functors out of discrete I,
specified by its components. -/
def map_pi {I : Type w} {C : Type u} [category.{v} C] {F G : discrete I ⥤ C}
  (on_obj : Π i : I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := on_obj }

end product

section equalizer

variables
  {C D E : Type u} [category.{v} C] [category.{v} D] [category.{v} E]
  {F G : C ⥤ D} {x y z : C} {f : x ⟶ y} {g : y ⟶ z}

/-- The equalizer category of two functors (as a subcategory of the source category C) -/
instance equalizer : category.{v} { c : C // F.obj c = G.obj c } :=
{ hom := λ x y,
    { f : x.1 ⟶ y.1 // F.map f == G.map f },
  id := λ x, ⟨ 𝟙 x , by { erw [F.map_id _, G.map_id, x.2], } ⟩,
  comp := λ x y z f g, ⟨ f.1 ≫ g.1 , functor.map_comp_heq x.2 y.2 z.2 f.2 g.2 ⟩ }
-- this proof used to be 14 lines long,
-- extracted map_comp_heq; thanks to Xu Junyan helping to use heq (==) ← eq (=)

abbreviation EQ (F G : C ⥤ D) := { c : C // F.obj c = G.obj c }

namespace equalizer

/-- Existence part of the universal property of equalizers -/
def lift (H : E ⥤ C) (hobj : ∀ e : E, (H ⋙ F).obj e = (H ⋙ G).obj e)
  (hmap : ∀ {x y : E} (f : x ⟶ y), F.map (H.map f) == G.map (H.map f)) :
  E ⥤ { c : C // F.obj c = G.obj c } :=
{ obj := λ x, ⟨ H.obj x , hobj x ⟩,
  map := λ _ _ f, ⟨ H.map f , hmap f ⟩ }

/-- The map embedding the equalizer of two functors into the source category -/
def ι : EQ F G ⥤ C :=
{ obj := subtype.val,
  map := λ _ _, subtype.val }

lemma ι_obj (x : EQ F G) : (ι ⋙ F).obj x = (ι ⋙ G).obj x := x.2

lemma ι_map {x y : EQ F G} (f : x ⟶ y) : (ι ⋙ F).map f == (ι ⋙ G).map f := f.2

lemma self_eq_lift_obj (H : E ⥤ EQ F G) (x : E) :
  (H ⋙ ι ⋙ F).obj x = (H ⋙ ι ⋙ G).obj x := by { erw ι_obj, refl }

lemma self_eq_lift_map (H : E ⥤ EQ F G) {x y : E} (f : x ⟶ y) :
  (H ⋙ ι ⋙ F).map f == (H ⋙ ι ⋙ G).map f :=
functor.precomp_map_heq _ ι_obj (λ _ _, ι_map) _

/-- Any map into the equalizer is equal to the induced map from the
universal property using the obvious composition-/
lemma self_eq_lift (H : E ⥤ EQ F G) :
  H = lift (H ⋙ ι) (self_eq_lift_obj H) (λ _ _, self_eq_lift_map H) :=
functor.hext (λ x, subtype.ext rfl)
  (λ x y f, by { dsimp only [lift, ι], apply heq_of_eq, apply subtype.ext, refl })

end equalizer
end equalizer

namespace Cat

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

instance has_equalizers : has_equalizers Cat.{v u} :=
has_equalizers_of_has_limit_parallel_pair _

end equalizer

/-- The category of small categories has all small limts -/
lemma has_limits : has_limits.{u} Cat.{u u} :=
limits_from_equalizers_and_products

/-- The category of small categories has pullback -/
instance : has_pullbacks Cat.{u u} :=
@has_limits.has_limits_of_shape _ _ has_limits _ _

end Cat
end category_theory

-- instance has_pullbacks : has_pullbacks Cat.{v u} :=
-- by apply_instance
