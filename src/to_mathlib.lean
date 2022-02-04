import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# Material I have made that is worth exporting to mathlib

This file contains some lemmas for how `heq` (==) interacts with functors.

This file contains a construction of equalizers of two functors,
as a subtype of the source category.
This construction will be used in a later file,
by making this category an object in Cat.{v u}.
The last result - factoring maps into the equalizer -
is a useful lemma when working with limits.

I also construct punit as a category, NOT using `discrete`,
as offered by the libarary.
This is because I need `punit` to be in `Cat.{v u}`,
but `discrete` only constructs small categories.
-/



universes u v u0 v0

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
by { rw [F.map_comp, G.map_comp], congr' }
-- thanks to Xu Junyan who came up with the proof
-- I extracted this to two lemmas

lemma map_comp_heq' (hobj : ∀ x : C, F.obj x = G.obj x)
  (hmap : ∀ {x y} (f : x ⟶ y), F.map f == G.map f) :
  F.map (f ≫ g) == G.map (f ≫ g) :=
by rw functor.hext hobj (λ _ _, hmap)

lemma precomp_map_heq (H : E ⥤ C)
  (hmap : ∀ {x y} (f : x ⟶ y), F.map f == G.map f) {x y : E} (f : x ⟶ y) :
  (H ⋙ F).map f == (H ⋙ G).map f := hmap _

lemma comp_map_heq (H : D ⥤ E) (hx : F.obj x = G.obj x) (hy : F.obj y = G.obj y)
  (hmap : F.map f == G.map f) :
  (F ⋙ H).map f == (G ⋙ H).map f :=
by { dsimp, congr' }
-- inspired by the proof above, which was not my own

lemma comp_map_heq' (H : D ⥤ E) (hobj : ∀ x : C, F.obj x = G.obj x)
  (hmap : ∀ {x y} (f : x ⟶ y), F.map f == G.map f) :
  (F ⋙ H).map f == (G ⋙ H).map f :=
by rw functor.hext hobj (λ _ _, hmap)

lemma hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f == G.map f :=
by subst h; simp

end functor

end heq

section product

/-- The natural transformation between two functors out of discrete I,
specified by its components. -/
def {w} map_pi {I : Type w} {C : Type u} [category.{v} C] {F G : discrete I ⥤ C}
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

/-- For our convenience we can write EQ for the equalizer -/
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
functor.precomp_map_heq _ (λ _ _, ι_map) _

/-- Any map into the equalizer is equal to the induced map from the
universal property using the obvious composition-/
lemma self_eq_lift (H : E ⥤ EQ F G) :
  H = lift (H ⋙ ι) (self_eq_lift_obj H) (λ _ _, self_eq_lift_map H) :=
functor.hext (λ x, subtype.ext rfl)
  (λ x y f, by { dsimp only [lift, ι], apply heq_of_eq, apply subtype.ext, refl })

end equalizer
end equalizer

end category_theory
