
-- Category Theory: Functors, natural transformations, and adjunctions
import Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Functors preserve identity morphisms -/
theorem Functor.map_id (F : C ⥤ D) (X : C) : F.map (𝟙 X) = 𝟙 (F.obj X) :=
  F.map_id X

/-- Functors preserve composition -/
theorem Functor.map_comp (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g :=
  F.map_comp f g

/-- Composition of functors is associative -/
theorem Functor.assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ Type*) :
    (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) := by
  rfl

/-- Natural transformation between functors -/
structure NatTrans (F G : C ⥤ D) :=
(app : ∀ X : C, F.obj X ⟶ G.obj X)
(naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f)

/-- Adjunction between functors -/
theorem adjunction_unit_counit {F : C ⥤ D} {G : D ⥤ C} 
    (adj : F ⊣ G) :
    ∀ X : C, adj.unit.app X ≫ G.map (F.map (adj.counit.app (F.obj X))) = 𝟙 X := by
  intro X
  exact adj.left_triangle_components

end CategoryTheory
