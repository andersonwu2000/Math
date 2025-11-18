import MATH.Category.Hom.Iso

namespace category
set_option trace.Meta.synthInstance true
set_option profiler true

universe u

abbrev Types : Category where
  obj := Type u
  hom X Y := X → Y
  id X := id
  comp f g := f ∘ g

attribute [simp] Function.comp_def

namespace Types

@[ext]
theorem ext
  (f g : X ⟶[Types] Y) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

@[simp, grind =]
theorem naturality_apply
  (α : F ⇒[C, Types] G) (f : X ⟶ Y) (a : F[X]) :
  (α·Y) (F[f] a) = G[f] ((α·X) a) :=
  congrFun (α.naturality f) a

abbrev Unit : Types.obj := PUnit
abbrev Point (a : X) : Unit ⟶ X := fun _ => a

end Types
namespace Types.Iso

@[simp, grind =]
theorem hom_inv_id_apply
  (x : X) (i : X ≅[Types] Y) :
  i.inv (i.hom x) = x :=
  congrFun i.inv_hom_id x

@[simp, grind =]
theorem inv_hom_id_apply
  (y : Y) (i : X ≅[Types] Y) :
  i.hom (i.inv y) = y :=
  congrFun i.hom_inv_id y

@[simp]
theorem eq_symm_apply
  (x : X) (y : Y) (i : X ≅[Types] Y) :
  x = i.inv y ↔ i.hom x = y := by grind

@[simp]
theorem symm_eq_apply
  (x : X) (y : Y) (i : X ≅[Types] Y) :
  i.inv y = x ↔ y = i.hom x := by grind

end Types.Iso
namespace Types.hom
variable (f : X ⟶[Types] Y)

theorem injective [p : f.IsMono] : Function.Injective f := by
  intro x1 x2 h
  have q : f ∘[Types] Types.Point x1 = f ∘[Types] Types.Point x2 := by
    simp [h]
  exact congrFun (p.right_uni q) PUnit.unit

theorem injective.IsMono
  (p : Function.Injective f) : f.IsMono where
  right_uni := by
    intro Z g h q
    funext z
    exact p (congrFun q z)

theorem surjective [p : f.IsEpi] : Function.Surjective f := by
    refine Function.surjective_of_right_cancellable_Prop
      fun g₁ g₂ h => ?_
    let up {Z} (g : Z → Prop) : Z ⟶[Types] ULift Prop :=
      fun z => .up (g z)
    have q : up g₁ = up g₂ → g₁ = g₂ := by
      intro h
      funext x
      let q := (congrFun h x)
      simp [up] at q
      simp_all
    apply q
    apply p.left_uni
    change ULift.up ∘ g₁ ∘ f = ULift.up ∘ g₂ ∘ f
    rw [h]

theorem surjective.IsEpi
  (p : Function.Surjective f) : f.IsEpi where
  left_uni := by
    intro Z g h q
    funext z
    let ⟨a, p⟩ := p z
    repeat rw [←p]
    exact (congrFun q a)

theorem bijective [f.IsIso] : Function.Bijective f :=
  ⟨injective f, surjective f⟩

noncomputable
instance bijective.IsIso
  (p : Function.Bijective f) : f.IsIso where
  inv y := Classical.choose (p.2 y)
  inv_hom_id := by
    funext x
    exact p.1 (Classical.choose_spec (p.2 (f x)))
  hom_inv_id := by
    funext y
    exact Classical.choose_spec (p.2 y)

noncomputable
instance Epi_Mono_toIso [p : f.IsEpi] [q : f.IsMono] : f.IsIso :=
  bijective.IsIso f ⟨injective f, surjective f⟩

end Types.hom
namespace Functor
variable (F G : C ⥤ Types)


@[simp, grind =]
theorem map_inv_map_hom_apply (i : X ≅[C] Y) (a : F[X]) :
  F[i.inv] (F[i.hom] a) = a := congrFun F[i].inv_hom_id a

@[simp, grind =]
theorem map_hom_map_inv_apply (i : X ≅[C] Y) (a : F[Y]) :
  F[i.hom] (F[i.inv] a) = a := congrFun F[i].hom_inv_id a

end Functor

namespace NatIso
variable (F G : C ⥤ Types) (α : F ≅ G)

@[simp, grind =]
theorem hom_inv_id_app_apply :
  (α.inv·X) ((α.hom·X) x) = x :=
  congr_fun (α.inv_hom_id_app X) x

@[simp, grind =]
theorem inv_hom_id_app_apply :
  α.hom.app X (α.inv.app X x) = x :=
  congr_fun (α.hom_inv_id_app X) x

@[simp]
theorem eq_symm_apply {x : F[X]} :
  x = (α.inv·X) y ↔ (α.hom·X) x = y := by grind

@[simp]
theorem symm_eq_apply {x : F[X]} :
  x = (α.inv·X) y ↔ y = (α.hom·X) x := by grind

end NatIso
