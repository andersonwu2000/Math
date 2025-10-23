import MATH.category.Iso

namespace category
-- set_option trace.Meta.synthInstance true
-- set_option profiler true

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
  (f g : X ⟶[Types] Y) (h : ∀x:X, f x = g x) : f = g := by
  funext x
  exact h x

@[simp, grind =]
theorem naturality
  (α : F ⇒[C, Types] G) (f : X ⟶ Y) (a : F[X]) :
  (α|Y) (F[f] a) = G[f] ((α|X) a) :=
  congrFun (α.naturality f) a

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

variable (F G : C ⥤ Types)

@[simp, grind =]
theorem map_inv_map_hom_apply
  (i : X ≅[C] Y) (a : F[X]) :
  F[i.inv] (F[i.hom] a) = a :=
  congrFun (F.mapIso i).inv_hom_id a

@[simp, grind =]
theorem map_hom_map_inv_apply
  (i : X ≅[C] Y) (a : F[Y]) :
  F[i.hom] (F[i.inv] a) = a :=
  congrFun (F.mapIso i).hom_inv_id a

@[simp, grind =]
theorem hom_inv_id_app_apply (α : F ≅ G) (X) (x) :
  (α.inv|X) ((α.hom|X) x) = x :=
  congr_fun (α.inv_hom_id_app X) x

@[simp, grind =]
theorem inv_hom_id_app_apply (α : F ≅ G) (X) (x) : α.hom.app X (α.inv.app X x) = x :=
  congr_fun (α.hom_inv_id_app X) x
