import MATH.Category.Yoneda
import MATH.Category.Morphism.PreserveReflect

/-!
# Functor/Hom.lean

Hom functor 在 isomorphism / natural isomorphism 下的保持與反射。

## 定理
### `Hom`
- `.preserve_iso_left` — `X ≅ Y → Hom[X, –] ≅ Hom[Y, –]`
- `.preserve_iso_right` — `X ≅ Y → Hom[–, X] ≅ Hom[–, Y]`
- `.reflect_iso_left` — `Hom[X, –] ≅ Hom[Y, –] → X ≅ Y`
- `.reflect_iso_right` — `Hom[–, X] ≅ Hom[–, Y] → X ≅ Y`
- `.preserve_natiso_left` / `.preserve_natiso_right` — nat iso 版本
- `.reflect_natiso_left` / `.reflect_natiso_right` — nat iso 版本
-/

namespace CategoryTheory


variable {C : Category} {X Y : C.obj}

/-- `X ≅ Y → Hom[X, –] ≅ Hom[Y, –]` -/
def Hom.preserve_iso_left (iso : X ≅ Y) : Hom[X, –] ≅ Hom[Y, –] :=
  Preserve.Iso CoYoneda iso.op

/-- `X ≅ Y → Hom[–, X] ≅ Hom[–, Y]` -/
def Hom.preserve_iso_right (iso : X ≅ Y) : Hom[–, X] ≅ Hom[–, Y] :=
  Preserve.Iso Yoneda iso

/-- `Hom[X, –] ≅ Hom[Y, –] → X ≅ Y`（Yoneda reflection） -/
noncomputable
def Hom.reflect_iso_left (iso : Hom[X, –] ≅ Hom[Y, –]) : X ≅ Y :=
  (Reflect.Iso CoYoneda iso).op

/-- `Hom[–, X] ≅ Hom[–, Y] → X ≅ Y` -/
noncomputable
def Hom.reflect_iso_right (iso : Hom[–, X] ≅ Hom[–, Y]) : X ≅ Y :=
  Reflect.Iso Yoneda iso


variable {F G : C ⥤ D}

/-- `F ≅ G → Hom[Fᵒᵖ–, –] ≅ Hom[Gᵒᵖ–, –]` -/
def Hom.preserve_natiso_left (iso : F ≅ G) : Hom[Fᵒᵖ–, –] ≅ Hom[Gᵒᵖ–, –] where
  hom := {app := fun (X, Y) f => f ○ iso⁻¹·X, naturality := by simp}
  inv := {app := fun (X, Y) f => f ○ iso·X, naturality := by simp}

/-- `F ≅ G → Hom[–, F–] ≅ Hom[–, G–]` -/
def Hom.preserve_natiso_right (iso : F ≅ G) : Hom[–, F–] ≅ Hom[–, G–] where
  hom := {app := fun (X, Y) f => iso·Y ○ f, naturality := by simp}
  inv := {app := fun (X, Y) f => iso⁻¹·Y ○ f, naturality := by simp}
  inv_hom_id := by ext X f; dsimp; grind
  hom_inv_id := by ext X f; dsimp; grind


private lemma right_nat
    (iso : Hom[–, F–] ≅ Hom[–, G–]) (f : X ⟶[C] Y) :
    iso·(F[Y].op, Y) (𝟙) ○ F[f] = G[f] ○ iso·(F[X].op, X) (𝟙) := by
  have p := congrFun (iso.hom.naturality ((𝟙).Prod f)) (𝟙)
  have q := congrFun (iso.hom.naturality ((F[f]).Prod (𝟙))) (𝟙)
  simp_all

private lemma left_nat
    (iso : Hom[Fᵒᵖ–, –] ≅ Hom[Gᵒᵖ–, –]) (f : X ⟶[C] Y) :
    iso·(Y, F[Y]) (𝟙) ○ G[f] = F[f] ○ iso·(X, F[X]) (𝟙) := by
  have p := congrFun (iso.hom.naturality (f.Prod (𝟙))) (𝟙)
  have q := congrFun (iso.hom.naturality ((𝟙).Prod F[f])) (𝟙)
  simp_all


/-- `Hom[Fᵒᵖ–, –] ≅ Hom[Gᵒᵖ–, –] → F ≅ G` -/
def Hom.reflect_natiso_left (iso : Hom[Fᵒᵖ–, –] ≅ Hom[Gᵒᵖ–, –]) : F ≅ G where
  hom := {app X := iso⁻¹·(X, G[X]) (𝟙), naturality := left_nat iso.symm }
  inv := {app X := iso·(X, F[X]) (𝟙),   naturality := left_nat iso }
  inv_hom_id := by
    ext X
    simpa using (congrFun (iso.inv.naturality ((𝟙).Prod (iso·(X, F[X]) (𝟙F[X])))) (𝟙)).symm
  hom_inv_id := by
    ext X
    simpa using (congrFun (iso.hom.naturality ((𝟙).Prod (iso⁻¹·(X, G[X]) (𝟙G[X])))) (𝟙)).symm

/-- `Hom[–, F–] ≅ Hom[–, G–] → F ≅ G` -/
def Hom.reflect_natiso_right (iso : Hom[–, F–] ≅ Hom[–, G–]) : F ≅ G where
  hom := {app X := iso·(F[X].op, X) (𝟙),   naturality := right_nat iso }
  inv := {app X := iso⁻¹·(G[X].op, X) (𝟙), naturality := right_nat iso.symm }
  inv_hom_id := by
    ext X
    simpa using (congrFun (iso.inv.naturality ((iso·(F[X].op, X) (𝟙F[X])).Prod (𝟙))) (𝟙)).symm
  hom_inv_id := by
    ext X
    simpa using (congrFun (iso.hom.naturality ((iso⁻¹·(G[X].op, X) (𝟙G[X])).Prod (𝟙))) (𝟙)).symm

end CategoryTheory
