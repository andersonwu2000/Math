import MATH.Category.Basic.Functor

/-
`Mono Epi`
  op comp cancel
`Category.hom`
  IsMono IsEpi
  Mono Epi : IsMono/Epi → Mono/Epi
  hom_eq
  right_uni left_uni

`Split Mono/Epi`
  op comp
  Mono Epi
`Category.hom`
  IsSplitMono IsSplitEpi
  SplitMono SplitEpi : Is... to ...
  hom_eq
  inv_hom_id hom_inv_id
-/

-- set_option trace.Meta.synthInstance true
-- set_option profiler true

namespace category
variable {C : Category}

structure Mono (X Y : C.obj) where
  hom : X ⟶ Y
  right_uni : hom ∘ g = hom ∘ h → g = h :=
    by simp

attribute [grind →] Mono.right_uni
attribute [coe] Mono.hom
notation X "↣[" C "]" Y => @Mono C X Y
notation X "↣" Y => Mono X Y
instance : Coe (X ↣ Y) (X ⟶ Y) where
  coe f := f.hom

structure Epi (X Y : C.obj) where
  hom : X ⟶ Y
  left_uni : g ∘ hom = h ∘ hom → g = h :=
    by simp

attribute [grind →] Epi.left_uni
attribute [coe] Epi.hom
notation X "↠[" C "]" Y => @Epi C X Y
notation X "↠" Y => Epi X Y
instance : Coe (X ↠ Y) (X ⟶ Y) where
  coe f := f.hom

abbrev Mono.op
  (f : X ↣[C] Y) : Y ↠[Cᵒᵖ] X where
  hom := f.hom
  left_uni := f.right_uni

abbrev Epi.op
  (f : X ↠[C] Y) : Y ↣[Cᵒᵖ] X where
  hom := f.hom
  right_uni := f.left_uni

abbrev Mono.comp
  (f : X ↣ Y) (g : Y ↣ Z) : X ↣ Z where
  hom := g.hom ∘ f.hom
  right_uni := by
    intros
    apply f.right_uni
    apply g.right_uni
    simp_all

abbrev Epi.comp
  (f : X ↠ Y) (g : Y ↠ Z) : X ↠ Z :=
  (Mono.comp g.op f.op).op

@[simp, grind =]
lemma Mono.cancel (g : X ↣[C] Y) :
  (g : X ⟶ Y) ∘ f = g ∘ h ↔ f = h :=
  ⟨g.right_uni, Whisker.left_cancel (g : X ⟶ Y)⟩

@[simp, grind =]
lemma Epi.cancel (f : X ↠[C] Y) :
  g ∘ (f : X ⟶ Y) = h ∘ f ↔ g = h :=
  ⟨f.left_uni, Whisker.right_cancel (f : X ⟶ Y)⟩

section Category.hom
variable (f : X ⟶ Y) (g : Y ⟶ Z)

abbrev Mono.mono_of_mono (h : X ↣ Z) (p : g ∘ f = h) : X ↣ Y where
  hom := f
  right_uni _ := by
    apply h.right_uni
    simp [←p]
    congr

abbrev Epi.epi_of_epi (h : X ↠ Z) (p : g ∘ f = h) : Y ↠ Z where
  hom := g
  left_uni _ := by
    apply h.left_uni
    simp [←p, ←Category.assoc]
    congr

end Category.hom


section Split

@[ext]
structure SplitMono (X Y : C.obj) where
  hom : X ⟶ Y
  left_inv : Y ⟶ X
  inv_hom_id : left_inv ∘ hom = 𝟙 X := by simp

attribute [grind =] SplitMono.inv_hom_id
attribute [coe] SplitMono.hom
instance : Coe (SplitMono X Y) (X ⟶ Y) where
  coe f := f.hom

@[ext]
structure SplitEpi (X Y : C.obj) where
  hom : X ⟶ Y
  right_inv : Y ⟶ X
  hom_inv_id : hom ∘ right_inv = 𝟙 Y := by simp

attribute [grind =] SplitEpi.hom_inv_id
attribute [coe] SplitEpi.hom
instance : Coe (SplitEpi X Y) (X ⟶ Y) where
  coe f := f.hom

abbrev SplitMono.op
  (f : @SplitMono C X Y) : SplitEpi (C := Cᵒᵖ) Y X where
  hom := f.hom
  right_inv := f.left_inv
  hom_inv_id := f.inv_hom_id

abbrev SplitEpi.op
  (f : @SplitEpi C X Y) : SplitMono (C := Cᵒᵖ) Y X where
  hom := f.hom
  left_inv := f.right_inv
  inv_hom_id := f.hom_inv_id

abbrev SplitMono.comp
  (f : SplitMono X Y) (g : SplitMono Y Z) : SplitMono X Z where
  hom := g.hom ∘ f.hom
  left_inv := f.left_inv ∘ g.left_inv
  inv_hom_id := by
    have : g.left_inv ∘ (g.hom ∘ f.hom) = f.hom := by
      rw [←Category.assoc, g.inv_hom_id]
      simp
    simp_all
    rw [f.inv_hom_id]

abbrev SplitEpi.comp
  (f : SplitEpi X Y) (g : SplitEpi Y Z) : SplitEpi X Z :=
  (SplitMono.comp g.op f.op).op

abbrev SplitMono.map (F : C ⥤ D) (f : SplitMono X Y) :
  SplitMono F[X] F[Y] where
  hom := F[f]
  left_inv := F.map f.left_inv
  inv_hom_id := by
    rw [←F.map_comp, f.inv_hom_id]
    simp_all

abbrev SplitEpi.map (F : C ⥤ D) (f : SplitEpi X Y) :
  SplitEpi F[X] F[Y] := (SplitMono.map F.op f.op).op

abbrev SplitMono.Mono (f : SplitMono X Y) : X ↣ Y where
  hom := f.hom
  right_uni {_ g h} _ := by
    rw [←Category.comp_id _ g, ←f.inv_hom_id]
    rw [←Category.comp_id _ h, ←f.inv_hom_id]
    simp_all

abbrev SplitEpi.Epi (f : SplitEpi X Y) : X ↠ Y :=
  (SplitMono.Mono f.op).op

end Split
