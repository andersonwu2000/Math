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

structure Mono (X Y) where
  hom : X ⟶[C] Y
  right_uni : hom ∘ f = hom ∘ g → f = g :=
    by simp

notation X "↣[" C "]" Y => @Mono C X Y
notation X "↣" Y => Mono X Y

structure Epi (X Y) where
  hom : X ⟶[C] Y
  left_uni : f ∘ hom = g ∘ hom → f = g :=
    by simp

notation X "↠[" C "]" Y => @Epi C X Y
notation X "↠" Y => Epi X Y


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
    simp_all only [Category.assoc]

abbrev Epi.comp
  (f : X ↠ Y) (g : Y ↠ Z) : X ↠ Z :=
  (Mono.comp g.op f.op).op


namespace Category.hom
variable (f : X ⟶ Y)

class IsMono where
  right_uni : f ∘ g = f ∘ h → g = h := by simp

class IsEpi where
  left_uni : g ∘ f = h ∘ f → g = h := by simp

def asMono [f.IsMono] : X ↣ Y where
  hom := f
  right_uni := IsMono.right_uni

def asEpi [f.IsEpi] : X ↠ Y where
  hom := f
  left_uni := IsEpi.left_uni

end Category.hom

instance Mono.IsMono (f : X ↣ Y) : f.hom.IsMono where
  right_uni := f.right_uni

instance Epi.IsEpi (f : X ↠ Y) : f.hom.IsEpi where
  left_uni := f.left_uni

section MonoEpi
variable (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp, grind =]
lemma IsMono.hom_eq [f.IsMono] :
  f.asMono.hom = f := rfl

@[simp, grind =]
lemma IsEpi.hom_eq [f.IsEpi] :
  f.asEpi.hom = f := rfl

lemma IsMono.right_uni [g.IsMono] :
  g ∘ f = g ∘ h → f = h := g.asMono.right_uni

lemma IsEpi.left_uni [f.IsEpi] :
  g ∘ f = h ∘ f → g = h := f.asEpi.left_uni

@[simp, grind =]
lemma IsMono.cancel [g.IsMono] :
  g ∘ f = g ∘ h ↔ f = h :=
  ⟨g.asMono.right_uni, Whisker.left_cancel g⟩

@[simp, grind =]
lemma IsEpi.cancel [f.IsEpi] :
  g ∘ f = h ∘ f ↔ g = h :=
  ⟨f.asEpi.left_uni, Whisker.right_cancel f⟩

@[simp]
theorem IsMono.mono_of_mono [(g ∘ f).IsMono] : f.IsMono where
  right_uni _ := by
    apply (g ∘ f).asMono.right_uni
    simp_all

@[simp]
theorem IsEpi.epi_of_epi [(g ∘ f).IsEpi] : g.IsEpi where
  left_uni _ := by
    apply (g ∘ f).asEpi.left_uni
    simp_all [←Category.assoc]

instance IsMono.comp [f.IsMono] [g.IsMono] : (g ∘ f).IsMono where
  right_uni _ := by
    apply f.asMono.right_uni
    apply g.asMono.right_uni
    simp_all

instance IsEpi.comp [f.IsEpi] [g.IsEpi] : (g ∘ f).IsEpi where
  left_uni _ := by
    apply g.asEpi.left_uni
    apply f.asEpi.left_uni
    simp_all

end MonoEpi


section Split

@[ext]
structure SplitMono (X Y) where
  hom : X ⟶[C] Y
  left_inv : Y ⟶[C] X
  inv_hom_id : left_inv ∘ hom = 𝟙 X := by simp

@[ext]
structure SplitEpi (X Y) where
  hom : X ⟶[C] Y
  right_inv : Y ⟶[C] X
  hom_inv_id : hom ∘ right_inv = 𝟙 Y := by simp

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
    simp_all only [Category.assoc]
    rw [f.inv_hom_id]

abbrev SplitEpi.comp
  (f : SplitEpi X Y) (g : SplitEpi Y Z) : SplitEpi X Z :=
  (SplitMono.comp g.op f.op).op


namespace Category.hom
variable (f : X ⟶ Y)

class IsSplitMono where
  left_inv : Y ⟶ X
  inv_hom_id : left_inv ∘ f = 𝟙 X := by simp

class IsSplitEpi where
  right_inv : Y ⟶ X
  hom_inv_id : f ∘ right_inv = 𝟙 Y := by simp

abbrev left_inv [f.IsSplitMono] := IsSplitMono.left_inv f
abbrev right_inv [f.IsSplitEpi] := IsSplitEpi.right_inv f

def asSplitMono [f.IsSplitMono] : SplitMono X Y where
  hom := f
  left_inv := left_inv f
  inv_hom_id := IsSplitMono.inv_hom_id

def asSplitEpi [f.IsSplitEpi] : SplitEpi X Y where
  hom := f
  right_inv := right_inv f
  hom_inv_id := IsSplitEpi.hom_inv_id

end Category.hom

instance SplitMono.IsSplitMono (f : SplitMono X Y) :
  f.hom.IsSplitMono where
  left_inv := f.left_inv
  inv_hom_id := f.inv_hom_id

instance SplitEpi.IsSplitEpi (f : SplitEpi X Y) :
  f.hom.IsSplitEpi where
  right_inv := f.right_inv
  hom_inv_id := f.hom_inv_id

variable {X Y Z : C.obj} (f : X ⟶[C] Y) (g : Y ⟶ Z)

@[simp, grind =]
lemma IsSplitMono.hom_eq [f.IsSplitMono] :
  f.asSplitMono.hom = f := rfl

@[simp, grind =]
lemma IsSplitEpi.hom_eq [f.IsSplitEpi] :
  f.asSplitEpi.hom = f := rfl

@[simp, grind =]
lemma IsSplitMono.left_inv_eq [f.IsSplitMono] :
  f.asSplitMono.left_inv = f.left_inv := rfl

@[simp, grind =]
lemma IsSplitEpi.right_inv_eq [f.IsSplitEpi] :
  f.asSplitEpi.right_inv = f.right_inv := rfl

lemma IsSplitMono.inv_hom_id [g.IsSplitMono] :
  g.left_inv ∘ g = 𝟙 Y := g.asSplitMono.inv_hom_id

lemma IsSplitEpi.hom_inv_id [f.IsSplitEpi] :
  f ∘ f.right_inv = 𝟙 Y := f.asSplitEpi.hom_inv_id

instance IsSplitMono.map (F : C ⥤ D) [f.IsSplitMono] :
  F[f].IsSplitMono where
  left_inv := F.map f.left_inv
  inv_hom_id := by
    rw [←F.map_comp, inv_hom_id]
    simp_all

instance IsSplitEpi.map (F : C ⥤ D) [f.IsSplitEpi] :
  F[f].IsSplitEpi where
  right_inv := F.map f.right_inv
  hom_inv_id := by
    rw [←F.map_comp, hom_inv_id]
    simp_all

instance IsSplitMono.IsMono [f.IsSplitMono] : f.IsMono where
  right_uni {_ g h} _ := by
    rw [←Category.comp_id _ g, ←f.asSplitMono.inv_hom_id]
    rw [←Category.comp_id _ h, ←f.asSplitMono.inv_hom_id]
    simp_all

instance IsSplitEpi.IsEpi [f.IsSplitEpi] : f.IsEpi where
  left_uni {_ g h} _ := by
    rw [←Category.id_comp _ g, ←f.asSplitEpi.hom_inv_id]
    rw [←Category.id_comp _ h, ←f.asSplitEpi.hom_inv_id]
    rw [←Category.assoc]
    simp_all

end Split
