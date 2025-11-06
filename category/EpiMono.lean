import MATH.category.Basic

/-
`Mono Epi`
  op comp cancel
`Category.hom`
  IsMono IsEpi
  Mono Epi : Is... to ...
  hom_eq
  right_uni left_uni

`Split Mono/Epi`
  op comp
  Mono Epi
`Category.hom`
  IsSplitMono IsSplitEpi
  SplitMono SplitEpi : Is... to ...
  hom_eq
  id_left id_right
  SplitMono_Epi_IsIso
  SplitEpi_Mono_IsIso
-/

-- set_option trace.Meta.synthInstance true
-- set_option profiler true

namespace category

structure Mono {C} (X Y) where
  hom : X ⟶[C] Y
  right_uni : hom ∘ f = hom ∘ g → f = g := by simp

notation X "↣[" C "]" Y => @Mono C X Y
notation X "↣" Y => Mono X Y

structure Epi {C} (X Y) where
  hom : X ⟶[C] Y
  left_uni : f ∘ hom = g ∘ hom → f = g := by simp

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

@[simp]
theorem Mono.cancel (f : X ↣ Y) :
  f.hom ∘ g = f.hom ∘ h ↔ g = h := by
  apply Iff.intro
  . intro p
    exact f.right_uni p
  . exact Whisker.left_cancel f.hom

@[simp]
theorem Epi.cancel (f : X ↠ Y) :
  g ∘ f.hom = h ∘ f.hom ↔ g = h :=
  f.op.cancel

namespace Category.hom
variable (f : X ⟶ Y)

class IsMono where
  right_uni : f ∘ g = f ∘ h → g = h := by simp

class IsEpi where
  left_uni : g ∘ f = h ∘ f → g = h := by simp

def Mono [p : f.IsMono] : X ↣ Y where
  hom := f
  right_uni := p.right_uni

def Epi [p : f.IsEpi] : X ↠ Y where
  hom := f
  left_uni := p.left_uni


lemma Mono_hom_eq [f.IsMono] : f = f.Mono.hom := rfl

lemma Epi_hom_eq [f.IsEpi] : f = f.Epi.hom := rfl

lemma Mono.right_uni [f.IsMono] :
  f ∘ g = f ∘ h → g = h := by
  conv_lhs => rw [f.Mono_hom_eq]
  exact f.Mono.right_uni

lemma Epi.left_uni [f.IsEpi] :
  g ∘ f = h ∘ f → g = h := by
  conv_lhs => rw [f.Epi_hom_eq]
  exact f.Epi.left_uni

end Category.hom


section Split

@[ext]
structure SplitMono {C} (X Y) where
  hom : X ⟶[C] Y
  left_inv : Y ⟶[C] X
  id_left : left_inv ∘ hom = 𝟙 X := by simp

@[ext]
structure SplitEpi {C} (X Y) where
  hom : X ⟶[C] Y
  right_inv : Y ⟶[C] X
  id_right : hom ∘ right_inv = 𝟙 Y := by simp

abbrev SplitMono.op
  (f : @SplitMono C X Y) : SplitEpi (C := Cᵒᵖ) Y X where
  hom := f.hom
  right_inv := f.left_inv
  id_right := f.id_left

abbrev SplitEpi.op
  (f : @SplitEpi C X Y) : SplitMono (C := Cᵒᵖ) Y X where
  hom := f.hom
  left_inv := f.right_inv
  id_left := f.id_right

abbrev SplitMono.comp
  (f : SplitMono X Y) (g : SplitMono Y Z) : SplitMono X Z where
  hom := g.hom ∘ f.hom
  left_inv := f.left_inv ∘ g.left_inv
  id_left := by
    have : g.left_inv ∘ (g.hom ∘ f.hom) = f.hom := by
      rw [←Category.assoc, g.id_left]
      simp
    simp_all only [Category.assoc]
    rw [f.id_left]

abbrev SplitEpi.comp
  (f : SplitEpi X Y) (g : SplitEpi Y Z) : SplitEpi X Z :=
  (SplitMono.comp g.op f.op).op

abbrev SplitMono.Mono
  (f : @SplitMono C X Y): X ↣ Y where
  hom := f.hom
  right_uni {Z g h} p := by
    rw [←C.comp_id g, ←f.id_left]
    rw [←C.comp_id h, ←f.id_left]
    rw [C.assoc, C.assoc, p]

abbrev SplitEpi.Epi
  (f : SplitEpi X Y): X ↠ Y :=
  f.op.Mono.op


namespace Category.hom
variable (f : X ⟶ Y)

class IsSplitMono where
  left_inv : Y ⟶ X
  id_left : left_inv ∘ f = 𝟙 X := by simp

class IsSplitEpi where
  right_inv : Y ⟶ X
  id_right : f ∘ right_inv = 𝟙 Y := by simp

def SplitMono [p : f.IsSplitMono] : SplitMono X Y where
  hom := f
  left_inv := p.left_inv
  id_left := p.id_left

def SplitEpi [p : f.IsSplitEpi] : SplitEpi X Y where
  hom := f
  right_inv := p.right_inv
  id_right := p.id_right


lemma SplitMono_hom_eq [f.IsSplitMono] :
  f = f.SplitMono.hom := rfl

lemma SplitEpi_hom_eq [f.IsSplitEpi] :
  f = f.SplitEpi.hom := rfl

lemma SplitMono.id_left [f.IsSplitMono] :
  f.SplitMono.left_inv ∘ f = 𝟙 X := by
  conv in f => rw [f.SplitMono_hom_eq]
  exact f.SplitMono.id_left

lemma SplitEpi.id_right [f.IsSplitEpi] :
  f ∘ f.SplitEpi.right_inv = 𝟙 Y := by
  conv in f => rw [f.SplitEpi_hom_eq]
  exact f.SplitEpi.id_right

end Category.hom
