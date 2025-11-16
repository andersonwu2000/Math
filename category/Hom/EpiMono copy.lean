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
attribute [simp] Mono.right_uni
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
attribute [simp] Epi.left_uni
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
    simp_all only [Category.assoc]

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
