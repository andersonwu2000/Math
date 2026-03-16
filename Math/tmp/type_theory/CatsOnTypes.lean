import Mathlib.CategoryTheory.Closed.Cartesian
import MATH.type_theory.Defs

open CategoryTheory

-- instance Types : Category Type where
--   Hom a b  := a → b
--   id _     := id
--   comp f g := g ∘ f

instance : Coe (Type → Prop) (Type 1) where
  coe φ := {A : Type // φ A}

instance Types.FullSub (φ : Type → Prop) : Category ↑φ where
  Hom := fun ⟨X, _⟩ ⟨Y, _⟩ => X → Y
  id _ := id
  comp := fun f g => g ∘ f

@[ext]
theorem types_ext {φ : Type → Prop} {X Y : ↑φ}
    (f g : X ⟶ Y) (h : ∀ a : X.1, f a = g a) :
    f = g := by
  funext x
  exact h x

abbrev Types.SelfProd (φ : Type → Prop) [Category ↑φ] :=
  ∀ (A : ↑φ) (f : A.1 → ↑φ),
  Limits.HasLimit (Discrete.functor f)

abbrev Types.SelfCoprod (φ : Type → Prop) [Category ↑φ] :=
  ∀ (A : ↑φ) (f : A.1 → ↑φ),
  Limits.HasColimit (Discrete.functor f)


class T_CategoryStruct (T : SimpTheory φ) (obj : Type u) where
  hom : obj → obj → ↑φ
  id (X : obj) : (hom X X).1
  comp {X Y Z : obj} : (hom Y Z).1 × (hom X Y).1 → (hom X Z).1
notation X "->" Y =>
  (fun X Y => (T_category_struct.hom X Y).1) X Y

class T_Category (T : SimpTheory φ) (obj : Type u) extends
  T_CategoryStruct T obj where
  id_comp {X Y : obj} (f : (hom X Y).1) : comp (f, id X) = f
  comp_id {X Y : obj} (f : (hom X Y).1) : comp (id Y, f) = f
  assoc {W X Y Z : obj}
    (f : (hom W X).1) (g : (hom X Y).1) (h : (hom Y Z).1) :
    comp (h, comp (g, f)) = comp (comp (h, g), f)

instance to_T_Category (T : SimpTheory φ) : T_Category T ↑φ where
  hom X Y := ⟨X.1 → Y.1, T.func X.2 Y.2⟩
  id X := fun x => x
  comp := fun (g, f) x => g (f x)
  id_comp f := by simp
  comp_id f := by simp
  assoc f g h := by simp

structure T_Functor (C : Type u) (D : Type v)
  [c : T_Category T C] [d : T_Category T D] where
  obj : C → D
  map : (c.hom X Y).1 → (d.hom (obj X) (obj Y)).1
  map_id (X : C) : map (c.id X) = d.id (obj X)
  map_comp (f : (c.hom X Y).1) (g : (c.hom Y Z).1) :
    map (c.comp (g, f)) = d.comp (map g, map f)

structure T_Cone [c : T_Category T J] [d : T_Category T D]
  (F : T_Functor (c := c) (d := d) J D) where
  pt : D
  app (j : J) : (d.hom pt (F.obj j)).1
  naturality (f : (c.hom i j).1) : d.comp (F.map f, app i) = app j

structure T_IsLimit [c : T_Category T J] [d : T_Category T D]
  {F : T_Functor (c := c) (d := d) J D} (t : T_Cone F) where
  lift (s : T_Cone F) : (d.hom s.pt t.pt).1
  fac (s : T_Cone F) (j : J) : d.comp (t.app j, lift s) = s.app j
  uniq (s : T_Cone F) (m : (d.hom s.pt t.pt).1) :
    (∀ j : J, d.comp (t.app j, m) = s.app j) → m = lift s

abbrev T_CompleteCategory {T : SimpTheory φ} [c : T_Category T C] :=
  ∀ J, [j : T_Category T J] → φ J →
  ∀ F : T_Functor (c := j) (d := c) J C,
  ∃ L : T_Cone F, Nonempty (T_IsLimit L)
