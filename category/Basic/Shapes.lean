import MATH.Category.Hom.Iso
import MATH.Category.Hom.FullyFaithful

namespace category
variable (C : Category)

def Zero : Category where
  obj := Empty
  hom x y := Empty
  id := Empty.elim
  comp x y := x

def One : Category where
  obj := Unit
  hom x y := Unit
  id x := Unit.unit
  comp x y := Unit.unit

def Interval : Category where
  obj := Bool
  hom
    | true, false => Empty
    | _, _ => Unit
  id x := match x with
    |  true => Unit.unit
    | false => Unit.unit
  comp := by aesop

class Groupoid where
  iso (f : X ⟶[C] Y) : f.IsIso

class Thin where
  subsingleton (X Y : C.obj) : Subsingleton (X ⟶ Y)

class Discrete extends Thin C where
  eq_of_hom (f : X ⟶[C] Y) : X = Y

class Skeletal where
  auto {X Y : C.obj} : (X ≅ Y) → (X = Y)

class Concrete where
  forget : C ⥤ Types
  faithful : forget.Faithful

class Connected where
  nonempty : Nonempty C.obj
  const (F : C ⥤ D) [Discrete D] (X : C.obj) : F ≅[⟦C, D⟧] Δ[F[X]]
