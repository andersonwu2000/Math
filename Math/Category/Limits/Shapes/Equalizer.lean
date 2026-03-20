import MATH.Category.Limits.Complete
import MATH.Category.Structure.Shapes

/-!
# Limits/Shapes/Equalizer.lean

Equalizer / coequalizer：parallel pair 圖的 limit / colimit。

## 定義
- `Equalizer f g` — `Limit (parallelPairFunctor f g)`
- `CoEqualizer f g` — `CoLimit (parallelPairFunctor f g)`
- `EqualizerData f g` — equalizer object `obj`、fork morphism `π`、universal `lift`
- `CoEqualizerData f g` — coequalizer object `obj`、cofork morphism `ι`、universal `desc`

## 定理
### `Equalizer`
- `.data` — `Equalizer` ⟹ `EqualizerData`
- `.unique` — equalizer 在 iso 下唯一
- `ShapeComplete.instEqualizer` — `ShapeComplete` ⟹ `Equalizer`
### `EqualizerData`
- `.toEqualizer` — `EqualizerData` ⟹ `Equalizer`
### `CoEqualizer`
- `.data` — `CoEqualizer` ⟹ `CoEqualizerData`
- `.unique` — coequalizer 在 iso 下唯一
- `ShapeCoComplete.instCoEqualizer` — `ShapeCoComplete` ⟹ `CoEqualizer`
### `CoEqualizerData`
- `.toCoEqualizer` — `CoEqualizerData` ⟹ `CoEqualizer`
-/

namespace CategoryTheory

variable (f g : A ⟶[C] B)

/-- Equalizer：`Limit (parallelPairFunctor f g)` -/
class Equalizer extends Limit (parallelPairFunctor f g)

/-- CoEqualizer：`CoLimit (parallelPairFunctor f g)` -/
class CoEqualizer extends CoLimit (parallelPairFunctor f g)

/-- Equalizer：equalizer object `obj`、fork morphism `π`、universal `lift` -/
structure EqualizerData where
  obj : C.obj
  π : obj ⟶ A
  cond : f ○ π = g ○ π
  lift (h : Z ⟶ A) (hh : f ○ h = g ○ h) : Z ⟶ obj
  lift_π (h : Z ⟶ A) (hh : f ○ h = g ○ h) : π ○ lift h hh = h
  lift_unique (h : Z ⟶ A) (hh : f ○ h = g ○ h) (k : Z ⟶ obj)
      (hk : π ○ k = h) : k = lift h hh

/-- CoEqualizer：coequalizer object `obj`、cofork morphism `ι`、universal `desc` -/
structure CoEqualizerData where
  obj : C.obj
  ι : B ⟶ obj
  cond : ι ○ f = ι ○ g
  desc (h : B ⟶ Z) (hh : h ○ f = h ○ g) : obj ⟶ Z
  desc_ι (h : B ⟶ Z) (hh : h ○ f = h ○ g) : desc h hh ○ ι = h
  desc_unique (h : B ⟶ Z) (hh : h ○ f = h ○ g) (k : obj ⟶ Z)
      (hk : k ○ ι = h) : k = desc h hh

-- ─── Equalizer ────────────────────────────────────────────────────────────────

namespace Equalizer

private def mkFork (h : Z ⟶ A) (hh : f ○ h = g ○ h) :
    Δ[Z] ⇒ parallelPairFunctor f g where
  app j    := match j with | .zero => h | .one => f ○ h
  naturality m := by
    cases m <;> simp only [Diagonal, Category.id_comp]
    · rename_i x; cases x <;> simp
    · exact hh

/-- `Equalizer` ⟹ `EqualizerData` -/
noncomputable def data (eq : Equalizer f g) : EqualizerData f g :=
  let ld := Limit.data (⟨eq.lim, eq.universal⟩ : Limit _)
  { obj  := eq.lim
    π    := ld.cone·.zero
    cond := by
      have l := ld.cone.naturality WalkingParallelPairMor.left
      have r := ld.cone.naturality WalkingParallelPairMor.right
      simpa using l.symm.trans r
    lift h hh := ld.lift (mkFork f g h hh)
    lift_π h hh := by simpa using ld.lift_π (mkFork f g h hh) .zero
    lift_unique h hh k hk :=
      ld.lift_unique (mkFork f g h hh) k (by
        intro j; cases j
        next => simpa using hk
        next =>
          have hnat := ld.cone.naturality WalkingParallelPairMor.left
          simp only [Diagonal, Category.id_comp] at hnat; rw [hnat, Category.assoc, hk]
          simp [mkFork]) }

/-- Equalizer 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Equalizer f g) : h₁.lim ≅ h₂.lim :=
  CoUniversal.unique h₁.universal h₂.universal

instance (priority := 100) ShapeComplete.instEqualizer
    [h : ShapeComplete WalkingParallelPairCat C] : Equalizer f g where
  lim := (h.hasLimit (parallelPairFunctor f g)).lim
  universal := (h.hasLimit (parallelPairFunctor f g)).universal

end Equalizer

/-- `EqualizerData` ⟹ `Equalizer` -/
@[reducible]
noncomputable def EqualizerData.toEqualizer (ed : EqualizerData f g) : Equalizer f g where
  lim := ed.obj
  universal := (LimitData.toLimit {
    obj  := ed.obj
    cone := show Δ[ed.obj] ⇒ parallelPairFunctor f g from {
      app j := match j with | .zero => ed.π | .one => f ○ ed.π
      naturality m := by
        match m with
        | .refl x => cases x <;> simp
        | .left   => simp
        | .right  => simpa using ed.cond }
    lift φ := ed.lift (φ·.zero) (by
      have l := φ.naturality WalkingParallelPairMor.left
      have r := φ.naturality WalkingParallelPairMor.right
      simpa using l.symm.trans r)
    lift_π φ j := by
      cases j
      next => simpa using ed.lift_π _ _
      next =>
        rw [Category.assoc, ed.lift_π]
        have := φ.naturality WalkingParallelPairMor.left
        simp at this; exact this.symm
    lift_unique φ k hk :=
      ed.lift_unique _ _ k (by simpa using hk .zero)
  }).universal

-- ─── CoEqualizer ──────────────────────────────────────────────────────────────

namespace CoEqualizer

private def mkCofork (h : B ⟶ Z) (hh : h ○ f = h ○ g) :
    parallelPairFunctor f g ⇒ Δ[Z] where
  app j    := match j with | .zero => h ○ f | .one => h
  naturality m := by
    cases m <;> simp only [Diagonal, Category.comp_id]
    · rename_i x; cases x <;> simp
    · exact hh.symm

/-- `CoEqualizer` ⟹ `CoEqualizerData` -/
noncomputable def data (coeq : CoEqualizer f g) : CoEqualizerData f g :=
  let cd := CoLimit.data (⟨coeq.colim, coeq.universal⟩ : CoLimit _)
  { obj  := coeq.colim
    ι    := cd.cocone·.one
    cond := by
      have l := cd.cocone.naturality WalkingParallelPairMor.left
      have r := cd.cocone.naturality WalkingParallelPairMor.right
      simp at l r; exact l.trans r.symm
    desc h hh := cd.desc (mkCofork f g h hh)
    desc_ι h hh := by simpa using cd.desc_ι (mkCofork f g h hh) .one
    desc_unique h hh k hk :=
      cd.desc_unique (mkCofork f g h hh) k (by
        intro j; cases j
        next =>
          have hnat := cd.cocone.naturality WalkingParallelPairMor.left
          simp only [Diagonal, Category.comp_id] at hnat; rw [← hnat, ← Category.assoc, hk]
          simp [mkCofork]
        next => simpa using hk) }

/-- CoEqualizer 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : CoEqualizer f g) : h₁.colim ≅ h₂.colim :=
  Universal.unique h₁.universal h₂.universal

instance (priority := 100) ShapeCoComplete.instCoEqualizer
    [h : ShapeCoComplete WalkingParallelPairCat C] : CoEqualizer f g where
  colim := (h.hascolimit (parallelPairFunctor f g)).colim
  universal := (h.hascolimit (parallelPairFunctor f g)).universal

end CoEqualizer

/-- `CoEqualizerData` ⟹ `CoEqualizer` -/
@[reducible]
noncomputable def CoEqualizerData.toCoEqualizer (ced : CoEqualizerData f g) : CoEqualizer f g where
  colim := ced.obj
  universal := (CoLimitData.toCoLimit {
    obj    := ced.obj
    cocone := show parallelPairFunctor f g ⇒ Δ[ced.obj] from {
      app j := match j with | .zero => ced.ι ○ f | .one => ced.ι
      naturality m := by
        match m with
        | .refl x => cases x <;> simp
        | .left   => simp
        | .right  => simpa using ced.cond.symm }
    desc φ := ced.desc (φ·.one) (by
      have l := φ.naturality WalkingParallelPairMor.left
      have r := φ.naturality WalkingParallelPairMor.right
      simp at l r; exact l.trans r.symm)
    desc_ι φ j := by
      cases j
      next =>
        rw [← Category.assoc, ced.desc_ι]
        have := φ.naturality WalkingParallelPairMor.left
        simpa using this
      next => exact ced.desc_ι _ _
    desc_unique φ k hk :=
      ced.desc_unique _ _ k (by simpa using hk .one)
  }).universal

end CategoryTheory
