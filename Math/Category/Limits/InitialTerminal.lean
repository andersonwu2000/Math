import MATH.Category.Limits.Basic

/-!
# Limits/InitialTerminal.lean

Initial / terminal object，由 identity functor 的 limit / colimit 定義。

## 定義
- `HasInitial C` — C 有 initial object（唯一態射到任意 object）
- `HasTerminal C` — C 有 terminal object（唯一態射從任意 object）

## 定理
### `HasInitial`
- `.map_id` — `init_map I = 𝟙 init`
- `.ofHasLimit` — `HasLimit (𝟭 C)` 構造 initial object
- `.toHasLimit` — initial object 構造 `HasLimit (𝟭 C)`
- `.unique` — initial object 在 iso 下唯一
### `HasTerminal`
- `.map_id` — `term_map T = 𝟙 term`
- `.ofHascoLimit` — `HascoLimit (𝟭 C)` 構造 terminal object
- `.toHascoLimit` — terminal object 構造 `HascoLimit (𝟭 C)`
- `.unique` — terminal object 在 iso 下唯一
-/

namespace CategoryTheory

/-- `HasInitial C`：C 有 initial object，對任意 Y 有唯一態射 `init ⟶ Y` -/
structure HasInitial (C : Category) where
  /-- Initial object -/
  init : C.obj
  /-- 唯一態射 `init ⟶ Y` -/
  map (Y : C.obj) : init ⟶ Y
  map_unique {Y : C.obj} (f : init ⟶ Y) : f = map Y

/-- `HasTerminal C`：C 有 terminal object，對任意 X 有唯一態射 `X ⟶ term` -/
structure HasTerminal (C : Category) where
  /-- Terminal object -/
  term : C.obj
  /-- 唯一態射 `X ⟶ term` -/
  map (X : C.obj) : X ⟶ term
  map_unique {X : C.obj} (f : X ⟶ term) : f = map X

namespace HasInitial

variable {C : Category}

@[simp]
lemma map_id (h : HasInitial C) : h.map h.init = 𝟙 h.init :=
  (h.map_unique (𝟙 h.init)).symm

/-- Limit cone 在 lim 的分量為 𝟙（關鍵引理） -/
private lemma cone_lim_id (h : HasLimit (Cat.id C)) : h.Cone·h.lim = 𝟙 h.lim := by
  -- 自然性：∀ g : X ⟶ Y, h.Cone·Y = g ○ h.Cone·X
  have nat : ∀ {X Y : C.obj} (g : X ⟶ Y), h.Cone·Y = g ○ h.Cone·X := by
    intro X Y g
    have := h.Cone.naturality g
    simp [Diagonal, Cat] at this
    exact this
  -- h.Cone·X ○ h.Cone·lim = h.Cone·X（取 g = h.Cone·X : lim → X）
  have right_id : ∀ (X : C.obj), h.Cone·X ○ h.Cone·h.lim = h.Cone·X :=
    fun X => (nat (X := h.lim) (Y := X) (h.Cone·X)).symm
  -- h.Cone = h.Cone ○ Δ[h.Cone·lim]
  have eq1 : h.Cone = h.Cone ○[⟦C, C⟧] Δ[h.Cone·h.lim] := by
    ext X; simp [NatTrans.vcomp_app, Diagonal]; exact (right_id X).symm
  -- h.Cone = h.Cone ○ Δ[𝟙 lim]
  have eq2 : h.Cone = h.Cone ○[⟦C, C⟧] Δ[𝟙 h.lim] := by
    ext X; simp [NatTrans.vcomp_app, Diagonal]
  -- 由唯一性：h.Cone·lim = 𝟙 lim
  have u1 := h.factor_unique h.Cone (h.Cone·h.lim) eq1
  have u2 := h.factor_unique h.Cone (𝟙 h.lim) eq2
  exact u1.trans u2.symm

/-- `HasLimit (𝟭 C)` 構造 initial object -/
noncomputable def ofHasLimit (h : HasLimit (Cat.id C)) : HasInitial C where
  init := h.lim
  map Y := h.Cone·Y
  map_unique {Y} f := by
    have nat : ∀ {X Y : C.obj} (g : X ⟶ Y), h.Cone·Y = g ○ h.Cone·X := by
      intro X Y g
      have := h.Cone.naturality g
      simp [Diagonal, Cat] at this
      exact this
    have key := nat (X := h.lim) (Y := Y) f
    rw [cone_lim_id h] at key
    simp at key
    exact key.symm

/-- Initial object 構造 `HasLimit (𝟭 C)` -/
noncomputable def toHasLimit (h : HasInitial C) : HasLimit (Cat.id C) :=
  HasLimit.ofCone h.init
    -- Cone：Δ[init] ⇒ 𝟭 C，分量為唯一態射 h.map Y
    { app := h.map
      naturality := fun {X Y} g => by
        simp [Diagonal, Cat]
        exact (h.map_unique (g ○ h.map X)).symm }
    -- Couniversal：∀ Y, φ : Δ[Y] ⇒ 𝟭 C，∃! f : Y → init 使 φ = Cone ○ Δ[f]
    (fun Y φ => ⟨
      -- 唯一候選：f = φ·init（取 X = init 代入）
      φ·h.init,
      -- factorization：φ·X = h.map X ○ φ·init（由 φ 在 h.map X 的自然性）
      by ext X
         simp [NatTrans.vcomp_app, Diagonal]
         have := φ.naturality (h.map X)
         simp [Diagonal, Cat] at this
         exact this,
      -- uniqueness：φ·X = h.map X ○ g，取 X = init 得 g = φ·init
      fun g hg => by
        have := congrFun (congrArg NatTrans.app hg) h.init
        simp [NatTrans.vcomp_app, Diagonal, Cat] at this
        exact this.symm⟩)

/-- Initial object 在 iso 下唯一 -/
noncomputable def unique (h₁ h₂ : HasInitial C) : h₁.init ≅ h₂.init :=
  HasLimit.unique h₁.toHasLimit h₂.toHasLimit

end HasInitial

namespace HasTerminal

variable {C : Category}

@[simp]
lemma map_id (h : HasTerminal C) : h.map h.term = 𝟙 h.term :=
  (h.map_unique (𝟙 h.term)).symm

/-- Colimit cocone 在 colim 的分量為 𝟙（關鍵引理） -/
private lemma cocone_colim_id (h : HascoLimit (Cat.id C)) :
    h.coCone·h.colim = 𝟙 h.colim := by
  -- 自然性：∀ g : X ⟶ Y, h.coCone·X = h.coCone·Y ○ g
  -- (cocone : 𝟭 C ⇒ Δ[colim]，naturality: coCone·Y ○ g = 𝟙 colim ○ coCone·X = coCone·X)
  have nat : ∀ {X Y : C.obj} (g : X ⟶ Y), h.coCone·X = h.coCone·Y ○ g := by
    intro X Y g
    have := h.coCone.naturality g
    simp [Diagonal, Cat] at this
    exact this.symm
  -- h.coCone·colim ○ h.coCone·X = h.coCone·X
  have left_id : ∀ (X : C.obj), h.coCone·h.colim ○ h.coCone·X = h.coCone·X :=
    fun X => (nat (X := X) (Y := h.colim) (h.coCone·X)).symm
  have eq1 : h.coCone = Δ[h.coCone·h.colim] ○[⟦C, C⟧] h.coCone := by
    ext X; simp [NatTrans.vcomp_app, Diagonal]; exact (left_id X).symm
  have eq2 : h.coCone = Δ[𝟙 h.colim] ○[⟦C, C⟧] h.coCone := by
    ext X; simp [NatTrans.vcomp_app, Diagonal]
  have u1 := h.factor_unique h.coCone (h.coCone·h.colim) eq1
  have u2 := h.factor_unique h.coCone (𝟙 h.colim) eq2
  exact u1.trans u2.symm

/-- `HascoLimit (𝟭 C)` 構造 terminal object -/
noncomputable def ofHascoLimit (h : HascoLimit (Cat.id C)) : HasTerminal C where
  term := h.colim
  map X := h.coCone·X
  map_unique {X} f := by
    have nat : ∀ {X Y : C.obj} (g : X ⟶ Y), h.coCone·X = h.coCone·Y ○ g := by
      intro X Y g
      have := h.coCone.naturality g
      simp [Diagonal, Cat] at this
      exact this.symm
    have key := nat (X := X) (Y := h.colim) f
    rw [cocone_colim_id h] at key
    simp at key
    exact key.symm

/-- Terminal object 構造 `HascoLimit (𝟭 C)` -/
noncomputable def toHascoLimit (h : HasTerminal C) : HascoLimit (Cat.id C) :=
  HascoLimit.ofcoCone h.term
    { app := h.map
      naturality := fun {X Y} g => by
        simp [Diagonal, Cat]
        exact h.map_unique (h.map Y ○ g) }
    (fun Y φ => ⟨
      φ·h.term,
      by ext X
         simp [NatTrans.vcomp_app, Diagonal]
         have := φ.naturality (h.map X)
         simp [Diagonal, Cat] at this
         exact this.symm,
      fun g hg => by
        have := congrFun (congrArg NatTrans.app hg) h.term
        simp [NatTrans.vcomp_app, Diagonal, Cat] at this
        exact this.symm⟩)

/-- Terminal object 在 iso 下唯一 -/
noncomputable def unique (h₁ h₂ : HasTerminal C) : h₁.term ≅ h₂.term :=
  HascoLimit.unique h₁.toHascoLimit h₂.toHascoLimit

end HasTerminal

end CategoryTheory
