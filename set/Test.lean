import Mathlib.Data.Set.Lattice
-- import Mathlib.SetTheory.ZFC.PSet

inductive PSet : Type (u + 1)
  | mk  (α : Type u) (A : α → PSet) : PSet
  | mk' (α : Type u) (A : α → PSet) : PSet

namespace PSet

abbrev compl : PSet → PSet
  | mk  α A => mk' α A
  | mk' α A => mk  α A

notation X "ᶜ" => compl X

/-- The underlying type of a pre-set -/
def «Type» : PSet → Type u
  | mk  α _ => α
  | mk' α _ => α

/-- The underlying pre-set family of a pre-set -/
def Func : ∀ x : PSet, x.Type → PSet
  | mk  _ A => A
  | mk' _ A => A

@[simp]
theorem mk_type (α A) : «Type» (mk α A) = α :=
  rfl

@[simp]
theorem mk'_type (α A) : «Type» (mk' α A) = α :=
  rfl

@[simp]
theorem mk_func (α A) : Func (mk α A) = A :=
  rfl

@[simp]
theorem mk'_func (α A) : Func (mk' α A) = A :=
  rfl

-- @[simp]
-- theorem eta : ∀ x : PSet, mk x.Type x.Func = x
--   | ⟨_, _⟩ => rfl

def Equiv : PSet.{u} → PSet.{u} → Prop
  -- (∀ z : PSet, Mem (mk x X) z ↔ Mem (mk y Y) z)
  | mk _ X, mk _ Y =>
    (∀ a, ∃ b, Equiv (X a) (Y b)) ∧ (∀ b, ∃ a, Equiv (X a) (Y b))
  | mk' _ X, mk' _ Y =>
    (∀ a, ∃ b, Equiv (X a) (Y b)) ∧ (∀ b, ∃ a, Equiv (X a) (Y b))
  | _, _ => False



@[refl]
protected theorem Equiv.refl : ∀ x, Equiv x x
  | mk  _ _ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩
  | mk' _ _ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩

protected theorem Equiv.rfl {x} : Equiv x x :=
  Equiv.refl x

protected theorem Equiv.euc
  (p : Equiv x y) (q : Equiv z y) : Equiv x z := match x, y, z with
  | mk  _ _,  mk  _ _,  mk _ _ =>
    ⟨fun a => let ⟨b, h⟩ := p.1 a; let ⟨c, k⟩ := q.2 b; ⟨c, .euc h k⟩,
    fun a => let ⟨b, h⟩ := q.1 a; let ⟨c, k⟩ := p.2 b; ⟨c, .euc k h⟩⟩
  | mk' _ _, mk' _ _, mk' _ _ =>
    ⟨fun a => let ⟨b, h⟩ := p.1 a; let ⟨c, k⟩ := q.2 b; ⟨c, .euc h k⟩,
    fun a => let ⟨b, h⟩ := q.1 a; let ⟨c, k⟩ := p.2 b; ⟨c, .euc k h⟩⟩

@[symm]
protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc

protected theorem Equiv.comm {x y} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm

instance setoid : Setoid PSet :=
  ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩


/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family `y`. -/
def Mem (y x : PSet.{u}) : Prop := match y with
  | mk  _ B => ∃ b, Equiv x (B b)
  | mk' _ B => ∀ b, ¬ Equiv x (B b)


instance : Membership PSet PSet :=
  ⟨PSet.Mem⟩

@[simp]
theorem Mem.dual' (x : PSet) :
  x ∉ mk' α A ↔ x ∈ mk α A := ⟨
    fun (p : (∀_, _) → _) => by simp at p; exact p,
    fun p (q : ∀_, _) => let ⟨p₀, p₁⟩ := p; let q₀ := q p₀; by simp_all
  ⟩

theorem Mem.dual (x y : PSet) :
  x ∉ yᶜ ↔ x ∈ y := match y with
  | mk  _ B => by simp
  | mk' _ B => by simp [←dual']

theorem Mem.mk {α : Type u} (A : α → PSet) (a : α) : A a ∈ mk α A :=
  ⟨a, Equiv.refl (A a)⟩

theorem Mem.mk' {α : Type u} (A : α → PSet) (a : α) : ¬ A a ∈ mk' α A :=
  (Mem.dual (A a) (PSet.mk α A)).2 (mk A a)

theorem Mem.ext : ∀ {x y : PSet.{u}},
  (∀ w, w ∈ x ↔ w ∈ y) → Equiv x y := by simp

theorem Mem.congr_right : ∀ {x y : PSet.{u}},
  Equiv x y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y := by simp_all

theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  ⟨Mem.congr_right, Mem.ext⟩


/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family. -/
protected def Subset (x y : PSet) : Prop :=
  ∀ a, (a ∈ x) → (a ∈ y)

instance : HasSubset PSet :=
  ⟨PSet.Subset⟩

instance : IsRefl PSet (· ⊆ ·) :=
  ⟨fun _ _ p => p⟩

instance : IsTrans PSet (· ⊆ ·) :=
  ⟨fun _ _ _ hxy hyz x p =>
    hyz x (hxy x p)⟩

-- theorem Equiv.ext : ∀ x y : PSet, Equiv x y ↔ x ⊆ y ∧ y ⊆ x :=
--   fun _ _ => ⟨
--     fun p => ⟨fun c => (p.1 c).1, fun c => (p.1 c).2⟩,
--     fun p => ⟨fun c => ⟨p.1 c, p.2 c⟩, fun c => sorry⟩⟩


instance : Preorder PSet where
  le := (· ⊆ ·)
  le_refl := refl_of (· ⊆ ·)
  le_trans _ _ _ := trans_of (· ⊆ ·)

instance : HasSSubset PSet := ⟨(· < ·)⟩

@[simp]
theorem le_def (x y : PSet) : x ≤ y ↔ x ⊆ y :=
  Iff.rfl

@[simp]
theorem lt_def (x y : PSet) : x < y ↔ x ⊂ y :=
  Iff.rfl

instance : IsNonstrictStrictOrder PSet (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ ↦ Iff.rfl⟩

-- theorem Mem.congr_left : ∀ {x y : PSet.{u}},
--   Equiv x y → ∀ {w : PSet.{u}}, x ∈ w ↔ y ∈ w
--   | x, y, h, PSet.mk  w W => by
--     apply Iff.intro
--     . intro p
--       let ⟨c, q⟩ := p
--       apply Exists.intro
--       case w => exact c
--       . let tmp := h.symm
--         rw [q] at tmp
--         dsimp at tmp
--         sorry
--     . intro p
--       let ⟨c, q⟩ := p
--       apply Exists.intro
--       case w => exact c
--       . sorry
--   | _, _, h, PSet.mk' _ _ => ⟨sorry, sorry⟩
-- ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩


def singleton (x : PSet.{u}) : PSet := mk PUnit fun _ => x

theorem singleton_self (x : PSet.{u}) : x ∈ singleton x := ⟨.unit, by simp⟩

theorem singleton_iff (x y : PSet.{u}) : y ∈ singleton x ↔ x = y := ⟨
  fun p : ∃ _, _ => by simp at p; exact p.symm,
  fun p => ⟨.unit, by simp; exact p.symm⟩⟩


/-- The empty pre-set -/
protected def empty : PSet :=
  mk _ PEmpty.elim

instance : EmptyCollection PSet :=
  ⟨PSet.empty⟩

instance : Inhabited PSet :=
  ⟨∅⟩

instance : IsEmpty («Type» ∅) :=
  ⟨PEmpty.elim⟩

theorem empty_def : (∅ : PSet) = mk _ PEmpty.elim := rfl

@[simp]
theorem notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1


-- @[simp]
-- theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]

@[simp]
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) ⊆ x := fun x p =>
  let sd := notMem_empty x
  by simp_all

-- @[simp]
-- theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]


abbrev univ : PSet := ∅ᶜ

@[simp]
theorem isMem_Universe (x : PSet.{u}) : x ∈ univ := by
  let h := (Mem.dual x ∅).not.2 (notMem_empty x)
  simp at h
  exact h

@[simp]
theorem Universe_subset (x : PSet.{u}) : x ⊆ univ :=
  fun p q => by simp
