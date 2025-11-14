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
--   | PSet.mk _ _ => rfl

def Equiv : PSet.{u} → PSet.{u} → Prop
  -- (∀ z : PSet, Mem (mk x X) z ↔ Mem (mk y Y) z)
  | mk  _ X, mk  _ Y =>
    (∀ a, ∃ b, Equiv (X a) (Y b)) ∧ (∀ b, ∃ a, Equiv (X a) (Y b))
  | mk' _ X, mk' _ Y =>
    (∀ a, ∃ b, Equiv (X a) (Y b)) ∧ (∀ b, ∃ a, Equiv (X a) (Y b))
  -- | mk  _ X, mk' _ Y =>
    -- ∀ x, (∀ a, ¬ Equiv x (X a)) ↔ (∃ b, Equiv x (Y b))
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



/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family. -/
protected def Subset : PSet → PSet → Prop
  | mk  _ A, mk  _ B => ∀ a, ∃ b, Equiv (A a) (B b)
  | mk' _ A, mk  _ B => ∀ x, (∀ a, ¬ Equiv x (A a)) → ∃ b, Equiv x (B b)
  | mk  _ A, mk' _ B => ∀ x, (∃ a, Equiv x (A a)) → ∀ b, ¬ Equiv x (B b)
  | mk' _ A, mk' _ B => ∀ x, (∀ a, ¬ Equiv x (A a)) → ∀ b, ¬ Equiv x (B b)

instance : HasSubset PSet :=
  ⟨PSet.Subset⟩

theorem Subset.in_iff_cinc : mk' y Y ⊆ mk' x X ↔ mk x X ⊆ mk y Y := ⟨
  fun (p : ∀_,_) a => by_contradiction fun q => by
    let h₀ := p (X a)
    simp at q
    let q : ∀ w, ¬ Equiv (X a) (Y w) := fun w p => by
      have := q w
      contradiction
    have := (h₀ q) a
    have := Equiv.refl (X a)
    contradiction,
  fun p x q b r => by
    let ⟨b', p'⟩ := p b;
    have := Equiv.trans r p'
    have := q b'
    contradiction
⟩

instance : IsRefl PSet (· ⊆ ·) := ⟨fun a => match a with
  | mk  _ _ => fun a => ⟨a, Equiv.refl _⟩
  | mk' _ _ => fun _ p => p⟩

instance : IsTrans PSet (· ⊆ ·) :=
  ⟨fun x y z hxy hyz => match x, y, z with
    | mk  _ _, mk  _ _,  mk  _ _ => fun a => by
      obtain ⟨b, hb⟩ := hxy a; obtain ⟨c, hc⟩ := hyz b; exact ⟨c, hb.trans hc⟩
    | mk  _ _, mk  _ _,  mk' _ _ => fun a ⟨b, p⟩ c q => by
      obtain ⟨b, hb⟩ := hxy b
      obtain r := hyz a
      let h₀ := Equiv.trans p hb
      let h₁ := r ⟨_, h₀⟩ c
      contradiction
    | mk  _ X, mk' _ _,  mk  _ _ => fun a => by
      have h := hxy (X a) ⟨_, Equiv.refl (X a)⟩
      let ⟨b, h⟩ := hyz (X a) h
      exact ⟨b, h⟩
    | mk  _ _, mk' _ Y,  mk' _ _ => fun a ⟨b, p⟩ c q =>
      let p' : ∀_,_ := hxy
      sorry
    | mk' _ _, mk  _ _,  mk  _ _ => sorry
    | mk' _ _, mk  _ _,  mk' _ _ => sorry
    | mk' _ _, mk' _ _,  mk  _ _ => sorry
    | mk' _ _, mk' _ _,  mk' _ _ => Subset.in_iff_cinc.2 sorry
    ⟩

theorem Equiv.ext : ∀ x y : PSet, Equiv x y ↔ x ⊆ y ∧ y ⊆ x
  | .mk  _ _, .mk  _ _ => ⟨
    fun ⟨αβ, βα⟩ => ⟨αβ, fun b => let ⟨a, h⟩ := βα b; ⟨a, Equiv.symm h⟩⟩,
    fun ⟨αβ, βα⟩ => ⟨αβ, fun b => let ⟨a, h⟩ := βα b; ⟨a, Equiv.symm h⟩⟩⟩
  | .mk' _ _, .mk' _ _ => ⟨
    fun ⟨αβ, βα⟩ => ⟨
      Subset.in_iff_cinc.2 sorry,
      Subset.in_iff_cinc.2 sorry⟩,
    fun ⟨αβ, βα⟩ => sorry⟩
  | .mk  _ _, .mk' _ _ => sorry
  | .mk' x X, .mk  y Y => by
    dsimp [Equiv]; simp
    intro p q
    have h : ∀ _, _ ↔ _ := fun x => ⟨p x, q x⟩
    sorry


theorem Subset.congr_left : ∀ {x y z : PSet}, Equiv x y → (x ⊆ z ↔ y ⊆ z)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun αγ b =>
      let ⟨a, ba⟩ := βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩

theorem Subset.congr_right : ∀ {x y z : PSet}, Equiv x y → (z ⊆ x ↔ z ⊆ y)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun γα c =>
      let ⟨a, ca⟩ := γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩

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

theorem Subset.iff {x y : PSet} : x ⊆ y ↔ ∀ z, z ∈ x → z ∈ y := match x, y with
  | mk  _ X, mk  _ _ => ⟨
    fun p z ⟨a, q⟩ => let ⟨b, r⟩ := p a; ⟨b, Equiv.trans q r⟩,
    fun p a => p (X a) (Mem.mk X a)⟩
  | mk  _ _, mk' _ _ => ⟨
    fun p z q b r => let h := p z q b; by contradiction,
    fun p x q b r => let h := p x q b; by contradiction⟩
  | mk' _ _, mk  _ _ => ⟨
    fun p z q => p z q,
    fun p x q => p x q⟩
  | mk' _ _, mk' _ _ => ⟨
    fun p z q => p z q,
    fun p x q => p x q⟩

theorem Mem.ext : ∀ {x y : PSet.{u}},
  (∀ w, w ∈ x ↔ w ∈ y) → Equiv x y := fun {x y} p =>
  match x, y with
  | .mk  _ _, .mk  _ _ => sorry
  | .mk  a X, .mk' b Y => by
    dsimp [Equiv]
    let p : ∀_,(∃_,_)↔(∀_,_) := p
    -- let p : ∀_,_ := p
    simp at p
    let s := Mem.mk Y
    let u := Mem.mk X
    sorry
  | .mk' _ _, .mk  _ _ => sorry
  | .mk' _ _, .mk' _ _ => sorry

theorem Mem.congr_right : ∀ {x y : PSet.{u}},
  Equiv x y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  fun {x y} p w => match x, y with
  | .mk  _ _, .mk  _ _ => ⟨
    fun ⟨b, q⟩ => let ⟨c, q'⟩ := p.1 b; ⟨c, Equiv.trans q q'⟩,
    fun ⟨b, q⟩ => let ⟨c, q'⟩ := p.2 b; ⟨c, Equiv.trans q q'.symm⟩⟩
  | .mk' _ _, .mk' _ _ => ⟨
    fun x b h =>
      let ⟨c, q'⟩ := p.2 b; let s := x c;
      have := Equiv.trans h q'.symm; by contradiction,
    fun x b h => let ⟨c, q'⟩ := p.1 b; let s := x c;
      have := Equiv.trans h q'; by contradiction⟩


theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  ⟨Mem.congr_right, Mem.ext⟩



protected def sep (p : PSet → Prop) : PSet → PSet
  | mk  _ A => mk { a // p (A a) } fun y => A y.1
  | mk' _ A => mk { a // ¬ p (A a) } fun y => (A y.1)ᶜ

instance : Sep PSet PSet :=
  ⟨PSet.sep⟩

theorem mem_sep {p : PSet → Prop} (H : ∀ x y, Equiv x y → p x → p y) :
    ∀ {x y : PSet}, y ∈ PSet.sep p x ↔ y ∈ x ∧ p y
  | .mk  _ _, _ => ⟨
    fun ⟨⟨a, pa⟩, h⟩ => ⟨⟨a, h⟩, H _ _ h.symm pa⟩,
    fun ⟨⟨a, h⟩, pa⟩ => ⟨⟨a, H _ _ h pa⟩, h⟩⟩
  | .mk' _ A, _ => ⟨
    fun ⟨⟨a, pa⟩, h⟩ => ⟨fun x q => by
      simp at h
      sorry, sorry⟩,
    fun ⟨p, pa⟩ => ⟨sorry, sorry⟩⟩




def singleton (x : PSet.{u}) : PSet := mk PUnit fun _ => x

theorem singleton_self (x : PSet.{u}) : x ∈ singleton x := match x with
  | mk  _ _ => ⟨.unit, Equiv.refl _⟩
  | mk' _ _ => ⟨.unit, Equiv.refl _⟩

theorem singleton_iff (x y : PSet.{u}) : y ∈ singleton x ↔ Equiv x y := ⟨
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
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) ⊆ x := match x with
  | mk  _ _ => fun p => p.elim
  | mk' _ _ => fun p => by simp

-- @[simp]
-- theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]


@[simp]
theorem isMem_univ (x : PSet.{u}) : x ∈ ∅ᶜ := by
  let h := (Mem.dual x ∅).not.2 (notMem_empty x)
  simp at h
  exact h

@[simp]
theorem univ_subset (x : PSet.{u}) : x ⊆ ∅ᶜ :=
  match x with
  | mk  _ _ => fun p q => by simp
  | mk' _ _ => fun p => by simp
