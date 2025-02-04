/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.SMulWithZero
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Modules over a ring

In this file we define

* `Module R M` : an additive commutative monoid `M` is a `Module` over a
  `Semiring R` if for `r : R` and `x : M` their "scalar multiplication" `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

## Implementation notes

In typical mathematical usage, our definition of `Module` corresponds to "semimodule", and the
word "module" is reserved for `Module R M` where `R` is a `Ring` and `M` an `AddCommGroup`.
If `R` is a `Field` and `M` an `AddCommGroup`, `M` would be called an `R`-vector space.
Since those assumptions can be made by changing the typeclasses applied to `R` and `M`,
without changing the axioms in `Module`, mathlib calls everything a `Module`.

In older versions of mathlib3, we had separate abbreviations for semimodules and vector spaces.
This caused inference issues in some cases, while not providing any real advantages, so we decided
to use a canonical `Module` typeclass throughout.

## Tags

semimodule, module, vector space
-/

assert_not_exists Multiset
assert_not_exists Set.indicator
assert_not_exists Pi.single_smul₀
assert_not_exists Field

open Function Set

universe u v

variable {α R k S M M₂ M₃ ι : Type*}

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext]
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

-- see Note [lower instance priority]
/-- A module over a semiring automatically inherits a `MulActionWithZero` structure. -/
instance (priority := 100) Module.toMulActionWithZero : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with
    smul_zero := smul_zero
    zero_smul := Module.zero_smul }

instance AddCommGroup.toNatModule : Module ℕ M where
  one_smul := one_nsmul
  mul_smul m n a := mul_nsmul' a m n
  smul_add n a b := nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul r s x := add_nsmul x r s

theorem AddMonoid.End.natCast_def (n : ℕ) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℕ M n :=
  rfl

theorem add_smul : (r + s) • x = r • x + s • x :=
  Module.add_smul r s x

theorem Convex.combo_self {a b : R} (h : a + b = 1) (x : M) : a • x + b • x = x := by
  rw [← add_smul, h, one_smul]

variable (R)

-- Porting note: this is the letter of the mathlib3 version, but not really the spirit
theorem two_smul : (2 : R) • x = x + x := by rw [← one_add_one_eq_two, add_smul, one_smul]

@[simp]
theorem invOf_two_smul_add_invOf_two_smul [Invertible (2 : R)] (x : M) :
    (⅟ 2 : R) • x + (⅟ 2 : R) • x = x :=
  Convex.combo_self invOf_two_add_invOf_two _

/-- Pullback a `Module` structure along an injective additive monoid homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.module [AddCommMonoid M₂] [SMul R M₂] (f : M₂ →+ M)
    (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.distribMulAction f smul with
    add_smul := fun c₁ c₂ x => hf <| by simp only [smul, f.map_add, add_smul]
    zero_smul := fun x => hf <| by simp only [smul, zero_smul, f.map_zero] }

/-- Pushforward a `Module` structure along a surjective additive monoid homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.module [AddCommMonoid M₂] [SMul R M₂] (f : M →+ M₂)
    (hf : Surjective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { toDistribMulAction := hf.distribMulAction f smul
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [add_smul, ← smul, ← f.map_add]
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      rw [← f.map_zero, ← smul, zero_smul] }

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →+* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.distribMulActionLeft`.
-/
abbrev Function.Surjective.moduleLeft {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring S] [SMul S M] (f : R →+* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : Module S M :=
  { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }

variable {R} (M)

/-- Compose a `Module` with a `RingHom`, with action `f s • m`.

See note [reducible non-instances]. -/
abbrev Module.compHom [Semiring S] (f : S →+* R) : Module S M :=
  { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S →* R) with
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication
    add_smul := fun r s x => show f (r + s) • x = f r • x + f s • x by simp [add_smul] }

variable (R)

/-- `(•)` as an `AddMonoidHom`.

This is a stronger version of `DistribMulAction.toAddMonoidEnd` -/
@[simps! apply_apply]
def Module.toAddMonoidEnd : R →+* AddMonoid.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    -- Porting note: the two `show`s weren't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication
    map_zero' := AddMonoidHom.ext fun r => show (0 : R) • r = 0 by simp
    map_add' := fun x y =>
      AddMonoidHom.ext fun r => show (x + y) • r = x • r + y • r by simp [add_smul] }

/-- A convenience alias for `Module.toAddMonoidEnd` as an `AddMonoidHom`, usually to allow the
use of `AddMonoidHom.flip`. -/
def smulAddHom : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

variable {R M}

@[simp]
theorem smulAddHom_apply (r : R) (x : M) : smulAddHom R M r x = r • x :=
  rfl

theorem Module.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 := by
  rw [← one_smul R x, ← zero_eq_one, zero_smul]

@[simp]
theorem smul_add_one_sub_smul {R : Type*} [Ring R] [Module R M] {r : R} {m : M} :
    r • m + (1 - r) • m = m := by rw [← add_smul, add_sub_cancel, one_smul]

end AddCommMonoid


section AddCommGroup

variable (R M) [Semiring R] [AddCommGroup M]

instance AddCommGroup.toIntModule : Module ℤ M where
  one_smul := one_zsmul
  mul_smul m n a := mul_zsmul a m n
  smul_add n a b := zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul r s x := add_zsmul x r s

theorem AddMonoid.End.intCast_def (z : ℤ) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℤ M z :=
  rfl

variable {R M}

theorem Convex.combo_eq_smul_sub_add [Module R M] {x y : M} {a b : R} (h : a + b = 1) :
    a • x + b • y = b • (y - x) + x :=
  calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by rw [sub_add_add_cancel, add_comm]
    _ = b • (y - x) + x := by rw [smul_sub, Convex.combo_self h]

end AddCommGroup

-- We'll later use this to show `Module ℕ M` and `Module ℤ M` are subsingletons.
/-- A variant of `Module.ext` that's convenient for term-mode. -/
theorem Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] (P Q : Module R M)
    (w : ∀ (r : R) (m : M), (haveI := P; r • m) = (haveI := Q; r • m)) :
    P = Q := by
  ext
  exact w _ _

section Module

variable [Ring R] [AddCommGroup M] [Module R M] (r s : R) (x y : M)

@[simp]
theorem neg_smul : -r • x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← add_smul, neg_add_cancel, zero_smul]

-- Porting note (#10618): simp can prove this
--@[simp]
theorem neg_smul_neg : -r • -x = r • x := by rw [neg_smul, smul_neg, neg_neg]

@[simp]
theorem Units.neg_smul (u : Rˣ) (x : M) : -u • x = -(u • x) := by
  rw [Units.smul_def, Units.val_neg, _root_.neg_smul, Units.smul_def]

variable (R)

theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp

variable {R}

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
  simp [add_smul, sub_eq_add_neg]

end Module

variable (R)

/-- An `AddCommMonoid` that is a `Module` over a `Ring` carries a natural `AddCommGroup`
structure.
See note [reducible non-instances]. -/
abbrev Module.addCommMonoidToAddCommGroup
    [Ring R] [AddCommMonoid M] [Module R M] : AddCommGroup M :=
  { (inferInstance : AddCommMonoid M) with
    neg := fun a => (-1 : R) • a
    neg_add_cancel := fun a =>
      show (-1 : R) • a + a = 0 by
        nth_rw 2 [← one_smul R a]
        rw [← add_smul, neg_add_cancel, zero_smul]
    zsmul := fun z a => (z : R) • a
    zsmul_zero' := fun a => by simpa only [Int.cast_zero] using zero_smul R a
    zsmul_succ' := fun z a => by simp [add_comm, add_smul]
    zsmul_neg' := fun z a => by simp [← smul_assoc, neg_one_smul] }

variable {R}

/-- A module over a `Subsingleton` semiring is a `Subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
protected theorem Module.subsingleton (R M : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : Subsingleton M :=
  MulActionWithZero.subsingleton R M

/-- A semiring is `Nontrivial` provided that there exists a nontrivial module over this semiring. -/
protected theorem Module.nontrivial (R M : Type*) [Semiring R] [Nontrivial M] [AddCommMonoid M]
    [Module R M] : Nontrivial R :=
  MulActionWithZero.nontrivial R M

-- see Note [lower instance priority]
instance (priority := 910) Semiring.toModule [Semiring R] : Module R R where
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul
  smul_zero := mul_zero

-- see Note [lower instance priority]
/-- Like `Semiring.toModule`, but multiplies on the right. -/
instance (priority := 910) Semiring.toOppositeModule [Semiring R] : Module Rᵐᵒᵖ R :=
  { MonoidWithZero.toOppositeMulActionWithZero R with
    smul_add := fun _ _ _ => add_mul _ _ _
    add_smul := fun _ _ _ => mul_add _ _ _ }

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`. -/
def RingHom.toModule [Semiring R] [Semiring S] (f : R →+* S) : Module R S :=
  Module.compHom S f

/-- If the module action of `R` on `S` is compatible with multiplication on `S`, then
`fun x ↦ x • 1` is a ring homomorphism from `R` to `S`.

This is the `RingHom` version of `MonoidHom.smulOneHom`.

When `R` is commutative, usually `algebraMap` should be preferred. -/
@[simps!] def RingHom.smulOneHom
    [Semiring R] [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] : R →+* S where
  __ := MonoidHom.smulOneHom
  map_zero' := zero_smul R 1
  map_add' := (add_smul · · 1)

/-- A homomorphism between semirings R and S can be equivalently specified by a R-module
structure on S such that S/S/R is a scalar tower. -/
def ringHomEquivModuleIsScalarTower [Semiring R] [Semiring S] :
    (R →+* S) ≃ {_inst : Module R S // IsScalarTower R S S} where
  toFun f := ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ RingHom.smulOneHom
  left_inv f := RingHom.ext fun r ↦ mul_one (f r)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| Module.ext <| funext₂ <| smul_one_smul S

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
lemma Nat.cast_smul_eq_nsmul (n : ℕ) (b : M) : (n : R) • b = n • b := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul]
  | succ n ih => rw [Nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul]

/-- `nsmul` is equal to any other module structure via a cast. -/
-- See note [no_index around OfNat.ofNat]
lemma ofNat_smul_eq_nsmul (n : ℕ) [n.AtLeastTwo] (b : M) :
    (no_index OfNat.ofNat n : R) • b = OfNat.ofNat n • b := Nat.cast_smul_eq_nsmul ..

/-- `nsmul` is equal to any other module structure via a cast. -/
@[deprecated Nat.cast_smul_eq_nsmul (since := "2024-07-23")]
lemma nsmul_eq_smul_cast (n : ℕ) (b : M) : n • b = (n : R) • b := (Nat.cast_smul_eq_nsmul ..).symm

end

/-- Convert back any exotic `ℕ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommMonoid`s should normally have exactly one `ℕ`-module structure by design.
-/
theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) : @SMul.smul ℕ M h.toSMul n x = n • x :=
  Nat.cast_smul_eq_nsmul ..

/-- All `ℕ`-module structures are equal. Not an instance since in mathlib all `AddCommMonoid`
should normally have exactly one `ℕ`-module structure by design. -/
def AddCommMonoid.uniqueNatModule : Unique (Module ℕ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert nat_smul_eq_nsmul P n

instance AddCommMonoid.nat_isScalarTower : IsScalarTower ℕ R M where
  smul_assoc n x y := by
    induction n with
    | zero => simp only [zero_smul]
    | succ n ih => simp only [add_smul, one_smul, ih]

end AddCommMonoid

section AddCommGroup

variable [Semiring S] [Ring R] [AddCommGroup M] [Module S M] [Module R M]

section

variable (R)

/-- `zsmul` is equal to any other module structure via a cast. -/
lemma Int.cast_smul_eq_zsmul (n : ℤ) (b : M) : (n : R) • b = n • b :=
  have : ((smulAddHom R M).flip b).comp (Int.castAddHom R) = (smulAddHom ℤ M).flip b := by
    apply AddMonoidHom.ext_int
    simp
  DFunLike.congr_fun this n

@[deprecated (since := "2024-07-23")] alias intCast_smul := Int.cast_smul_eq_zsmul

/-- `zsmul` is equal to any other module structure via a cast. -/
@[deprecated Int.cast_smul_eq_zsmul (since := "2024-07-23")]
theorem zsmul_eq_smul_cast (n : ℤ) (b : M) : n • b = (n : R) • b := (Int.cast_smul_eq_zsmul ..).symm

end

/-- Convert back any exotic `ℤ`-smul to the canonical instance. This should not be needed since in
mathlib all `AddCommGroup`s should normally have exactly one `ℤ`-module structure by design. -/
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) : @SMul.smul ℤ M h.toSMul n x = n • x :=
  Int.cast_smul_eq_zsmul ..

/-- All `ℤ`-module structures are equal. Not an instance since in mathlib all `AddCommGroup`
should normally have exactly one `ℤ`-module structure by design. -/
def AddCommGroup.uniqueIntModule : Unique (Module ℤ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert int_smul_eq_zsmul P n

end AddCommGroup

theorem map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M] [Module S M₂]
    (x : ℤ) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by simp only [Int.cast_smul_eq_zsmul, map_zsmul]

theorem map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Semiring R] [Semiring S] [Module R M]
    [Module S M₂] (x : ℕ) (a : M) : f ((x : R) • a) = (x : S) • f a := by
  simp only [Nat.cast_smul_eq_nsmul, AddMonoidHom.map_nsmul, map_nsmul]

instance AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] : IsScalarTower ℤ R M where
  smul_assoc n x y := ((smulAddHom R M).flip y).map_zsmul x n

section NoZeroSMulDivisors

/-! ### `NoZeroSMulDivisors`

This section defines the `NoZeroSMulDivisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).
-/


/-- `NoZeroSMulDivisors R M` states that a scalar multiple is `0` only if either argument is `0`.
This is a version of saying that `M` is torsion free, without assuming `R` is zero-divisor free.

The main application of `NoZeroSMulDivisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0`.

It is a generalization of the `NoZeroDivisors` class to heterogeneous multiplication.
-/
@[mk_iff]
class NoZeroSMulDivisors (R M : Type*) [Zero R] [Zero M] [SMul R M] : Prop where
  /-- If scalar multiplication yields zero, either the scalar or the vector was zero. -/
  eq_zero_or_eq_zero_of_smul_eq_zero : ∀ {c : R} {x : M}, c • x = 0 → c = 0 ∨ x = 0

export NoZeroSMulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

/-- Pullback a `NoZeroSMulDivisors` instance along an injective function. -/
theorem Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Zero N]
    [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M → N) (hf : Function.Injective f)
    (h0 : f 0 = 0) (hs : ∀ (c : R) (x : M), f (c • x) = c • f x) : NoZeroSMulDivisors R M :=
  ⟨fun {_ _} h =>
    Or.imp_right (@hf _ _) <| h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

-- See note [lower instance priority]
instance (priority := 100) NoZeroDivisors.toNoZeroSMulDivisors [Zero R] [Mul R]
    [NoZeroDivisors R] : NoZeroSMulDivisors R R :=
  ⟨fun {_ _} => eq_zero_or_eq_zero_of_mul_eq_zero⟩

theorem smul_ne_zero [Zero R] [Zero M] [SMul R M] [NoZeroSMulDivisors R M] {c : R} {x : M}
    (hc : c ≠ 0) (hx : x ≠ 0) : c • x ≠ 0 := fun h =>
  (eq_zero_or_eq_zero_of_smul_eq_zero h).elim hc hx

section SMulWithZero

variable [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] {c : R} {x : M}

@[simp]
theorem smul_eq_zero : c • x = 0 ↔ c = 0 ∨ x = 0 :=
  ⟨eq_zero_or_eq_zero_of_smul_eq_zero, fun h =>
    h.elim (fun h => h.symm ▸ zero_smul R x) fun h => h.symm ▸ smul_zero c⟩

theorem smul_ne_zero_iff : c • x ≠ 0 ↔ c ≠ 0 ∧ x ≠ 0 := by rw [Ne, smul_eq_zero, not_or]

lemma smul_eq_zero_iff_left (hx : x ≠ 0) : c • x = 0 ↔ c = 0 := by simp [hx]
lemma smul_eq_zero_iff_right (hc : c ≠ 0) : c • x = 0 ↔ x = 0 := by simp [hc]
lemma smul_ne_zero_iff_left (hx : x ≠ 0) : c • x ≠ 0 ↔ c ≠ 0 := by simp [hx]
lemma smul_ne_zero_iff_right (hc : c ≠ 0) : c • x ≠ 0 ↔ x ≠ 0 := by simp [hc]

end SMulWithZero

section Module

section Nat

theorem Nat.noZeroSMulDivisors
    (R) (M) [Semiring R] [CharZero R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M] :
    NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} := by rw [← Nat.cast_smul_eq_nsmul R, smul_eq_zero]; simp

theorem two_nsmul_eq_zero
    (R) (M) [Semiring R] [CharZero R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M]
    {v : M} : 2 • v = 0 ↔ v = 0 := by
  haveI := Nat.noZeroSMulDivisors R M
  simp [smul_eq_zero]

end Nat

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (R M)

/-- If `M` is an `R`-module with one and `M` has characteristic zero, then `R` has characteristic
zero as well. Usually `M` is an `R`-algebra. -/
theorem CharZero.of_module (M) [AddCommMonoidWithOne M] [CharZero M] [Module R M] : CharZero R := by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one, ← nsmul_one, ← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, h]

end Module

section AddCommGroup

-- `R` can still be a semiring here
variable [Semiring R] [AddCommGroup M] [Module R M]

section SMulInjective

variable (M)

theorem smul_right_injective [NoZeroSMulDivisors R M] {c : R} (hc : c ≠ 0) :
    Function.Injective (c • · : M → M) :=
  (injective_iff_map_eq_zero (smulAddHom R M c)).2 fun _ ha => (smul_eq_zero.mp ha).resolve_left hc

variable {M}

theorem smul_right_inj [NoZeroSMulDivisors R M] {c : R} (hc : c ≠ 0) {x y : M} :
    c • x = c • y ↔ x = y :=
  (smul_right_injective M hc).eq_iff

end SMulInjective

section Nat

theorem self_eq_neg
    (R) (M) [Semiring R] [CharZero R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    {v : M} : v = -v ↔ v = 0 := by
  rw [← two_nsmul_eq_zero R M, two_smul, add_eq_zero_iff_eq_neg]

theorem neg_eq_self
    (R) (M) [Semiring R] [CharZero R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    {v : M} : -v = v ↔ v = 0 := by
  rw [eq_comm, self_eq_neg R M]

theorem self_ne_neg
    (R) (M) [Semiring R] [CharZero R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    {v : M} : v ≠ -v ↔ v ≠ 0 :=
  (self_eq_neg R M).not

theorem neg_ne_self
    (R) (M) [Semiring R] [CharZero R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    {v : M} : -v ≠ v ↔ v ≠ 0 :=
  (neg_eq_self R M).not

end Nat

end AddCommGroup

section Module

variable [Ring R] [AddCommGroup M] [Module R M]

section SMulInjective

variable (R)
variable [NoZeroSMulDivisors R M]

theorem smul_left_injective {x : M} (hx : x ≠ 0) : Function.Injective fun c : R => c • x :=
  fun c d h =>
  sub_eq_zero.mp
    ((smul_eq_zero.mp
          (calc
            (c - d) • x = c • x - d • x := sub_smul c d x
            _ = 0 := sub_eq_zero.mpr h
            )).resolve_right
      hx)

end SMulInjective

instance [NoZeroSMulDivisors ℤ M] : NoZeroSMulDivisors ℕ M :=
  ⟨fun {c x} hcx ↦ by rwa [← Nat.cast_smul_eq_nsmul ℤ, smul_eq_zero, Nat.cast_eq_zero] at hcx⟩

variable (R M)

theorem NoZeroSMulDivisors.int_of_charZero
    (R) (M) [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] [CharZero R] :
    NoZeroSMulDivisors ℤ M :=
  ⟨fun {z x} h ↦ by simpa [← smul_one_smul R z x] using h⟩

/-- Only a ring of characteristic zero can can have a non-trivial module without additive or
scalar torsion. -/
theorem CharZero.of_noZeroSMulDivisors [Nontrivial M] [NoZeroSMulDivisors ℤ M] : CharZero R := by
  refine ⟨fun {n m h} ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : ℤ) • x = (m : ℤ) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective ℤ hx h

end Module

end NoZeroSMulDivisors

-- Porting note (#10618): simp can prove this
--@[simp]
theorem Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring R] (m : ℕ) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul, mul_one]

-- Porting note (#10618): simp can prove this
--@[simp]
theorem Int.smul_one_eq_cast {R : Type*} [NonAssocRing R] (m : ℤ) : m • (1 : R) = ↑m := by
  rw [zsmul_eq_mul, mul_one]

@[deprecated (since := "2024-05-03")] alias Nat.smul_one_eq_coe := Nat.smul_one_eq_cast
@[deprecated (since := "2024-05-03")] alias Int.smul_one_eq_coe := Int.smul_one_eq_cast
