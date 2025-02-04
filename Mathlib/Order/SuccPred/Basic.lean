/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Cover
import Mathlib.Order.GaloisConnection
import Mathlib.Order.Iterate
import Mathlib.Order.WellFounded

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `Fin n`, but also `ENat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `SuccOrder`: Order equipped with a sensible successor function.
* `PredOrder`: Order equipped with a sensible predecessor function.
* `IsSuccArchimedean`: `SuccOrder` where `succ` iterated to an element gives all the greater
  ones.
* `IsPredArchimedean`: `PredOrder` where `pred` iterated to an element gives all the smaller
  ones.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class NaiveSuccOrder (α : Type*) [Preorder α] :=
  (succ : α → α)
  (succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
  (lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `OrderTop` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`max_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `SuccOrder α` and `NoMaxOrder α`.
-/

open Function OrderDual Set

variable {α β : Type*}

/-- Order equipped with a sensible successor function. -/
@[ext]
class SuccOrder (α : Type*) [Preorder α] where
  /-- Successor function-/
  succ : α → α
  /-- Proof of basic ordering with respect to `succ`-/
  le_succ : ∀ a, a ≤ succ a
  /-- Proof of interaction between `succ` and maximal element-/
  max_of_succ_le {a} : succ a ≤ a → IsMax a
  /-- Proof that `succ` satisfies ordering invariants between `LT` and `LE`-/
  succ_le_of_lt {a b} : a < b → succ a ≤ b
  /-- Proof that `succ` satisfies ordering invariants between `LE` and `LT`-/
  le_of_lt_succ {a b} : a < succ b → a ≤ b

/-- Order equipped with a sensible predecessor function. -/
@[ext]
class PredOrder (α : Type*) [Preorder α] where
  /-- Predecessor function-/
  pred : α → α
  /-- Proof of basic ordering with respect to `pred`-/
  pred_le : ∀ a, pred a ≤ a
  /-- Proof of interaction between `pred` and minimal element-/
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  /-- Proof that `pred` satisfies ordering invariants between `LT` and `LE`-/
  le_pred_of_lt {a b} : a < b → a ≤ pred b
  /-- Proof that `pred` satisfies ordering invariants between `LE` and `LT`-/
  le_of_pred_lt {a b} : pred a < b → a ≤ b

instance [Preorder α] [SuccOrder α] :
    PredOrder αᵒᵈ where
  pred := toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := by
    simp only [comp, OrderDual.forall, ofDual_toDual, toDual_le_toDual,
     SuccOrder.le_succ, implies_true]
  min_of_le_pred h := by apply SuccOrder.max_of_succ_le h
  le_pred_of_lt := by intro a b h; exact SuccOrder.succ_le_of_lt h
  le_of_pred_lt := SuccOrder.le_of_lt_succ

instance [Preorder α] [PredOrder α] :
    SuccOrder αᵒᵈ where
  succ := toDual ∘ PredOrder.pred ∘ ofDual
  le_succ := by
    simp only [comp, OrderDual.forall, ofDual_toDual, toDual_le_toDual,
     PredOrder.pred_le, implies_true]
  max_of_succ_le h := by apply PredOrder.min_of_le_pred h
  succ_le_of_lt := by intro a b h; exact PredOrder.le_pred_of_lt h
  le_of_lt_succ := PredOrder.le_of_pred_lt

section Preorder

variable [Preorder α]

/-- A constructor for `SuccOrder α` usable when `α` has no maximal element. -/
def SuccOrder.ofSuccLeIffOfLeLtSucc (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
    (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) : SuccOrder α :=
  { succ
    le_succ := fun _ => (hsucc_le_iff.1 le_rfl).le
    max_of_succ_le := fun ha => (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
    succ_le_of_lt := fun h => hsucc_le_iff.2 h
    le_of_lt_succ := fun h => hle_of_lt_succ h}

/-- A constructor for `PredOrder α` usable when `α` has no minimal element. -/
def PredOrder.ofLePredIffOfPredLePred (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b)
    (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) : PredOrder α :=
  { pred
    pred_le := fun _ => (hle_pred_iff.1 le_rfl).le
    min_of_le_pred := fun ha => (lt_irrefl _ <| hle_pred_iff.1 ha).elim
    le_pred_of_lt := fun h => hle_pred_iff.2 h
    le_of_pred_lt := fun h => hle_of_pred_lt h }

end Preorder

section LinearOrder

variable [LinearOrder α]

/-- A constructor for `SuccOrder α` for `α` a linear order. -/
@[simps]
def SuccOrder.ofCore (succ : α → α) (hn : ∀ {a}, ¬IsMax a → ∀ b, a < b ↔ succ a ≤ b)
    (hm : ∀ a, IsMax a → succ a = a) : SuccOrder α :=
  { succ
    succ_le_of_lt := fun {a b} =>
      by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp
    le_succ := fun a =>
      by_cases (fun h => (hm a h).symm.le) fun h => le_of_lt <| by simpa using (hn h a).not
    le_of_lt_succ := fun {a b} hab =>
      by_cases (fun h => hm b h ▸ hab.le) fun h => by simpa [hab] using (hn h a).not
    max_of_succ_le := fun {a} => not_imp_not.mp fun h => by simpa using (hn h a).not }

/-- A constructor for `PredOrder α` for `α` a linear order. -/
@[simps]
def PredOrder.ofCore {α} [LinearOrder α] (pred : α → α)
    (hn : ∀ {a}, ¬IsMin a → ∀ b, b ≤ pred a ↔ b < a) (hm : ∀ a, IsMin a → pred a = a) :
    PredOrder α :=
  { pred
    le_pred_of_lt := fun {a b} =>
      by_cases (fun h hab => (hm b h).symm ▸ hab.le) fun h => (hn h a).mpr
    pred_le := fun a =>
      by_cases (fun h => (hm a h).le) fun h => le_of_lt <| by simpa using (hn h a).not
    le_of_pred_lt := fun {a b} hab =>
      by_cases (fun h => hm a h ▸ hab.le) fun h => by simpa [hab] using (hn h b).not
    min_of_le_pred := fun {a} => not_imp_not.mp fun h => by simpa using (hn h a).not }

/-- A constructor for `SuccOrder α` usable when `α` is a linear order with no maximal element. -/
def SuccOrder.ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
    SuccOrder α :=
  { succ
    le_succ := fun _ => (hsucc_le_iff.1 le_rfl).le
    max_of_succ_le := fun ha => (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
    succ_le_of_lt := fun h => hsucc_le_iff.2 h
    le_of_lt_succ := fun {_ _} h => le_of_not_lt ((not_congr hsucc_le_iff).1 h.not_le) }

/-- A constructor for `PredOrder α` usable when `α` is a linear order with no minimal element. -/
def PredOrder.ofLePredIff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
    PredOrder α :=
  { pred
    pred_le := fun _ => (hle_pred_iff.1 le_rfl).le
    min_of_le_pred := fun ha => (lt_irrefl _ <| hle_pred_iff.1 ha).elim
    le_pred_of_lt := fun h => hle_pred_iff.2 h
    le_of_pred_lt := fun {_ _} h => le_of_not_lt ((not_congr hle_pred_iff).1 h.not_le) }

variable (α)

open Classical in
/-- A well-order is a `SuccOrder`. -/
noncomputable def SuccOrder.ofLinearWellFoundedLT [WellFoundedLT α] : SuccOrder α :=
  ofCore (fun a ↦ if h : (Ioi a).Nonempty then wellFounded_lt.min _ h else a)
    (fun ha _ ↦ by
      rw [not_isMax_iff] at ha
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos ha]
      exact ⟨(wellFounded_lt.min_le · ha), lt_of_lt_of_le (wellFounded_lt.min_mem _ ha)⟩)
    fun a ha ↦ dif_neg (not_not_intro ha <| not_isMax_iff.mpr ·)

/-- A linear order with well-founded greater-than relation is a `PredOrder`. -/
noncomputable def PredOrder.ofLinearWellFoundedGT (α) [LinearOrder α] [WellFoundedGT α] :
    PredOrder α := letI := SuccOrder.ofLinearWellFoundedLT αᵒᵈ; inferInstanceAs (PredOrder αᵒᵈᵒᵈ)

end LinearOrder

/-! ### Successor order -/


namespace Order

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
def succ : α → α :=
  SuccOrder.succ

theorem le_succ : ∀ a : α, a ≤ succ a :=
  SuccOrder.le_succ

theorem max_of_succ_le {a : α} : succ a ≤ a → IsMax a :=
  SuccOrder.max_of_succ_le

theorem succ_le_of_lt {a b : α} : a < b → succ a ≤ b :=
  SuccOrder.succ_le_of_lt

alias _root_.LT.lt.succ_le := succ_le_of_lt

theorem le_of_lt_succ {a b : α} : a < succ b → a ≤ b :=
  SuccOrder.le_of_lt_succ

@[simp]
theorem succ_le_iff_isMax : succ a ≤ a ↔ IsMax a :=
  ⟨max_of_succ_le, fun h => h <| le_succ _⟩

alias ⟨_root_.IsMax.of_succ_le, _root_.IsMax.succ_le⟩ := succ_le_iff_isMax

@[simp]
theorem lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a :=
  ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_le fun h => ha <| max_of_succ_le h⟩

alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax

theorem wcovBy_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_lt⟩

theorem covBy_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a :=
  (wcovBy_succ a).covBy_of_lt <| lt_succ_of_not_isMax h

theorem lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b ≤ a :=
  ⟨le_of_lt_succ, fun h => h.trans_lt <| lt_succ_of_not_isMax ha⟩

theorem succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩

lemma succ_lt_succ_of_not_isMax (h : a < b) (hb : ¬ IsMax b) : succ a < succ b :=
  (lt_succ_iff_of_not_isMax hb).2 <| succ_le_of_lt h

theorem succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a < succ b ↔ a < b := by
  rw [lt_succ_iff_of_not_isMax hb, succ_le_iff_of_not_isMax ha]

theorem succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a ≤ succ b ↔ a ≤ b := by
  rw [succ_le_iff_of_not_isMax ha, lt_succ_iff_of_not_isMax hb]

@[simp, mono]
theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := by
  by_cases hb : IsMax b
  · by_cases hba : b ≤ a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_le hba).trans_le <| le_succ b)
  · rwa [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h, lt_succ_iff_of_not_isMax hb]

theorem succ_mono : Monotone (succ : α → α) := fun _ _ => succ_le_succ

/-- See also `Order.succ_eq_of_covBy`. -/
lemma le_succ_of_wcovBy (h : a ⩿ b) : b ≤ succ a := by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
    exact h.2 (lt_succ_of_not_isMax hab.lt.not_isMax) <| hab.lt.succ_le.lt_of_not_le hba
  · exact hba.trans (le_succ _)

alias _root_.WCovBy.le_succ := le_succ_of_wcovBy

theorem le_succ_iterate (k : ℕ) (x : α) : x ≤ succ^[k] x := by
  conv_lhs => rw [(by simp only [Function.iterate_id, id] : x = id^[k] x)]
  exact Monotone.le_iterate_of_le succ_mono le_succ k x

theorem isMax_iterate_succ_of_eq_of_lt {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_lt : n < m) : IsMax (succ^[n] a) := by
  refine max_of_succ_le (le_trans ?_ h_eq.symm.le)
  have : succ (succ^[n] a) = succ^[n + 1] a := by rw [Function.iterate_succ', comp]
  rw [this]
  have h_le : n + 1 ≤ m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le

theorem isMax_iterate_succ_of_eq_of_ne {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_ne : n ≠ m) : IsMax (succ^[n] a) := by
  rcases le_total n m with h | h
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)

theorem Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun _ => lt_succ_iff_of_not_isMax ha

theorem Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun _ => succ_le_iff_of_not_isMax ha

theorem Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio, Iio_succ_of_not_isMax hb, Ici_inter_Iic]

theorem Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio, Iio_succ_of_not_isMax hb, Ioi_inter_Iic]

theorem Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic, Ici_succ_of_not_isMax ha, Ioi_inter_Iic]

theorem Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio, Ici_succ_of_not_isMax ha, Ioi_inter_Iio]

section NoMaxOrder

variable [NoMaxOrder α]

theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_isMax <| not_isMax a

@[simp]
theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_isMax <| not_isMax b

@[simp]
theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_isMax <| not_isMax a

theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by simp

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp

alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff

alias ⟨lt_of_succ_lt_succ, succ_lt_succ⟩ := succ_lt_succ_iff

theorem succ_strictMono : StrictMono (succ : α → α) := fun _ _ => succ_lt_succ

theorem covBy_succ (a : α) : a ⋖ succ a :=
  covBy_succ_of_not_isMax <| not_isMax a

@[simp]
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
  Iio_succ_of_not_isMax <| not_isMax _

@[simp]
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
  Ici_succ_of_not_isMax <| not_isMax _

@[simp]
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_of_not_isMax <| not_isMax _

@[simp]
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_of_not_isMax <| not_isMax _

@[simp]
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_of_not_isMax <| not_isMax _

@[simp]
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
  Ico_succ_left_of_not_isMax <| not_isMax _

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α}

@[simp]
theorem succ_eq_iff_isMax : succ a = a ↔ IsMax a :=
  ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge <| le_succ _⟩

alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax

theorem succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a = succ b ↔ a = b := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, succ_le_succ_iff_of_not_isMax ha hb,
    succ_lt_succ_iff_of_not_isMax ha hb]

theorem le_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a := by
  refine
    ⟨fun h =>
      or_iff_not_imp_left.2 fun hba : b ≠ a =>
        h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm),
      ?_⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩

/-- See also `Order.le_succ_of_wcovBy`. -/
lemma succ_eq_of_covBy (h : a ⋖ b) : succ a = b := (succ_le_of_lt h.lt).antisymm h.wcovBy.le_succ

alias _root_.CovBy.succ_eq := succ_eq_of_covBy

theorem le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b := by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]

theorem lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt

theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le

theorem Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

theorem Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h

theorem Ico_succ_right_eq_insert_of_not_isMax (h₁ : a ≤ b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

theorem Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)

theorem succ_injective : Injective (succ : α → α) := fun _ _ => succ_eq_succ_iff.1

theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff

alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff

theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt

theorem succ_eq_iff_covBy : succ a = b ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact covBy_succ _, CovBy.succ_eq⟩

theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
  Iio_succ_eq_insert_of_not_isMax <| not_isMax a

theorem Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
  Ico_succ_right_eq_insert_of_not_isMax h <| not_isMax b

theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
  Ioo_succ_right_eq_insert_of_not_isMax h <| not_isMax b

end NoMaxOrder

section OrderTop

variable [OrderTop α]

@[simp]
theorem succ_top : succ (⊤ : α) = ⊤ := by
  rw [succ_eq_iff_isMax, isMax_iff_eq_top]

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ :=
  succ_le_iff_isMax.trans isMax_iff_eq_top

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
  lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α]

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥ := by rw [lt_succ_iff, le_bot_iff]

theorem le_succ_bot_iff : a ≤ succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ := by
  rw [le_succ_iff_eq_or_le, le_bot_iff, or_comm]

variable [Nontrivial α]

theorem bot_lt_succ (a : α) : ⊥ < succ a :=
  (lt_succ_of_not_isMax not_isMax_bot).trans_le <| succ_mono bot_le

theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'

end OrderBot

end PartialOrder

/-- There is at most one way to define the successors in a `PartialOrder`. -/
instance [PartialOrder α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @CovBy.succ_eq _ _ h₀ _ _ (covBy_succ_of_not_isMax ha)⟩

theorem succ_eq_sInf [CompleteLattice α] [SuccOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_sInf fun b => succ_le_of_lt).antisymm
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  · exact sInf_le (lt_succ_iff_ne_top.2 ha)

theorem succ_eq_iInf [CompleteLattice α] [SuccOrder α] (a : α) : succ a = ⨅ b > a, b := by
  rw [succ_eq_sInf, iInf_subtype', iInf, Subtype.range_coe_subtype]
  rfl

theorem succ_eq_csInf [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_csInf nonempty_Ioi fun b => succ_le_of_lt).antisymm
  exact csInf_le ⟨a, fun b => le_of_lt⟩ <| lt_succ a

/-! ### Predecessor order -/

section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

/-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest element less
than `a`. If `a` is minimal, then `pred a = a`. -/
def pred : α → α :=
  PredOrder.pred

theorem pred_le : ∀ a : α, pred a ≤ a :=
  PredOrder.pred_le

theorem min_of_le_pred {a : α} : a ≤ pred a → IsMin a :=
  PredOrder.min_of_le_pred

theorem le_pred_of_lt {a b : α} : a < b → a ≤ pred b :=
  PredOrder.le_pred_of_lt

alias _root_.LT.lt.le_pred := le_pred_of_lt

theorem le_of_pred_lt {a b : α} : pred a < b → a ≤ b :=
  PredOrder.le_of_pred_lt

@[simp]
theorem le_pred_iff_isMin : a ≤ pred a ↔ IsMin a :=
  ⟨min_of_le_pred, fun h => h <| pred_le _⟩

alias ⟨_root_.IsMin.of_le_pred, _root_.IsMin.le_pred⟩ := le_pred_iff_isMin

@[simp]
theorem pred_lt_iff_not_isMin : pred a < a ↔ ¬IsMin a :=
  ⟨not_isMin_of_lt, fun ha => (pred_le a).lt_of_not_le fun h => ha <| min_of_le_pred h⟩

alias ⟨_, pred_lt_of_not_isMin⟩ := pred_lt_iff_not_isMin

theorem pred_wcovBy (a : α) : pred a ⩿ a :=
  ⟨pred_le a, fun _ hb => (le_of_pred_lt hb).not_lt⟩

theorem pred_covBy_of_not_isMin (h : ¬IsMin a) : pred a ⋖ a :=
  (pred_wcovBy a).covBy_of_lt <| pred_lt_of_not_isMin h

theorem pred_lt_iff_of_not_isMin (ha : ¬IsMin a) : pred a < b ↔ a ≤ b :=
  ⟨le_of_pred_lt, (pred_lt_of_not_isMin ha).trans_le⟩

theorem le_pred_iff_of_not_isMin (ha : ¬IsMin a) : b ≤ pred a ↔ b < a :=
  ⟨fun h => h.trans_lt <| pred_lt_of_not_isMin ha, le_pred_of_lt⟩

lemma pred_lt_pred_of_not_isMin (h : a < b) (ha : ¬ IsMin a) : pred a < pred b :=
  (pred_lt_iff_of_not_isMin ha).2 <| le_pred_of_lt h

theorem pred_lt_pred_iff_of_not_isMin (ha : ¬IsMin a) (hb : ¬IsMin b) :
    pred a < pred b ↔ a < b := by
  rw [pred_lt_iff_of_not_isMin ha, le_pred_iff_of_not_isMin hb]

theorem pred_le_pred_iff_of_not_isMin (ha : ¬IsMin a) (hb : ¬IsMin b) :
    pred a ≤ pred b ↔ a ≤ b := by
  rw [le_pred_iff_of_not_isMin hb, pred_lt_iff_of_not_isMin ha]

@[simp, mono]
theorem pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b :=
  succ_le_succ h.dual

theorem pred_mono : Monotone (pred : α → α) := fun _ _ => pred_le_pred

/-- See also `Order.pred_eq_of_covBy`. -/
lemma pred_le_of_wcovBy (h : a ⩿ b) : pred b ≤ a := by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
    exact h.2 (hab.lt.le_pred.lt_of_not_le hba) (pred_lt_of_not_isMin hab.lt.not_isMin)
  · exact (pred_le _).trans hba

alias _root_.WCovBy.pred_le := pred_le_of_wcovBy

theorem pred_iterate_le (k : ℕ) (x : α) : pred^[k] x ≤ x := by
  conv_rhs => rw [(by simp only [Function.iterate_id, id] : x = id^[k] x)]
  exact Monotone.iterate_le_of_le pred_mono pred_le k x

theorem isMin_iterate_pred_of_eq_of_lt {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_lt : n < m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

theorem isMin_iterate_pred_of_eq_of_ne {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_ne : n ≠ m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

theorem Ioi_pred_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = Ici a :=
  Set.ext fun _ => pred_lt_iff_of_not_isMin ha

theorem Iic_pred_of_not_isMin (ha : ¬IsMin a) : Iic (pred a) = Iio a :=
  Set.ext fun _ => le_pred_iff_of_not_isMin ha

theorem Ioc_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioc (pred a) b = Icc a b := by
  rw [← Ioi_inter_Iic, Ioi_pred_of_not_isMin ha, Ici_inter_Iic]

theorem Ioo_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioo (pred a) b = Ico a b := by
  rw [← Ioi_inter_Iio, Ioi_pred_of_not_isMin ha, Ici_inter_Iio]

theorem Icc_pred_right_of_not_isMin (ha : ¬IsMin b) : Icc a (pred b) = Ico a b := by
  rw [← Ici_inter_Iic, Iic_pred_of_not_isMin ha, Ici_inter_Iio]

theorem Ioc_pred_right_of_not_isMin (ha : ¬IsMin b) : Ioc a (pred b) = Ioo a b := by
  rw [← Ioi_inter_Iic, Iic_pred_of_not_isMin ha, Ioi_inter_Iio]

section NoMinOrder

variable [NoMinOrder α]

theorem pred_lt (a : α) : pred a < a :=
  pred_lt_of_not_isMin <| not_isMin a

@[simp]
theorem pred_lt_iff : pred a < b ↔ a ≤ b :=
  pred_lt_iff_of_not_isMin <| not_isMin a

@[simp]
theorem le_pred_iff : a ≤ pred b ↔ a < b :=
  le_pred_iff_of_not_isMin <| not_isMin b

theorem pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b := by simp

theorem pred_lt_pred_iff : pred a < pred b ↔ a < b := by simp

alias ⟨le_of_pred_le_pred, _⟩ := pred_le_pred_iff

alias ⟨lt_of_pred_lt_pred, pred_lt_pred⟩ := pred_lt_pred_iff

theorem pred_strictMono : StrictMono (pred : α → α) := fun _ _ => pred_lt_pred

theorem pred_covBy (a : α) : pred a ⋖ a :=
  pred_covBy_of_not_isMin <| not_isMin a

@[simp]
theorem Ioi_pred (a : α) : Ioi (pred a) = Ici a :=
  Ioi_pred_of_not_isMin <| not_isMin a

@[simp]
theorem Iic_pred (a : α) : Iic (pred a) = Iio a :=
  Iic_pred_of_not_isMin <| not_isMin a

@[simp]
theorem Ioc_pred_left (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_of_not_isMin <| not_isMin _

@[simp]
theorem Ioo_pred_left (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_of_not_isMin <| not_isMin _

@[simp]
theorem Icc_pred_right (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_of_not_isMin <| not_isMin _

@[simp]
theorem Ioc_pred_right (a b : α) : Ioc a (pred b) = Ioo a b :=
  Ioc_pred_right_of_not_isMin <| not_isMin _

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α}

@[simp]
theorem pred_eq_iff_isMin : pred a = a ↔ IsMin a :=
  ⟨fun h => min_of_le_pred h.ge, fun h => h.eq_of_le <| pred_le _⟩

alias ⟨_, _root_.IsMin.pred_eq⟩ := pred_eq_iff_isMin

theorem pred_eq_pred_iff_of_not_isMin (ha : ¬IsMin a) (hb : ¬IsMin b) :
    pred a = pred b ↔ a = b := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, pred_le_pred_iff_of_not_isMin ha hb,
    pred_lt_pred_iff_of_not_isMin ha hb]

theorem pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a := by
  refine
    ⟨fun h =>
      or_iff_not_imp_left.2 fun hba : b ≠ a => (le_pred_of_lt <| h.2.lt_of_ne hba).antisymm h.1, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨pred_le b, le_rfl⟩
  · exact ⟨le_rfl, pred_le a⟩

/-- See also `Order.pred_le_of_wcovBy`. -/
lemma pred_eq_of_covBy (h : a ⋖ b) : pred b = a := h.wcovBy.pred_le.antisymm (le_pred_of_lt h.lt)

alias _root_.CovBy.pred_eq := pred_eq_of_covBy

theorem pred_le_iff_eq_or_le : pred a ≤ b ↔ b = pred a ∨ a ≤ b := by
  by_cases ha : IsMin a
  · rw [ha.pred_eq, or_iff_right_of_imp ge_of_eq]
  · rw [← pred_lt_iff_of_not_isMin ha, le_iff_eq_or_lt, eq_comm]

theorem pred_lt_iff_eq_or_lt_of_not_isMin (ha : ¬IsMin a) : pred a < b ↔ a = b ∨ a < b :=
  (pred_lt_iff_of_not_isMin ha).trans le_iff_eq_or_lt

theorem Ici_pred (a : α) : Ici (pred a) = insert (pred a) (Ici a) :=
  ext fun _ => pred_le_iff_eq_or_le

theorem Ioi_pred_eq_insert_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = insert a (Ioi a) := by
  ext x; simp only [insert, mem_setOf, @eq_comm _ x a, mem_Ioi, Set.insert]
  exact pred_lt_iff_eq_or_lt_of_not_isMin ha

theorem Icc_pred_left (h : pred a ≤ b) : Icc (pred a) b = insert (pred a) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Ici_pred, insert_inter_of_mem (mem_Iic.2 h)]

theorem Ico_pred_left (h : pred a < b) : Ico (pred a) b = insert (pred a) (Ico a b) := by
  simp_rw [← Ici_inter_Iio, Ici_pred, insert_inter_of_mem (mem_Iio.2 h)]

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem pred_eq_pred_iff : pred a = pred b ↔ a = b := by
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff]

theorem pred_injective : Injective (pred : α → α) := fun _ _ => pred_eq_pred_iff.1

theorem pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b :=
  pred_injective.ne_iff

alias ⟨_, pred_ne_pred⟩ := pred_ne_pred_iff

theorem pred_lt_iff_eq_or_lt : pred a < b ↔ a = b ∨ a < b :=
  pred_lt_iff.trans le_iff_eq_or_lt

theorem pred_eq_iff_covBy : pred b = a ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact pred_covBy _, CovBy.pred_eq⟩

theorem Ioi_pred_eq_insert (a : α) : Ioi (pred a) = insert a (Ioi a) :=
  ext fun _ => pred_lt_iff_eq_or_lt.trans <| or_congr_left eq_comm

theorem Ico_pred_right_eq_insert (h : a ≤ b) : Ioc (pred a) b = insert a (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iic.2 h)]

theorem Ioo_pred_right_eq_insert (h : a < b) : Ioo (pred a) b = insert a (Ioo a b) := by
  simp_rw [← Ioi_inter_Iio, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iio.2 h)]

end NoMinOrder

section OrderBot

variable [OrderBot α]

@[simp]
theorem pred_bot : pred (⊥ : α) = ⊥ :=
  isMin_bot.pred_eq

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem le_pred_iff_eq_bot : a ≤ pred a ↔ a = ⊥ :=
  @succ_le_iff_eq_top αᵒᵈ _ _ _ _

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem pred_lt_iff_ne_bot : pred a < a ↔ a ≠ ⊥ :=
  @lt_succ_iff_ne_top αᵒᵈ _ _ _ _

end OrderBot

section OrderTop

variable [OrderTop α]

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem pred_top_lt_iff [NoMinOrder α] : pred ⊤ < a ↔ a = ⊤ :=
  @lt_succ_bot_iff αᵒᵈ _ _ _ _ _

theorem pred_top_le_iff : pred ⊤ ≤ a ↔ a = ⊤ ∨ a = pred ⊤ :=
  @le_succ_bot_iff αᵒᵈ _ _ _ _

variable [Nontrivial α]

theorem pred_lt_top (a : α) : pred a < ⊤ :=
  (pred_mono le_top).trans_lt <| pred_lt_of_not_isMin not_isMin_top

theorem pred_ne_top (a : α) : pred a ≠ ⊤ :=
  (pred_lt_top a).ne

end OrderTop

end PartialOrder

/-- There is at most one way to define the predecessors in a `PartialOrder`. -/
instance [PartialOrder α] : Subsingleton (PredOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMin a
    · exact (@IsMin.pred_eq _ _ h₀ _ ha).trans ha.pred_eq.symm
    · exact @CovBy.pred_eq _ _ h₀ _ _ (pred_covBy_of_not_isMin ha)⟩

theorem pred_eq_sSup [CompleteLattice α] [PredOrder α] :
    ∀ a : α, pred a = sSup (Set.Iio a) :=
  succ_eq_sInf (α := αᵒᵈ)

theorem pred_eq_iSup [CompleteLattice α] [PredOrder α] (a : α) : pred a = ⨆ b < a, b :=
  succ_eq_iInf (α := αᵒᵈ) a

theorem pred_eq_csSup [ConditionallyCompleteLattice α] [PredOrder α] [NoMinOrder α] (a : α) :
    pred a = sSup (Set.Iio a) :=
  succ_eq_csInf (α := αᵒᵈ) a

/-! ### Successor-predecessor orders -/

section SuccPredOrder
section Preorder
variable [Preorder α] [SuccOrder α] [PredOrder α] {a b : α}

lemma le_succ_pred (a : α) : a ≤ succ (pred a) := (pred_wcovBy _).le_succ
lemma pred_succ_le (a : α) : pred (succ a) ≤ a := (wcovBy_succ _).pred_le

lemma pred_le_iff_le_succ : pred a ≤ b ↔ a ≤ succ b where
  mp hab := (le_succ_pred _).trans (succ_mono hab)
  mpr hab := (pred_mono hab).trans (pred_succ_le _)

lemma gc_pred_succ : GaloisConnection (pred : α → α) succ := fun _ _ ↦ pred_le_iff_le_succ

end Preorder

variable [PartialOrder α] [SuccOrder α] [PredOrder α] {a b : α}

@[simp]
theorem succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy_of_not_isMin h)

@[simp]
theorem pred_succ_of_not_isMax (h : ¬IsMax a) : pred (succ a) = a :=
  CovBy.pred_eq (covBy_succ_of_not_isMax h)

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy _)

-- Porting note (#10618): removing @[simp],`simp` can prove it
theorem pred_succ [NoMaxOrder α] (a : α) : pred (succ a) = a :=
  CovBy.pred_eq (covBy_succ _)

theorem pred_succ_iterate_of_not_isMax (i : α) (n : ℕ) (hin : ¬IsMax (succ^[n - 1] i)) :
    pred^[n] (succ^[n] i) = i := by
  induction' n with n hn
  · simp only [Function.iterate_zero, id]
  rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hin
  have h_not_max : ¬IsMax (succ^[n - 1] i) := by
    cases' n with n
    · simpa using hin
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hn ⊢
    have h_sub_le : succ^[n] i ≤ succ^[n.succ] i := by
      rw [Function.iterate_succ']
      exact le_succ _
    refine fun h_max => hin fun j hj => ?_
    have hj_le : j ≤ succ^[n] i := h_max (h_sub_le.trans hj)
    exact hj_le.trans h_sub_le
  rw [Function.iterate_succ, Function.iterate_succ']
  simp only [Function.comp_apply]
  rw [pred_succ_of_not_isMax hin]
  exact hn h_not_max

theorem succ_pred_iterate_of_not_isMin (i : α) (n : ℕ) (hin : ¬IsMin (pred^[n - 1] i)) :
    succ^[n] (pred^[n] i) = i :=
  @pred_succ_iterate_of_not_isMax αᵒᵈ _ _ _ i n hin

end SuccPredOrder

end Order

open Order

/-! ### `WithBot`, `WithTop`
Adding a greatest/least element to a `SuccOrder` or to a `PredOrder`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `OrderTop`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `NoMaxOrder`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `OrderBot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `NoMinOrder`: Preserves `pred`. Never preserves `succ`.
where "preserves `(succ/pred)`" means
`(Succ/Pred)Order α → (Succ/Pred)Order ((WithTop/WithBot) α)`.
-/

namespace WithTop

/-! #### Adding a `⊤` to an `OrderTop` -/

section Succ

variable [DecidableEq α] [PartialOrder α] [OrderTop α] [SuccOrder α]

instance : SuccOrder (WithTop α) where
  succ a :=
    match a with
    | ⊤ => ⊤
    | Option.some a => ite (a = ⊤) ⊤ (some (succ a))
  le_succ a := by
    cases' a with a a
    · exact le_top
    change _ ≤ ite _ _ _
    split_ifs
    · exact le_top
    · exact coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
    dsimp only at ha
    split_ifs at ha with ha'
    · exact (not_top_le_coe _ ha).elim
    · rw [coe_le_coe, succ_le_iff_eq_top] at ha
      exact (ha' ha).elim
  succ_le_of_lt {a b} h := by
    cases b
    · exact le_top
    cases a
    · exact (not_top_lt h).elim
    rw [coe_lt_coe] at h
    change ite _ _ _ ≤ _
    split_ifs with ha
    · rw [ha] at h
      exact (not_top_lt h).elim
    · exact coe_le_coe.2 (succ_le_of_lt h)
  le_of_lt_succ {a b} h := by
    cases a
    · exact (not_top_lt h).elim
    cases b
    · exact le_top
    dsimp only at h
    rw [coe_le_coe]
    split_ifs at h with hb
    · rw [hb]
      exact le_top
    · exact le_of_lt_succ (coe_lt_coe.1 h)

@[simp]
theorem succ_coe_top : succ ↑(⊤ : α) = (⊤ : WithTop α) :=
  dif_pos rfl

theorem succ_coe_of_ne_top {a : α} (h : a ≠ ⊤) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg h

end Succ

section Pred

variable [Preorder α] [OrderTop α] [PredOrder α]

instance : PredOrder (WithTop α) where
  pred a :=
    match a with
    | ⊤ => some ⊤
    | Option.some a => some (pred a)
  pred_le a :=
    match a with
    | ⊤ => le_top
    | Option.some a => coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_le ha).elim
    · exact (min_of_le_pred <| coe_le_coe.1 ha).withTop
  le_pred_of_lt {a b} h := by
    cases a
    · exact (le_top.not_lt h).elim
    cases b
    · exact coe_le_coe.2 le_top
    exact coe_le_coe.2 (le_pred_of_lt <| coe_lt_coe.1 h)
  le_of_pred_lt {a b} h := by
    cases b
    · exact le_top
    cases a
    · exact (not_top_lt <| coe_lt_coe.1 h).elim
    · exact coe_le_coe.2 (le_of_pred_lt <| coe_lt_coe.1 h)

@[simp]
theorem pred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) :=
  rfl

@[simp]
theorem pred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) :=
  rfl

@[simp]
theorem pred_untop :
    ∀ (a : WithTop α) (ha : a ≠ ⊤),
      pred (a.untop ha) = (pred a).untop (by induction a <;> simp)
  | ⊤, ha => (ha rfl).elim
  | (a : α), _ => rfl

end Pred

/-! #### Adding a `⊤` to a `NoMaxOrder` -/

section Succ

variable [Preorder α] [NoMaxOrder α] [SuccOrder α]

instance succOrderOfNoMaxOrder : SuccOrder (WithTop α) where
  succ a :=
    match a with
    | ⊤ => ⊤
    | Option.some a => some (succ a)
  le_succ a := by
    cases' a with a a
    · exact le_top
    · exact coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
    · exact (not_isMax _ <| max_of_succ_le <| coe_le_coe.1 ha).elim
  succ_le_of_lt {a b} h := by
    cases a
    · exact (not_top_lt h).elim
    cases b
    · exact le_top
    · exact coe_le_coe.2 (succ_le_of_lt <| coe_lt_coe.1 h)
  le_of_lt_succ {a b} h := by
    cases a
    · exact (not_top_lt h).elim
    cases b
    · exact le_top
    · exact coe_le_coe.2 (le_of_lt_succ <| coe_lt_coe.1 h)

@[simp]
theorem succ_coe (a : α) : succ (↑a : WithTop α) = ↑(succ a) :=
  rfl

end Succ

section Pred

variable [Preorder α] [NoMaxOrder α]

instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    cases' h : pred (⊤ : WithTop α) with a ha
    · exact hα.elim fun a => (min_of_le_pred h.ge).not_lt <| coe_lt_top a
    · obtain ⟨c, hc⟩ := exists_gt a
      rw [← coe_lt_coe, ← h] at hc
      exact (le_of_pred_lt hc).not_lt (coe_lt_top _)⟩

end Pred

end WithTop

namespace WithBot

/-! #### Adding a `⊥` to an `OrderBot` -/

section Succ

variable [Preorder α] [OrderBot α] [SuccOrder α]

instance : SuccOrder (WithBot α) where
  succ a :=
    match a with
    | ⊥ => some ⊥
    | Option.some a => some (succ a)
  le_succ a :=
    match a with
    | ⊥ => bot_le
    | Option.some a => coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact ((bot_lt_coe (⊥ : α)).not_le ha).elim
    · exact (max_of_succ_le <| coe_le_coe.1 ha).withBot
  succ_le_of_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact coe_le_coe.2 bot_le
    · exact coe_le_coe.2 (succ_le_of_lt <| coe_lt_coe.1 h)
  le_of_lt_succ {a b} h := by
    cases a
    · exact bot_le
    cases b
    · exact (not_lt_bot <| coe_lt_coe.1 h).elim
    · exact coe_le_coe.2 (le_of_lt_succ <| coe_lt_coe.1 h)

@[simp]
theorem succ_bot : succ (⊥ : WithBot α) = ↑(⊥ : α) :=
  rfl

@[simp]
theorem succ_coe (a : α) : succ (↑a : WithBot α) = ↑(succ a) :=
  rfl

@[simp]
theorem succ_unbot :
    ∀ (a : WithBot α) (ha : a ≠ ⊥),
      succ (a.unbot ha) = (succ a).unbot (by induction a <;> simp)
  | ⊥, ha => (ha rfl).elim
  | (a : α), _ => rfl

end Succ

section Pred

variable [DecidableEq α] [PartialOrder α] [OrderBot α] [PredOrder α]

instance : PredOrder (WithBot α) where
  pred a :=
    match a with
    | ⊥ => ⊥
    | Option.some a => ite (a = ⊥) ⊥ (some (pred a))
  pred_le a := by
    cases' a with a a
    · exact bot_le
    change ite _ _ _ ≤ _
    split_ifs
    · exact bot_le
    · exact coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases' a with a a
    · exact isMin_bot
    dsimp only at ha
    split_ifs at ha with ha'
    · exact (not_coe_le_bot _ ha).elim
    · rw [coe_le_coe, le_pred_iff_eq_bot] at ha
      exact (ha' ha).elim
  le_pred_of_lt {a b} h := by
    cases a
    · exact bot_le
    cases b
    · exact (not_lt_bot h).elim
    rw [coe_lt_coe] at h
    change _ ≤ ite _ _ _
    split_ifs with hb
    · rw [hb] at h
      exact (not_lt_bot h).elim
    · exact coe_le_coe.2 (le_pred_of_lt h)
  le_of_pred_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact bot_le
    dsimp only at h
    rw [coe_le_coe]
    split_ifs at h with ha
    · rw [ha]
      exact bot_le
    · exact le_of_pred_lt (coe_lt_coe.1 h)

@[simp]
theorem pred_coe_bot : pred ↑(⊥ : α) = (⊥ : WithBot α) :=
  dif_pos rfl

theorem pred_coe_of_ne_bot {a : α} (h : a ≠ ⊥) : pred (↑a : WithBot α) = ↑(pred a) :=
  dif_neg h

end Pred

/-! #### Adding a `⊥` to a `NoMinOrder` -/

section Succ

variable [Preorder α] [NoMinOrder α]

instance [hα : Nonempty α] : IsEmpty (SuccOrder (WithBot α)) :=
  ⟨by
    intro
    cases' h : succ (⊥ : WithBot α) with a ha
    · exact hα.elim fun a => (max_of_succ_le h.le).not_lt <| bot_lt_coe a
    · obtain ⟨c, hc⟩ := exists_lt a
      rw [← coe_lt_coe, ← h] at hc
      exact (le_of_lt_succ hc).not_lt (bot_lt_coe _)⟩

end Succ

section Pred

variable [Preorder α] [NoMinOrder α] [PredOrder α]

instance predOrderOfNoMinOrder : PredOrder (WithBot α) where
  pred a :=
    match a with
    | ⊥ => ⊥
    | Option.some a => some (pred a)
  pred_le a := by
    cases' a with a a
    · exact bot_le
    · exact coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
    · exact (not_isMin _ <| min_of_le_pred <| coe_le_coe.1 ha).elim
  le_pred_of_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact bot_le
    · exact coe_le_coe.2 (le_pred_of_lt <| coe_lt_coe.1 h)
  le_of_pred_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact bot_le
    · exact coe_le_coe.2 (le_of_pred_lt <| coe_lt_coe.1 h)

@[simp]
theorem pred_coe (a : α) : pred (↑a : WithBot α) = ↑(pred a) :=
  rfl

end Pred

end WithBot

/-! ### Archimedeanness -/

/-- A `SuccOrder` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class IsSuccArchimedean (α : Type*) [Preorder α] [SuccOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `a` from `b` by iterating `succ` -/
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, succ^[n] a = b

/-- A `PredOrder` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `b` from `a` by iterating `pred` -/
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a

export IsSuccArchimedean (exists_succ_iterate_of_le)

export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorder

variable [Preorder α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

instance : IsPredArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert exists_succ_iterate_of_le h.ofDual⟩

theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
  exists_succ_iterate_of_le h

theorem exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b := by
  refine ⟨?_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

/-- Induction principle on a type with a `SuccOrder` for all elements above a given element `m`. -/
@[elab_as_elim]
theorem Succ.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄
    (hmn : m ≤ n) : P n := by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate; clear hmn
  induction' n with n ih
  · exact h0
  · rw [Function.iterate_succ_apply']
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih

theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

instance : IsSuccArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert exists_pred_iterate_of_le h.ofDual⟩

theorem LE.le.exists_pred_iterate (h : a ≤ b) : ∃ n, pred^[n] b = a :=
  exists_pred_iterate_of_le h

theorem exists_pred_iterate_iff_le : (∃ n, pred^[n] b = a) ↔ a ≤ b :=
  exists_succ_iterate_iff_le (α := αᵒᵈ)

/-- Induction principle on a type with a `PredOrder` for all elements below a given element `m`. -/
@[elab_as_elim]
theorem Pred.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄
    (hmn : n ≤ m) : P n :=
  Succ.rec (α := αᵒᵈ) (P := P) h0 h1 hmn

theorem Pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b :=
  (Succ.rec_iff (α := αᵒᵈ) hsucc h).symm

end PredOrder

end Preorder

section LinearOrder

variable [LinearOrder α]

section SuccOrder
variable [SuccOrder α]

lemma succ_max (a b : α) : succ (max a b) = max (succ a) (succ b) := succ_mono.map_max
lemma succ_min (a b : α) : succ (min a b) = min (succ a) (succ b) := succ_mono.map_min

variable [IsSuccArchimedean α] {a b : α}

theorem exists_succ_iterate_or : (∃ n, succ^[n] a = b) ∨ ∃ n, succ^[n] b = a :=
  (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

end SuccOrder

section PredOrder
variable [PredOrder α]

lemma pred_max (a b : α) : pred (max a b) = max (pred a) (pred b) := pred_mono.map_max
lemma pred_min (a b : α) : pred (min a b) = min (pred a) (pred b) := pred_mono.map_min

variable [IsPredArchimedean α] {a b : α}

theorem exists_pred_iterate_or : (∃ n, pred^[n] b = a) ∨ ∃ n, pred^[n] a = b :=
  (le_total a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le

theorem Pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Pred.rec_iff hsucc) fun h => (Pred.rec_iff hsucc h).symm

end PredOrder

end LinearOrder

section bdd_range
variable [Preorder α] [Nonempty α] [Preorder β] {f : α → β}

lemma StrictMono.not_bddAbove_range [NoMaxOrder α] [SuccOrder β] [IsSuccArchimedean β]
    (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨m, hm⟩
  have hm' : ∀ a, f a ≤ m := fun a ↦ hm <| Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices ∀ b, f a₀ ≤ b → ∃ a, b < f a by
    obtain ⟨a, ha⟩ : ∃ a, m < f a := this m (hm' a₀)
    exact ha.not_le (hm' a)
  have h : ∀ a, ∃ a', f a < f a' := fun a ↦ (exists_gt a).imp (fun a' h ↦ hf h)
  apply Succ.rec
  · exact h a₀
  rintro b _ ⟨a, hba⟩
  exact (h a).imp (fun a' ↦ (succ_le_of_lt hba).trans_lt)

lemma StrictMono.not_bddBelow_range [NoMinOrder α] [PredOrder β] [IsPredArchimedean β]
    (hf : StrictMono f) : ¬ BddBelow (Set.range f) := hf.dual.not_bddAbove_range

lemma StrictAnti.not_bddAbove_range [NoMinOrder α] [SuccOrder β] [IsSuccArchimedean β]
    (hf : StrictAnti f) : ¬ BddAbove (Set.range f) := hf.dual_right.not_bddBelow_range

lemma StrictAnti.not_bddBelow_range [NoMaxOrder α] [PredOrder β] [IsPredArchimedean β]
    (hf : StrictAnti f) : ¬ BddBelow (Set.range f) := hf.dual_right.not_bddAbove_range

end bdd_range

section IsWellOrder

variable [LinearOrder α]

instance (priority := 100) IsWellOrder.toIsPredArchimedean [h : IsWellOrder α (· < ·)]
    [PredOrder α] : IsPredArchimedean α :=
  ⟨fun {a b} => by
    refine WellFounded.fix (C := fun b => a ≤ b → ∃ n, Nat.iterate pred n b = a)
      h.wf ?_ b
    intros b ih hab
    replace hab := eq_or_lt_of_le hab
    rcases hab with (rfl | hab)
    · exact ⟨0, rfl⟩
    rcases le_or_lt b (pred b) with hb | hb
    · cases (min_of_le_pred hb).not_lt hab
    dsimp at ih
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    refine ⟨k + 1, ?_⟩
    rw [iterate_add_apply, iterate_one, hk]⟩

instance (priority := 100) IsWellOrder.toIsSuccArchimedean [h : IsWellOrder α (· > ·)]
    [SuccOrder α] : IsSuccArchimedean α :=
  let h : IsPredArchimedean αᵒᵈ := by infer_instance
  ⟨h.1⟩

end IsWellOrder

section OrderBot

variable [Preorder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)

end OrderBot

section OrderTop

variable [Preorder α] [OrderTop α] [PredOrder α] [IsPredArchimedean α]

theorem Pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
  Pred.rec htop (fun x _ h => hpred x h) (le_top : a ≤ ⊤)

end OrderTop

lemma SuccOrder.forall_ne_bot_iff
    [Nontrivial α] [PartialOrder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]
    (P : α → Prop) :
    (∀ i, i ≠ ⊥ → P i) ↔ (∀ i, P (SuccOrder.succ i)) := by
  refine ⟨fun h i ↦ h _ (Order.succ_ne_bot i), fun h i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ ≤ i)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose! hi; simp [hi]
  rw [← Nat.succ_pred_eq_of_pos hj]
  simp only [Function.iterate_succ', Function.comp_apply]
  apply h
