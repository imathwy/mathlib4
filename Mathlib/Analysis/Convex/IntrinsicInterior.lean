/-
Copyright (c) 2025 Zichen Wang, Chenyi Li, ZaiWen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Chenyi Li, ZaiWen Wen
-/
import Mathlib.Analysis.Convex.Intrinsic
/-!
# Intrinsic Interior, Closure, and Related Properties of Convex Sets

This file explores the intrinsic interior, intrinsic closure,
and related properties of convex sets in a normed vector space,
focusing on their interactions with affine spans, closures, and intersections.
The intrinsic interior and closure of a convex set are defined based on its affine span,
while the intrinsic interior is generally larger than the topological interior,
and the intrinsic closure coincides with the topological closure under certain conditions.

## Results
The main results are:
* `openSegment_sub_intrinsicInterior`: The open segment between two points in the intrinsic
    interior of a convex set is contained in the intrinsic interior.
* `convex_intrinsicInterior`: The intrinsic interior of a convex set is convex.
* `convex_intrinsicClosure`: The intrinsic closure of a convex set is convex.
* `affinespan_intrinsicInterior`: The affine span of the intrinsic interior of a convex set is
    equal to the affine span of the set.
* `intrinsicInterior_intrinsicInterior`: The intrinsic interior of the intrinsic interior of
    a convex set is equal to the intrinsic interior of the set.
* `intrinsicInterior_iff`: A point lies in the intrinsic interior of a convex set if and only if
    for every point in the set, there exists a scalar greater than one such that the point
    lies in the set.
* `intrinsicInterior_intrinsicClosure`: The intrinsic interior of the intrinsic closure of a
    convex set is equal to the intrinsic interior of the set.
* `intrinsicClosure_intrinsicInterior`: The intrinsic closure of the intrinsic interior of a
    convex set is equal to the intrinsic closure of the set.
* `closure_intrinsicInterior`: The closure of the intrinsic interior of a convex set is equal to
    the closure of the set.
* `intrinsicInterior_closure`: The intrinsic interior of the closure of a convex set is
    equal to the intrinsic interior of the set.
* `iIntersection_closure_eq_intrinsicInterior_closure`: if each set is convex and there exists
    a point in the intrinsic interior of all sets, then the intersection of their closures equals
    the closure of their intersection.
* `iIntersection_intrinsicInterior_eq_intrinsicInterior_iIntersection`: The intrinsic interior
    of the finite intersection of convex sets is equal to the intersection of their intrinsic
    interiors.

## References

* Chapter 6 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open AffineSubspace Set

open scoped Pointwise

variable {𝕜 V P : Type*}

noncomputable section

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-
Given a nonempty affineSubspace s, it defines an isomorphism
between the affineSubspace and its direction
-/
def AffineSubspaceEquivAffineSubspace_direction {s : AffineSubspace 𝕜 P} {z} (hz : z ∈ s) :
    s ≃ s.direction where
  toFun := fun x => ⟨x.1 -ᵥ z,
    AffineSubspace.vsub_mem_direction (SetLike.coe_mem x) hz⟩
  invFun := fun x => ⟨x +ᵥ z,
    AffineSubspace.vadd_mem_of_mem_direction (Submodule.coe_mem x) hz⟩
  left_inv := by
    simp only [Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    intro a _
    exact ((eq_vadd_iff_vsub_eq a _ _).mpr rfl).symm
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, Subtype.forall, Subtype.mk.injEq]
    intro a _
    exact AddTorsor.vadd_vsub' _ _

/-
Given a nonempty set s, it defines an isomorphism
between the affine span and its direction
-/
@[simp]
def AffineSpanEquivAffineSpan_direction {s : Set P} (hs : s.Nonempty):
    affineSpan 𝕜 s ≃ (affineSpan 𝕜 s).direction := by
  apply AffineSubspaceEquivAffineSubspace_direction 𝕜 <| mem_affineSpan 𝕜 hs.choose_spec


end

noncomputable section

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [ContinuousSub V] [ContinuousAdd V]

/-
there exists a homeomorphism (a continuous bijection with a continuous inverse)
between an affine subspace  s  of a vector space  V  over a field  𝕜  and
its direction  s.direction , given a chosen point  z ∈ s .
-/
def AffineSubspaceHomeomorphAffineSubspace_direction
    {s : AffineSubspace 𝕜 V} {z} (hz : z ∈ s) : s ≃ₜ s.direction:=
    ⟨AffineSubspaceEquivAffineSubspace_direction 𝕜 hz, by
      simpa only [Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      using .subtype_mk (.comp (continuous_sub_right _) continuous_subtype_val) _, by
      simpa only [Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      using .subtype_mk (.comp (continuous_add_right _) continuous_subtype_val) _⟩

@[simp]
def AffineSpanHomeomorphAffineSpan_direction
    {s : Set V} (hs : s.Nonempty):
  affineSpan 𝕜 s ≃ₜ (affineSpan 𝕜 s).direction:=
  AffineSubspaceHomeomorphAffineSubspace_direction 𝕜 <| mem_affineSpan 𝕜 hs.choose_spec

end
