module

public import ContinuousFlexibility.Analysis.CanonicalEndpointInverse
public import ContinuousFlexibility.Analysis.N01cFiniteAffineJets
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Actual planar inverses on finite affine parameter slices

The implicit function theorem supplies smoothness of the given right
inverse from the genuine forward family, its spatial Jacobian and its
injectivity domain. No regularity of the right inverse is assumed.

A genuine tower on a topological parameter space restricts to an ordinary
smooth function on each finite affine slice. This module applies the
planar inverse theorem on precisely those slices; it does not give the
original parameter space an artificial norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

section NormedParameters

variable {P Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {U : Set P} {V W : Set Y} {F G : P × Y → Y}

/-- A spatially injective family identifies its actual right inverse with
its local implicit solution. The conclusion includes inverse continuity. -/
theorem n04NegativeGeometry_contDiffOn_parameterized_inverse
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    (hD : ∀ z ∈ U ×ˢ V,
      (fderiv ℝ (fun y => F (z.1, y)) z.2).IsInvertible)
    (hInj : ∀ p ∈ U, InjOn (fun y => F (p, y)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ z ∈ U ×ˢ W, F (z.1, G z) = z.2) :
    ContDiffOn ℝ ∞ G (U ×ˢ W) := by
  intro q hq
  have hqV : G q ∈ V := hMaps hq
  have hFq : ContDiffAt ℝ ∞ F (q.1, G q) :=
    hF.contDiffAt ((hU.prod hV).mem_nhds ⟨hq.1, hqV⟩)
  let A : Y →L[ℝ] Y := fderiv ℝ (fun y => F (q.1, y)) (G q)
  let H : (P × Y) × Y → Y := fun z => F (z.1.1, z.2) - z.1.2
  have hH : ContDiffAt ℝ ∞ H (q, G q) :=
    (hFq.comp (q, G q) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub
      contDiffAt_fst.snd
  have hsmooth : ContDiffAt ℝ ∞ (fun y => F (q.1, y)) (G q) :=
    hFq.comp (G q) (contDiffAt_const.prodMk contDiffAt_id)
  have hs : HasFDerivAt (fun y => H (q, y)) A (G q) :=
    (hsmooth.differentiableAt (by simp)).hasFDerivAt.sub_const q.2
  have hp : HasFDerivAt (fun y => H (q, y))
      ((fderiv ℝ H (q, G q)).comp (ContinuousLinearMap.inr ℝ (P × Y) Y)) (G q) := by
    simpa only [Function.comp_def] using
      (hH.differentiableAt (by simp)).hasFDerivAt.comp (G q)
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) q (G q))
  have hi : ((fderiv ℝ H (q, G q)).comp
      (ContinuousLinearMap.inr ℝ (P × Y) Y)).IsInvertible := by
    rw [hp.unique hs]
    exact hD (q.1, G q) ⟨hq.1, hqV⟩
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let ψ : P × Y → Y := hH.implicitFunction hn hi
  have hψ : ContDiffAt ℝ ∞ ψ q := hH.contDiffAt_implicitFunction hn hi
  have hψq : ψ q = G q := hH.implicitFunction_apply_self hn hi
  have hψV : ∀ᶠ z in 𝓝 q, ψ z ∈ V :=
    hψ.continuousAt.tendsto.eventually (by rw [hψq]; exact hV.mem_nhds hqV)
  have hsol : ∀ᶠ z in 𝓝 q, H (z, ψ z) = H (q, G q) :=
    hH.eventually_apply_implicitFunction hn hi
  have hzero : H (q, G q) = 0 := by
    change F (q.1, G q) - q.2 = 0
    rw [hRight q hq, sub_self]
  have heq : G =ᶠ[𝓝 q] ψ := by
    filter_upwards [(hU.prod hW).mem_nhds hq, hψV, hsol] with z hz hψz hsz
    apply hInj z.1 hz.1 (hMaps hz) hψz
    have hzsol : F (z.1, ψ z) = z.2 := by
      have hh : F (z.1, ψ z) - z.2 = 0 := hsz.trans hzero
      exact sub_eq_zero.mp hh
    exact (hRight z hz).trans hzsol.symm
  exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt

/-- A nonzero planar Jacobian supplies the required spatial invertibility. -/
theorem n04NegativeGeometry_contDiffOn_parameterized_planar_inverse
    {V W : Set PolarPoint} {F G : P × PolarPoint → PolarPoint}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    (hJac : ∀ z ∈ U ×ˢ V, planeJacobian (fun y => F (z.1, y)) z.2 ≠ 0)
    (hInj : ∀ p ∈ U, InjOn (fun y => F (p, y)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ z ∈ U ×ˢ W, F (z.1, G z) = z.2) :
    ContDiffOn ℝ ∞ G (U ×ˢ W) := by
  apply n04NegativeGeometry_contDiffOn_parameterized_inverse hU hV hW hF
    (fun z hz => ?_) hInj hMaps hRight
  let A := fderiv ℝ (fun y => F (z.1, y)) z.2
  have hd : A.det ≠ 0 := by
    simpa only [A, planeJacobian_eq_fderiv_det] using hJac z hz
  let L : PolarPoint ≃L[ℝ] PolarPoint := A.toContinuousLinearEquivOfDetNeZero hd
  have hL : (L : PolarPoint →L[ℝ] PolarPoint) = A := by
    simp only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  exact ⟨L, hL⟩

end NormedParameters

section FiniteAffineParameters

variable {E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {U : Set E} {V W : Set PolarPoint} {F G : E × PolarPoint → PolarPoint}

/-- The literal inverse is jointly smooth on every finite affine slice
of the original parameter space. This is a consequence of the forward
tower and the actual slice-wise inverse identities. -/
theorem n04NegativeGeometry_inverse_contDiffOn_finiteAffine
    (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hJac : ∀ z ∈ U ×ˢ V, planeJacobian (fun y => F (z.1, y)) z.2 ≠ 0)
    (hInj : ∀ x ∈ U, InjOn (fun y => F (x, y)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ z ∈ U ×ˢ W, F (z.1, G z) = z.2)
    (x₀ : E) (L : P →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun z : P × PolarPoint => G (x₀ + L z.1, z.2))
      (((fun p => x₀ + L p) ⁻¹' U) ×ˢ W) := by
  let A : (P × PolarPoint) →L[ℝ] E × PolarPoint :=
    (L.comp (ContinuousLinearMap.fst ℝ P PolarPoint)).prod
      (ContinuousLinearMap.snd ℝ P PolarPoint)
  have hA (z : P × PolarPoint) : (x₀, (0 : PolarPoint)) + A z =
      (x₀ + L z.1, z.2) := by
    change (x₀ + L z.1, 0 + z.2) = _
    rw [zero_add]
  have hf := smoothDirections_contDiffOn_finiteAffine J (x₀, (0 : PolarPoint)) A
  have heq : (fun z : P × PolarPoint => F ((x₀, (0 : PolarPoint)) + A z)) =
      (fun z => F (x₀ + L z.1, z.2)) := by
    funext z
    rw [hA]
  have hdomain : (fun z : P × PolarPoint => (x₀, (0 : PolarPoint)) + A z) ⁻¹' (U ×ˢ V) =
      (((fun p => x₀ + L p) ⁻¹' U) ×ˢ V) := by
    ext z
    simp only [mem_preimage, hA, mem_prod]
  rw [heq, hdomain] at hf
  exact n04NegativeGeometry_contDiffOn_parameterized_planar_inverse
    (hU.preimage (continuous_const.add L.continuous)) hV hW hf
    (fun z hz => hJac (x₀ + L z.1, z.2) ⟨hz.1, hz.2⟩)
    (fun p hp => hInj (x₀ + L p) hp)
    (fun z hz => hMaps ⟨hz.1, hz.2⟩)
    (fun z hz => hRight (x₀ + L z.1, z.2) ⟨hz.1, hz.2⟩)

end FiniteAffineParameters

end ContinuousFlexibility.Analysis
