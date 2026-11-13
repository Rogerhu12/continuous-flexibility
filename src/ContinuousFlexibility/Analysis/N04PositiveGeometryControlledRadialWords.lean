import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRadialFormula
import ContinuousFlexibility.Analysis.N04PositiveGeometrySampledPlaneKernel

/-!
# Saved words of both stored radial factors

The forward and inverse radial factors use one coefficient packet and
one open coefficient domain. The inverse estimate is evaluated only on
the physical component slab; its scalar inverse remains the inverse of
the displayed stored kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_controlled_forwardKernel_contDiff
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    ContDiff ℝ ∞ (G.toN04PositiveGeometryControlData.radialKernel i) := by
  have ho := G.buffer.ordered i
  have hcd := ho.2.1.trans (ho.2.2.1.trans ho.2.2.2.1)
  have hgeom := n04PositiveGeometry_radialKernel_geometry n ho.1 hcd ho.2.2.2.2
    (half_pos (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))))
    (zero_le_one.trans (G.inverse_one i))
  exact n04PositiveGeometry_radialKernel_contDiff n _ _ _ _ hcd _ hgeom.1 hgeom.2.1

variable {V : Type*}
  [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem n04PositiveGeometry_controlledRadial_saved_word_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (inverse : Bool)
    (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (U : Set V), IsOpen U →
      ∀ state : V → AnnularState W.S × ℝ,
      (∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε) →
      (∀ x ∈ U, stateSector W.S (state x).1) →
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ J : SmoothDirections (U ×ˢ univ)
        (fun z : V × ℝ => fun side (k : Fin (n + 1)) =>
          G.toN04PositiveGeometryControlData.coefficients (state z.1) i side (k + 1) z.2),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun z : V × PolarPoint => if inverse then
          G.toN04PositiveGeometryControlData.radialInverse (state z.1) i z.2 else
          G.toN04PositiveGeometryControlData.radial (state z.1) i z.2),
      ∀ (p q : Seminorm ℝ V) (R H t : ℝ), 0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ (K s shift : ℕ) (x : V), x ∈ U → ∀ y : PolarPoint,
      y.1 ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) →
      N04BoundaryWordBounds J K (s + K) 1 x y.2
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift →
      ∀ j : ℕ, 0 < j → j ≤ N → j ≤ K + s + 1 →
      ∀ w : StateAngleWord j, w.stateArity ≤ K →
      ∀ v : Fin j → V × PolarPoint,
      (∀ k, if w.isState k then (v k).2 = 0 else (v k).1 = 0) →
      (∀ k, p (v k).1 ≤ 1 ∧ q (v k).1 ≤ R ∧ ‖(v k).2‖ ≤ 1) →
        ‖Q.D j (x, y) v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
          parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := by
  let I := N04PositiveComponent W.D.a W.D.b (deriv W.D.w)
  let E : I → ℝ := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i : I) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let C := G.toN04PositiveGeometryControlData.radialCoefficientDomain
  let Ω : I → Set (N04PositiveRadialCoefficients n × ℝ) :=
    fun i => C i ×ˢ Icc (n04PositiveLeft i) (n04PositiveRight i)
  let g := fun i => if inverse then G.toN04PositiveGeometryControlData.radialInverseKernel i
    else G.toN04PositiveGeometryControlData.radialKernel i
  have hopen (i : I) : IsOpen (C i ×ˢ (univ : Set ℝ)) :=
    (n04PositiveGeometry_radialCoefficientDomain_isOpen n _ _).prod isOpen_univ
  have hg (i : I) : ContDiffOn ℝ ∞ (g i) (C i ×ˢ univ) := by
    cases inverse with
    | false => exact (n04PositiveGeometry_controlled_forwardKernel_contDiff G i).contDiffOn
    | true => exact n04PositiveGeometry_controlled_inverseKernel_contDiffOn G i
  have hkernel (j : ℕ) (_hj : j ≤ N) : ∃ C₀ P : ℝ, 0 ≤ C₀ ∧ 0 ≤ P ∧
      ∀ i z, z ∈ Ω i → ‖iteratedFDeriv ℝ j (g i) z‖ ≤ C₀ * E i ^ P := by
    obtain ⟨C₀, P, hC₀, hP, hb⟩ := n04PositiveGeometry_controlled_radialKernels_bounds G inverse j
    exact ⟨C₀, P, hC₀.le, hP, fun i z hz => hb i z.1 hz.1 z.2 hz.2⟩
  obtain ⟨B, hB, hbound⟩ := n04PositiveGeometry_sampledPlaneKernel_saved_prefix
    (E := V) E hE (fun i => C i ×ˢ univ) Ω g hopen hg N A RH hA hkernel
  refine ⟨B, hB, ?_⟩
  intro U hU state hstate hsector i J Q p q R H t hR hH hHR ht K s shift x hx y hy hraw
    j hj hjN hjs w hw v hpure hbox
  let f : V × ℝ → N04PositiveRadialCoefficients n := fun z side k =>
    G.toN04PositiveGeometryControlData.coefficients (state z.1) i side (k + 1) z.2
  have hmem (z : V × ℝ) (hz : z.1 ∈ U) : f z ∈ C i :=
    n04PositiveGeometry_controlled_coefficients_mem G (hstate z.1 hz) (hsector z.1 hz) i z.2
  have hmap : MapsTo (fun z : V × PolarPoint => (f (z.1, z.2.2), z.2.1))
      (U ×ˢ univ) (C i ×ˢ univ) := fun z hz => ⟨hmem _ hz.1, mem_univ _⟩
  let QK : SmoothDirections (U ×ˢ univ)
      (fun z : V × PolarPoint => g i (f (z.1, z.2.2), z.2.1)) :=
    Q.congr (fun z hz => by
      cases inverse with
      | false =>
          exact n04PositiveGeometry_controlled_radial_eq_kernel G
            (hstate z.1 hz.1) (hsector z.1 hz.1) i z.2
      | true =>
          exact n04PositiveGeometry_controlled_radialInverse_eq_kernel G
            (hstate z.1 hz.1) (hsector z.1 hz.1) i z.2)
  exact hbound U hU f J i hmap QK p q R H t hR hH hHR ht K s shift x hx y
    ⟨hmem _ hx, hy⟩ hraw j hj hjN hjs w hw v hpure hbox

end ContinuousFlexibility.Analysis
