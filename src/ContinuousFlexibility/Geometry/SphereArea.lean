module

public import ContinuousFlexibility.Geometry.SphereMetric
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual Hausdorff area of the constructed sphere images

Area is the normalized Euclidean two-dimensional Hausdorff measure of the
actual image in E3. The rotating graph image is an ambient isometric image;
the cap is fixed, and their intersection is contained in a null circle.
Finiteness uses Lipschitz images of compact two-dimensional parameter sets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory Measure
open scoped ContDiff Topology ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

private instance polar_hausdorffTwo_haar :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure PolarPoint).IsAddHaarMeasure := by
  simpa [PolarPoint] using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := PolarPoint))

theorem euclideanArea_zero_iff_hausdorff (s : Set E3) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) s = 0 ↔
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E3) s = 0 := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  simp only [mul_eq_zero, ENNReal.coe_eq_zero,
    Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, false_or]
  norm_num

theorem euclideanArea_lt_top_of_hausdorff {s : Set E3}
    (hs : (Measure.hausdorffMeasure (2 : ℝ) : Measure E3) s < ⊤) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) s < ⊤ := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  exact ENNReal.nnreal_smul_lt_top hs

theorem smooth_compact_planar_image_area_lt_top {F : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) {s : Set PolarPoint} (hs : IsCompact s) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) (F '' s) < ⊤ := by
  have hl : LocallyLipschitzOn s F :=
    (hF.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).locallyLipschitz.locallyLipschitzOn
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs hl
  apply euclideanArea_lt_top_of_hausdorff
  have hh := hK.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
  apply hh.trans_lt
  rw [ENNReal.rpow_two]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hs.measure_lt_top

theorem IsometricGraphDevelopment.graphPhaseDiskImage_area_invariant {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R t : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) (graphPhaseDiskImage D R t) =
      (Measure.euclideanHausdorffMeasure 2 : Measure E3) (graphPhaseDiskImage D R 0) := by
  unfold graphPhaseDiskImage
  rw [D.rotationFamily_image_closedDisk t R, D.rotationFamily_image_closedDisk 0 R]
  rw [(axialRotation (-t)).isometry.euclideanHausdorffMeasure_image,
    (axialRotation (-0)).isometry.euclideanHausdorffMeasure_image]

/-- The graph portion's actual area measure is transported by the actual
ambient rotation, providing a measure-level bridge for geometric integrals. -/
theorem IsometricGraphDevelopment.graphPhaseDiskImage_areaMeasure_map {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R t : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (graphPhaseDiskImage D R t) =
      ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
        (D.map '' {x : PolarPoint | cartesianRadius x ≤ R})).map (axialRotation (-t)) := by
  let μ : Measure E3 := Measure.euclideanHausdorffMeasure 2
  let S : Set E3 := D.map '' {x : PolarPoint | cartesianRadius x ≤ R}
  let e : E3 ≃ᵐ E3 := (axialRotation (-t)).toHomeomorph.toMeasurableEquiv
  have hm : μ.map e = μ :=
    (axialRotation (-t)).toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure 2 |>.map_eq
  have hres := e.restrict_map μ (e '' S)
  rw [hm, Set.preimage_image_eq _ e.injective] at hres
  unfold graphPhaseDiskImage
  rw [D.rotationFamily_image_closedDisk t R]
  change μ.restrict (e '' S) = (μ.restrict S).map e
  exact hres

theorem IsometricGraphDevelopment.graphPhaseDiskImage_area_lt_top {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R t : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) (graphPhaseDiskImage D R t) < ⊤ :=
  smooth_compact_planar_image_area_lt_top (D.rotationFamily_smooth t)
    (isCompact_closedCartesianDisk R)

/-- Change of variables on the actual rotating graph image, for an arbitrary
ambient integrand. The measure is the image Hausdorff area, not a parameter
measure or a newly defined invariant. -/
theorem IsometricGraphDevelopment.graphPhaseDiskImage_integral_rotate {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (R t : ℝ) (h : E3 → ℝ) :
    (∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (graphPhaseDiskImage D R t)) =
      ∫ z, h (axialRotation (-t) z)
        ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
          (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) := by
  rw [D.graphPhaseDiskImage_areaMeasure_map R t]
  exact ((axialRotation (-t)).toHomeomorph.toMeasurableEquiv).measurableEmbedding.integral_map h

private def areaPlanarProjection : E3 →L[ℝ] PolarPoint :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).prod
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))

private theorem areaPlanarProjection_apply (v : E3) :
    areaPlanarProjection v = graphBaseProjection v := rfl

theorem IsometricGraphDevelopment.graphPhaseDiskImage_area_pos {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b ≤ R) (t : ℝ) :
    0 < (Measure.euclideanHausdorffMeasure 2 : Measure E3) (graphPhaseDiskImage D R t) := by
  have hRp : 0 < R := A.b_pos.trans_le hR
  have hopen : IsOpen {x : PolarPoint | cartesianRadius x < R} :=
    isOpen_lt continuous_cartesianRadius continuous_const
  have hnonempty : ({x : PolarPoint | cartesianRadius x < R} : Set PolarPoint).Nonempty :=
    ⟨0, by
      change cartesianRadius (0 : PolarPoint) < R
      simpa only [cartesianRadius, map_zero, norm_zero] using hRp⟩
  have hpos : 0 < (Measure.hausdorffMeasure (2 : ℝ) : Measure PolarPoint)
      {x : PolarPoint | cartesianRadius x ≤ R} :=
    (hopen.measure_pos (μ := (Measure.hausdorffMeasure (2 : ℝ) : Measure PolarPoint)) hnonempty).trans_le
      (measure_mono (by
        intro x hx
        change cartesianRadius x < R at hx
        change cartesianRadius x ≤ R
        exact hx.le))
  apply pos_iff_ne_zero.mpr
  intro hz
  have hraw := (euclideanArea_zero_iff_hausdorff _).mp hz
  have hp := areaPlanarProjection.lipschitzWith.hausdorffMeasure_image_le
    (d := (2 : ℝ)) (by norm_num) (graphPhaseDiskImage D R t)
  rw [hraw, mul_zero] at hp
  have himage : areaPlanarProjection '' graphPhaseDiskImage D R t =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
    have he : (areaPlanarProjection : E3 → PolarPoint) = graphBaseProjection :=
      funext areaPlanarProjection_apply
    rw [he]
    exact D.rotationFamily_projects_onto_disk t hR
  rw [himage] at hp
  exact (not_le_of_gt hpos) hp

theorem isCompact_markedCapImage {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ) :
    IsCompact (markedCapMap R h L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) :=
  isCompact_capDiskDomain_set.image (contDiff_markedCapMap hR hL h k ρ).continuous

theorem markedCapImage_area_lt_top {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3)
      (markedCapMap R h L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) < ⊤ :=
  smooth_compact_planar_image_area_lt_top (contDiff_markedCapMap hR hL h k ρ)
    isCompact_capDiskDomain_set

theorem smooth_compact_curve_area_eq_zero {γ : ℝ → E3}
    (hγ : ContDiff ℝ ∞ γ) {s : Set ℝ} (hs : IsCompact s) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) (γ '' s) = 0 := by
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by simp)
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs
    hγ1.locallyLipschitz.locallyLipschitzOn
  have hsfin : (Measure.hausdorffMeasure (1 : ℝ) : Measure ℝ) s < ⊤ := by
    simpa using (hs.measure_lt_top
      (μ := (Measure.hausdorffMeasure (Module.finrank ℝ ℝ) : Measure ℝ)))
  have hs0 : (Measure.hausdorffMeasure (2 : ℝ) : Measure ℝ) s = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (d₁ := 1) (d₂ := 2) (by norm_num) s).resolve_right hsfin.ne
  have himage : (Measure.hausdorffMeasure (2 : ℝ) : Measure E3) (γ '' s) = 0 := by
    apply le_antisymm _ zero_le
    simpa only [hs0, mul_zero] using hK.hausdorffMeasure_image_le (d := 2) (by norm_num)
  exact (euclideanArea_zero_iff_hausdorff _).mpr himage

theorem capAttachingRim_area_eq_zero (R h : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3) (capAttachingRim R h) = 0 := by
  let γ : ℝ → E3 := fun θ => graphMap id (fun _ => h) (polarMap (R, θ))
  have hγ : ContDiff ℝ ∞ γ := by
    have hp : ContDiff ℝ ∞ (fun θ : ℝ => (R, θ)) := contDiff_const.prodMk contDiff_id
    have hpolar : ContDiff ℝ ∞ (fun θ : ℝ => polarMap (R, θ)) := contDiff_polarMap.comp hp
    have hg : ContDiff ℝ ∞ (graphMap id (fun _ => h)) :=
      contDiff_graphMap contDiff_id contDiff_const
    simpa only [γ, Function.comp_def] using hg.comp hpolar
  have hsub : capAttachingRim R h ⊆ γ '' Icc (-Real.pi) Real.pi := by
    rintro z ⟨x, hx, rfl⟩
    change cartesianRadius x = R at hx
    refine ⟨(Complex.equivRealProdCLM.symm x).arg,
      ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩, ?_⟩
    exact congrArg (graphMap id (fun _ => h))
      (by simpa only [hx] using polarMap_cartesianCoordinates x)
  exact measure_mono_null hsub (smooth_compact_curve_area_eq_zero hγ isCompact_Icc)

theorem IsometricGraphDevelopment.markedSphereFamily_area_add {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3)
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) =
      (Measure.euclideanHausdorffMeasure 2 : Measure E3) (graphPhaseDiskImage D R t) +
        (Measure.euclideanHausdorffMeasure 2 : Measure E3)
          (markedCapMap R A.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) := by
  rw [sphereGraphCapFamily_range D hR hL (fun _ hy =>
    markedCapMap_capSphereRadialMap_rim_germ (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t]
  apply measure_union₀
    (isCompact_markedCapImage (A.b_pos.trans hR) hL A.cRight k ρ).measurableSet.nullMeasurableSet
  exact measure_mono_null (D.marked_cap_meeting_subset hR hL hρ hsmall hmeet)
    (capAttachingRim_area_eq_zero R A.cRight)

/-- Equality of the actual surface-area measures, also usable for geometric
integrals once their genuine ambient integrands have been identified. -/
theorem IsometricGraphDevelopment.markedSphereFamily_areaMeasure_add {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) =
      (Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (graphPhaseDiskImage D R t) +
        (Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
          (markedCapMap R A.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) := by
  rw [sphereGraphCapFamily_range D hR hL (fun _ hy =>
    markedCapMap_capSphereRadialMap_rim_germ (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t]
  apply Measure.restrict_union₀
  · exact measure_mono_null (D.marked_cap_meeting_subset hR hL hρ hsmall hmeet)
      (capAttachingRim_area_eq_zero R A.cRight)
  · exact (isCompact_markedCapImage (A.b_pos.trans hR) hL A.cRight k ρ).measurableSet.nullMeasurableSet

theorem IsometricGraphDevelopment.markedSphereFamily_area_invariant {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : ∀ s : ℝ, graphPhaseDiskImage D R s ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (t : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3)
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) =
      (Measure.euclideanHausdorffMeasure 2 : Measure E3)
        (Set.range (fun x : SpherePoint =>
          sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, 0))) := by
  rw [D.markedSphereFamily_area_add hR hL hρ hsmall t (hmeet t),
    D.markedSphereFamily_area_add hR hL hρ hsmall 0 (hmeet 0),
    D.graphPhaseDiskImage_area_invariant R t]

/-- The null attaching circle allows the genuine surface integral to split
into its moving graph and fixed marked cap, without counting the rim twice. -/
theorem IsometricGraphDevelopment.markedSphereFamily_integral_add {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ)
    (hmeet : graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) {h : E3 → ℝ}
    (hint : Integrable h ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))))) :
    (∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)))) =
      (∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
        (graphPhaseDiskImage D R t)) +
      ∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
        (markedCapMap R A.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) := by
  rw [D.markedSphereFamily_areaMeasure_add hR hL hρ hsmall t hmeet] at hint ⊢
  exact integral_add_measure hint.left_of_add_measure hint.right_of_add_measure

/-- Actual image-integral invariance from actual rotation transport on the
graph and pointwise agreement on the fixed cap. Geometric integrands must
still be identified with their true curvature values before applying this. -/
theorem IsometricGraphDevelopment.markedSphereFamily_integral_invariant
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hmeet : ∀ s : ℝ, graphPhaseDiskImage D R s ∩ capDiskImage R A.cRight L =
      capAttachingRim R A.cRight) (t : ℝ) {h ht : E3 → ℝ}
    (hi : Integrable h ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, 0)))))
    (hit : Integrable ht ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)))))
    (hg : ∀ z ∈ D.map '' {x : PolarPoint | cartesianRadius x ≤ R},
      ht (axialRotation (-t) z) = h z)
    (hc : ∀ z ∈ markedCapMap R A.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1},
      ht z = h z) :
    (∫ z, ht z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t)))) =
      ∫ z, h z ∂(Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict
        (Set.range (fun x : SpherePoint =>
          sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, 0))) := by
  rw [D.markedSphereFamily_integral_add hR hL hρ hsmall t (hmeet t) hit,
    D.markedSphereFamily_integral_add hR hL hρ hsmall 0 (hmeet 0) hi,
    D.graphPhaseDiskImage_integral_rotate R t,
    D.graphPhaseDiskImage_integral_rotate R 0]
  apply congrArg₂ (· + ·)
  · apply integral_congr_ae
    have hcompact : IsCompact (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) :=
      (isCompact_closedCartesianDisk R).image D.smooth_graph.continuous
    apply ae_restrict_of_forall_mem hcompact.measurableSet
    intro z hz
    simpa only [neg_zero, axialRotation_apply, axialRotationMap_zero] using hg z hz
  · exact integral_congr_ae (ae_restrict_of_forall_mem
      (isCompact_markedCapImage (A.b_pos.trans hR) hL A.cRight k ρ).measurableSet hc)

theorem IsometricGraphDevelopment.markedSphereFamily_area_lt_top {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E3)
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) < ⊤ := by
  rw [sphereGraphCapFamily_range D hR hL (fun _ hy =>
    markedCapMap_capSphereRadialMap_rim_germ (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t]
  apply (measure_union_le _ _).trans_lt
  exact ENNReal.add_lt_top.mpr ⟨D.graphPhaseDiskImage_area_lt_top R t,
    markedCapImage_area_lt_top (A.b_pos.trans hR) hL A.cRight k ρ⟩

theorem IsometricGraphDevelopment.markedSphereFamily_area_pos {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    0 < (Measure.euclideanHausdorffMeasure 2 : Measure E3)
      (Set.range (fun x : SpherePoint =>
        sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) := by
  rw [sphereGraphCapFamily_range D hR hL (fun _ hy =>
    markedCapMap_capSphereRadialMap_rim_germ (A.b_pos.trans hR) hL hρ hsmall A.cRight hy) t]
  exact (D.graphPhaseDiskImage_area_pos hR.le t).trans_le (measure_mono Set.subset_union_left)

/-- A genuine scalar representative on the embedded image is integrable when
its pullback is continuous and the actual image area is finite. No ambient
local-finiteness assumption is made for two-dimensional measure in E3. -/
theorem integrable_surfaceArea_of_continuous_comp {F : SpherePoint → E3} {h : E3 → ℝ}
    (he : Topology.IsEmbedding F) (hc : Continuous (h ∘ F))
    (hfinite : (Measure.euclideanHausdorffMeasure 2 : Measure E3) (Set.range F) < ⊤) :
    Integrable h ((Measure.euclideanHausdorffMeasure 2 : Measure E3).restrict (Set.range F)) := by
  have hK : IsCompact (Set.range F) := isCompact_range he.continuous
  have hcon' : ContinuousOn h (F '' (Set.univ : Set SpherePoint)) :=
    he.isInducing.continuousOn_image_iff.mpr hc.continuousOn
  have hcon : ContinuousOn h (Set.range F) := by simpa only [image_univ] using hcon'
  exact hcon.integrableOn_of_subset_isCompact hK hK.measurableSet Subset.rfl hfinite.ne

/-- The actual cap-length construction supplies finite positive constant area.
The intersection witness is retained, so the same length can be used in the
metric, embedding, normal, and remaining enclosed-region constructions. -/
theorem IsometricGraphDevelopment.exists_markedSphereFamily_area {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R A.cRight L =
        capAttachingRim R A.cRight) ∧
      ∀ k ρ : ℝ, 0 < ρ → ρ < L / 64 → ∀ t : ℝ,
        0 < (Measure.euclideanHausdorffMeasure 2 : Measure E3)
          (Set.range (fun x : SpherePoint =>
            sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) ∧
        (Measure.euclideanHausdorffMeasure 2 : Measure E3)
          (Set.range (fun x : SpherePoint =>
            sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) < ⊤ ∧
        (Measure.euclideanHausdorffMeasure 2 : Measure E3)
          (Set.range (fun x : SpherePoint =>
            sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, t))) =
          (Measure.euclideanHausdorffMeasure 2 : Measure E3)
            (Set.range (fun x : SpherePoint =>
              sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L (x, 0))) := by
  obtain ⟨L, hL, hmeet, _⟩ := D.exists_fixed_cap_attachment hR
  refine ⟨L, hL, hmeet, ?_⟩
  intro k ρ hρ hsmall t
  exact ⟨D.markedSphereFamily_area_pos hR hL hρ hsmall t,
    D.markedSphereFamily_area_lt_top hR hL hρ hsmall t,
    D.markedSphereFamily_area_invariant hR hL hρ hsmall hmeet t⟩

end ContinuousFlexibility
