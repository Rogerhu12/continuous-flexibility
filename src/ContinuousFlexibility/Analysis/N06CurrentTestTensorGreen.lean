module

public import ContinuousFlexibility.Analysis.N06CurrentTestTraceCalculus
public import ContinuousFlexibility.Analysis.N06CurrentCubicTestPairing
public import ContinuousFlexibility.Analysis.N06NegativeBulkLimits

/-!
# Closed tensor Green identities against actual current tests

The transformed test is smooth only on the open canonical strip. Its
closed radial value and first jet are the genuine Lipschitz traces already
constructed from the N04 forward chart. Radial Green therefore retains
the actual endpoint terms, while angular integration by parts uses only
the open strip and the genuine half-period symmetry.

All integrals use the original, unnormalized canonical half-period
measure. No boundary smoothness of the totalized inverse chart is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A radial L2 function times a continuous angular function belongs to
the original canonical L2 space on any recorded finite interval. -/
theorem n06_canonical_tensor_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ} {v e : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (he : Continuous e) :
    MemLp (fun p : PolarPoint => v p.1 * e p.2) 2 (canonicalMeasure S K m) := by
  rw [n06_canonicalMeasure_eq_radial_prod]
  exact r11b_memLp_tensor hv (memLp_angleMeasure_of_continuous he)

/-- A continuous radial coefficient is an L2 multiplier on each actual
finite canonical piece; no uniform estimate over pieces is asserted. -/
theorem n06_canonical_radialWeight_mul_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {w : ℝ → ℝ} {f : PolarPoint → ℝ} (hw : Continuous w)
    (hf : MemLp f 2 (canonicalMeasure S K m)) :
    MemLp (fun p => w p.1 * f p) 2 (canonicalMeasure S K m) := by
  have hm : AEStronglyMeasurable (fun p : PolarPoint => w p.1)
      (canonicalMeasure S K m) := (hw.comp continuous_fst).aestronglyMeasurable
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (show ContinuousOn (fun y => ‖w y‖) (Icc (K.left m) (K.right m)) from
      hw.norm.continuousOn)
  have htop : MemLp (fun p : PolarPoint => w p.1) ∞ (canonicalMeasure S K m) := by
    apply memLp_top_of_bound hm M
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact hM ⟨p.1, mem_Icc_of_Ioo hp.1, rfl⟩
  exact htop.fun_mul hf

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The actual current height test has the ordinary second angular
derivative on every interior radial slice. -/
theorem n06_currentHeight_angular_second_slice
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {y : ℝ}
    (hy : y ∈ Ioo (K.left m) (K.right m)) :
    iteratedDeriv 2 (fun θ => canonicalHeight S K z m φ (y, θ)) =
      fun θ => angularPartial (angularPartial (canonicalHeight S K z m φ)) (y, θ) := by
  have hW := n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ
  have hjet (θ : ℝ) : ContDiffAt ℝ ∞ (canonicalHeight S K z m φ) (y, θ) :=
    hW.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩)
  have hd : deriv (fun θ => canonicalHeight S K z m φ (y, θ)) =
      fun θ => angularPartial (canonicalHeight S K z m φ) (y, θ) := by
    funext θ
    exact (hasDerivAt_angularSlice ((hjet θ).differentiableAt (by simp))).deriv
  have hdd : deriv (fun θ => angularPartial (canonicalHeight S K z m φ) (y, θ)) =
      fun θ => angularPartial (angularPartial (canonicalHeight S K z m φ)) (y, θ) := by
    funext θ
    exact (hasDerivAt_angularSlice
      ((contDiffAt_angularPartial (hjet θ) (m := ∞) (by simp)).differentiableAt
        (by simp))).deriv
  simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_one, iteratedDeriv_zero, hd]
    using hdd

/-- Radial H2 Green against a genuine current test, with both endpoint
Wronskians retained. Angular factors require only continuity here. -/
theorem N06CurrentHeightTestTraces.tensor_radial_green
    (P : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {v e : ℝ → ℝ}
    (hC : ContDiff ℝ 1 v)
    (hAC : AbsolutelyContinuousOnInterval (deriv v) (K.left m) (K.right m))
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (hv₂ : MemLp (deriv (deriv v)) 2
      (volume.restrict (Ioo (K.left m) (K.right m)))) (he : Continuous e) :
    (∫ p, (deriv (deriv v) p.1 * e p.2) * canonicalHeight S K z m φ p
      ∂canonicalMeasure S K m) -
      (∫ p, (v p.1 * e p.2) *
        radialPartial (radialPartial (canonicalHeight S K z m φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi, e θ *
        ((P.value (K.right m, θ) * deriv v (K.right m) -
          v (K.right m) * P.radial (K.right m, θ)) -
        (P.value (K.left m, θ) * deriv v (K.left m) -
          v (K.left m) * P.radial (K.left m, θ))) := by
  have hab : K.left m ≤ K.right m := (h04.1.referenceBounds m).2.1.le
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hWrr := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).1
  have hI : Integrable (fun p : PolarPoint =>
      (deriv (deriv v) p.1 * e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hv₂ he).integrable_mul hW
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) *
      radialPartial (radialPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hv he).integrable_mul hWrr
  rw [← integral_sub hI hJ]
  have hIJ : Integrable (fun p : PolarPoint =>
      (deriv (deriv v) p.1 * e p.2) * canonicalHeight S K z m φ p -
        (v p.1 * e p.2) * radialPartial (radialPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) := hI.sub hJ
  rw [n06_canonicalMeasure_eq_radial_prod] at hIJ ⊢
  rw [integral_prod_symm _ hIJ, intervalIntegral.integral_of_le Real.pi_pos.le]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change (∫ y in Ioo (K.left m) (K.right m),
    (deriv (deriv v) y * e θ) * canonicalHeight S K z m φ (y, θ) -
      (v y * e θ) * radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ)) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  calc
    _ = e θ * (∫ y in K.left m..K.right m,
        deriv (deriv v) y * canonicalHeight S K z m φ (y, θ) -
          v y * radialPartial (radialPartial (canonicalHeight S K z m φ)) (y, θ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ = _ := by rw [P.radial_slice_green h04 hz hs hφ hC hAC hθ]

/-- On the angular factor, two integrations by parts require only the
actual open-strip smoothness and pi-periodicity. No endpoint extension is
needed, and the radial factor is only L2. -/
theorem n06_currentHeight_tensor_angular_green
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi))
    {v e : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo (K.left m) (K.right m))))
    (he : ContDiff ℝ ∞ e) (hep : Function.Periodic e Real.pi) :
    (∫ p, (v p.1 * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p
      ∂canonicalMeasure S K m) =
      ∫ p, (v p.1 * e p.2) *
        angularPartial (angularPartial (canonicalHeight S K z m φ)) p
          ∂canonicalMeasure S K m := by
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hWtt := (n06_current_canonicalHeight_second_memLp h04 hz hs m hφ).2
  have hI : Integrable (fun p : PolarPoint =>
      (v p.1 * iteratedDeriv 2 e p.2) * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hv
        (circleFourier_contDiff_iteratedDeriv he 2).continuous).integrable_mul hW
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) *
      angularPartial (angularPartial (canonicalHeight S K z m φ)) p)
      (canonicalMeasure S K m) := (n06_canonical_tensor_memLp hv he.continuous).integrable_mul hWtt
  rw [n06_canonicalMeasure_eq_radial_prod] at hI hJ ⊢
  rw [integral_prod _ hI, integral_prod _ hJ]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hWopen := n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ
  have hslice : ContDiff ℝ ∞ (fun θ => canonicalHeight S K z m φ (y, θ)) :=
    hWopen.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨hy, mem_univ _⟩)
  have hperiod : Function.Periodic
      (fun θ => canonicalHeight S K z m φ (y, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      n06_current_canonicalHeight_periodic_on h04 hz hs m hφp
        (p := (y, θ)) ⟨hy, mem_univ _⟩
  have hbase := integral_angle_iteratedDeriv_mul he hep 2 hslice hperiod
  rw [n06_currentHeight_angular_second_slice h04 hz hs hφ hy] at hbase
  norm_num only [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul] at hbase
  change (∫ θ, (v y * iteratedDeriv 2 e θ) * canonicalHeight S K z m φ (y, θ)
    ∂angleMeasure) = ∫ θ, (v y * e θ) *
      angularPartial (angularPartial (canonicalHeight S K z m φ)) (y, θ) ∂angleMeasure
  simp only [mul_assoc, integral_const_mul]
  exact congrArg (fun t : ℝ => v y * t) hbase

end ContinuousFlexibility.Statements
