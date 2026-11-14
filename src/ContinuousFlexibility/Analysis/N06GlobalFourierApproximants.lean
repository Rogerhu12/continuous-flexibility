module

public import ContinuousFlexibility.Analysis.N06CanonicalCosineCutoff

/-!
# Actual global canonical Fourier approximants

The same centered Fourier cutoff is contractive in every original piece
measure. Applying it to all pieces therefore retains the original l2
height sequence. The three scalar coordinates are unchanged. These are
canonical unknowns even when they do not belong to the N05 graph, and
their piecewise strong limits are precisely the original unknown.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Analysis
open scoped Topology ENNReal

theorem n06CircleFourierCut_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (s : Finset ℤ)
    (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) :
    (∫ θ, (n06CircleFourierCut s f θ) ^ 2 ∂angleMeasure) ≤
      ∫ θ, f θ ^ 2 ∂angleMeasure := by
  let hP := memLp_angleMeasure_of_continuous (n06CircleFourierCut_contDiff s f).continuous
  have he : hP.toLp (n06CircleFourierCut s f) =
      circleFourierJetCutFun s 0 (hf.toLp f) := by
    simpa only [iteratedDeriv_zero] using n06CircleFourierCut_toLp hf s 0
  rw [← r11b_norm_toLp_sq hP, ← r11b_norm_toLp_sq hf, he]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (n06_circleFourierCut_norm_le s hs (hf.toLp f))

theorem n06CylinderFourierCut_sq_le {μ : Measure ℝ} [SFinite μ]
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (μ.prod angleMeasure))
    (s : Finset ℤ) (hs : ∀ n : ℤ, -n ∈ s ↔ n ∈ s) :
    (∫ p, (n06CylinderFourierCut s f p) ^ 2 ∂μ.prod angleMeasure) ≤
      ∫ p, f p ^ 2 ∂μ.prod angleMeasure := by
  have hP := n06CylinderFourierCut_memLp hf s
  rw [integral_prod _ hP.integrable_sq, integral_prod _ hf.integrable_sq]
  apply integral_mono_ae hP.integrable_sq.integral_prod_left hf.integrable_sq.integral_prod_left
  filter_upwards [r11b_memLp_product_sections hf] with r hr
  exact n06CircleFourierCut_sq_le hr s hs

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n06_canonicalFourierCut_memLp {m : ℕ}
    (U : CanonicalL2 S K m) (N : ℕ) :
    MemLp (n06CylinderFourierCut (n06FourierCutoff N) U) 2 (canonicalMeasure S K m) := by
  simpa only [spaces_mixedDerivative_zero] using
    n06_canonicalFourierCut_angularJet_memLp U (n06FourierCutoff N) 0

/-- The actual Fourier polynomial in the original piece L2 space. -/
def n06CanonicalFourierCutL2 {m : ℕ} (N : ℕ) (U : CanonicalL2 S K m) :
    CanonicalL2 S K m :=
  (n06_canonicalFourierCut_memLp U N).toLp
    (n06CylinderFourierCut (n06FourierCutoff N) U)

theorem n06CanonicalFourierCutL2_coe_ae {m : ℕ}
    (N : ℕ) (U : CanonicalL2 S K m) :
    (n06CanonicalFourierCutL2 N U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CylinderFourierCut (n06FourierCutoff N) U :=
  (n06_canonicalFourierCut_memLp U N).coeFn_toLp

theorem n06CanonicalFourierCutL2_norm_le {m : ℕ}
    (N : ℕ) (U : CanonicalL2 S K m) : ‖n06CanonicalFourierCutL2 N U‖ ≤ ‖U‖ := by
  have hu : ‖U‖ ^ 2 = ∫ p, U p ^ 2 ∂canonicalMeasure S K m := by
    simpa only [Lp.toLp_coeFn] using r11b_norm_toLp_sq (Lp.memLp U)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [n06CanonicalFourierCutL2, r11b_norm_toLp_sq, hu]
  exact (congrArg (fun μ : Measure PolarPoint =>
    (∫ p, (n06CylinderFourierCut (n06FourierCutoff N) U p) ^ 2 ∂μ) ≤
      ∫ p, U p ^ 2 ∂μ)
        (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr
          (n06CylinderFourierCut_sq_le (n06_canonicalL2_memLp_prod U)
            (n06FourierCutoff N) (n06FourierCutoff_neg N))

theorem n06CanonicalFourierCutL2_tendsto {m : ℕ} (U : CanonicalL2 S K m) :
    Tendsto (fun N => n06CanonicalFourierCutL2 N U) atTop (𝓝 U) := by
  have h := (r11b_tendsto_toLp_iff_integral_sq_sub
    (fun N => n06_canonicalFourierCut_memLp U N) (Lp.memLp U)).mpr
      (n06_canonicalFourierCut_error_tendsto U)
  simpa only [n06CanonicalFourierCutL2, Lp.toLp_coeFn] using h

/-- Even fields have exactly the finite cosine representatives used by
the genuine modal differential equations. -/
theorem n06CanonicalFourierCutL2_coe_cosine_ae {m : ℕ}
    (N : ℕ) (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ)) :
    (n06CanonicalFourierCutL2 N U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CylinderCosineCut N U := by
  apply (n06CanonicalFourierCutL2_coe_ae N U).trans
  simpa only [spaces_mixedDerivative_zero] using
    n06_canonicalFourierCut_angularJet_eq_cosine_ae U he N 0

/-- The same projection on every piece retains the true global l2
condition; no finite-piece support is imposed on the unknown. -/
def n06CanonicalFourierCutSequence (N : ℕ) (W : CanonicalL2Sequence S K) :
    CanonicalL2Sequence S K :=
  ⟨fun m => n06CanonicalFourierCutL2 N (W m),
    (lp.memℓp W).mono' (fun m => n06CanonicalFourierCutL2_norm_le N (W m))⟩

theorem n06CanonicalFourierCutSequence_apply (N : ℕ) (W : CanonicalL2Sequence S K) (m : ℕ) :
    n06CanonicalFourierCutSequence N W m = n06CanonicalFourierCutL2 N (W m) := rfl

theorem n06CanonicalFourierCutSequence_norm_le (N : ℕ) (W : CanonicalL2Sequence S K) :
    ‖n06CanonicalFourierCutSequence N W‖ ≤ ‖W‖ :=
  lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun m => n06CanonicalFourierCutL2_norm_le N (W m))

theorem n06CanonicalFourierCutSequence_piece_tendsto (W : CanonicalL2Sequence S K) (m : ℕ) :
    Tendsto (fun N => n06CanonicalFourierCutSequence N W m) atTop (𝓝 (W m)) :=
  n06CanonicalFourierCutL2_tendsto (W m)

/-- The original left-height, nu and compatibility scalars are retained. -/
def n06CanonicalUnknownFourierCut (N : ℕ) (U : CanonicalUnknown S K) :
    CanonicalUnknown S K := (n06CanonicalFourierCutSequence N U.1, U.2)

theorem n06CanonicalUnknownFourierCut_scalars (N : ℕ) (U : CanonicalUnknown S K) :
    (n06CanonicalUnknownFourierCut N U).2 = U.2 := rfl

theorem n06CanonicalUnknownFourierCut_height_tendsto (U : CanonicalUnknown S K) (m : ℕ) :
    Tendsto (fun N => (n06CanonicalUnknownFourierCut N U).1 m) atTop (𝓝 (U.1 m)) :=
  n06CanonicalFourierCutSequence_piece_tendsto U.1 m

end ContinuousFlexibility.Statements
