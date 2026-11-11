import ContinuousFlexibility.Radial.ReferenceRadialJetBootstrap

/-!
# Compact forcing and flat scalar inverse images

A smooth radial forcing supported strictly inside the core belongs to every
scalar weighted space, because only finitely many cells meet its support.
The actual radial equation and the first-normal weighted bound therefore
give a smooth flat extension of each nonzero-mode solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Core-supported continuous radial fields belong to every weighted
space. Values outside the physical core play no role in the norm. -/
theorem referenceRadialWeighted_of_compact_core {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (hf : Continuous f) {K : Set ℝ} (hK : IsCompact K)
    (hKs : K ⊆ radialCore D)
    (hz : ∀ r ∈ radialCore D, r ∉ K → f r = 0)
    (γ A : ℝ) : ReferenceRadialWeighted D γ A f := by
  obtain ⟨C, _, hp, _, _, _, hcompact, _⟩ := hD
  let μ : Measure ℝ := volume.restrict (radialCore D)
  letI : IsFiniteMeasure μ := by dsimp only [μ, radialCore]; infer_instance
  have hlocal (m : ℕ) : MemLp (fun r => D.localizer m r * f r) 2 μ := by
    have hc : Continuous (fun r => D.localizer m r * f r) := (hp.1 m).continuous.mul hf
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
      (hc.norm.continuousOn (s := Icc D.a D.b))
    apply MemLp.of_bound hc.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hB ⟨r, Ioo_subset_Icc_self hr, rfl⟩
  refine ⟨hlocal, ?_⟩
  have hfinite := hcompact K hK hKs
  apply summable_of_hasFiniteSupport
  apply hfinite.subset
  intro m hm
  by_contra hnot
  change ¬(D.cells m ∩ K).Nonempty at hnot
  have hzero :
      (fun r => (D.localizer m r * f r) ^ 2) =ᵐ[volume.restrict (radialCore D)]
        fun _ => (0 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    by_cases hχ : D.localizer m r = 0
    · simp only [hχ, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · have hrCell : r ∈ D.cells m := hp.2.2.1 m hχ
      have hrK : r ∉ K := fun hrK => hnot ⟨r, hrCell, hrK⟩
      rw [hz r hr hrK, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hi : (∫ r, (D.localizer m r * f r) ^ 2
      ∂volume.restrict (radialCore D)) = 0 := by
    rw [integral_congr_ae hzero, integral_zero]
  apply hm
  change exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    (∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D)) = 0
  rw [hi, mul_zero]

theorem referenceRadialWeighted_of_compact_support {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ radialCore D)
    (γ A : ℝ) : ReferenceRadialWeighted D γ A f :=
  referenceRadialWeighted_of_compact_core hD hf hfc hfs
    (fun _ _ hr => image_eq_zero_of_notMem_tsupport hr) γ A

theorem referenceRapid_compact_jets {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ radialCore D) (n : ℕ) :
    ReferenceRapid D (iteratedDeriv n f) := by
  have hsmooth : ContDiff ℝ ∞ (iteratedDeriv n f) :=
    contDiffOn_univ.mp (reference_contDiffOn_iteratedDeriv isOpen_univ hf.contDiffOn n)
  have hsupp (n : ℕ) : HasCompactSupport (iteratedDeriv n f) ∧
      tsupport (iteratedDeriv n f) ⊆ radialCore D := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using (show HasCompactSupport f ∧
        tsupport f ⊆ radialCore D from ⟨hfc, hfs⟩)
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ⟨ih.1.deriv, tsupport_deriv_subset.trans ih.2⟩
  exact ⟨1, 0, zero_lt_one,
    referenceRadialWeighted_of_compact_support hD hsmooth.continuous (hsupp n).1 (hsupp n).2 1 0⟩

/-- All higher endpoint estimates follow from the genuine equation and
the two weighted bounds already supplied by the inverse and first-normal
estimate. No endpoint value is assumed. -/
theorem reference_radial_smooth_zero_extension {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u f : ℝ → ℝ} {J : ℝ}
    (hu : ContDiffOn ℝ ∞ u (radialCore D))
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ radialCore D)
    (he : ∀ r ∈ radialCore D, radialJacobi J D.w u r = f r)
    (huW : ReferenceRapid D u) (hdW : ReferenceRapid D (deriv u)) :
    ContDiff ℝ ∞ (Analysis.extendZeroOutside D.a D.b u) := by
  apply reference_contDiff_zero_extension_of_weighted_jets hD hu
  intro n
  exact reference_radial_jets_rapid hD hu hf.contDiffOn he huW hdW
    (referenceRapid_compact_jets hD hf hfc hfs) n

end ContinuousFlexibility.Radial
