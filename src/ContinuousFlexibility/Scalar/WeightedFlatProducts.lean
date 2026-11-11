import ContinuousFlexibility.Scalar.WeightedFieldRegularity

/-!
# Multiplication preserves the actual uniform flat jets

Each ordinary jet of a smooth factor is bounded on the closed physical
rectangle.  The product rule and induction on the two derivative orders
therefore preserve every endpoint decay order.  This argument uses the
actual derivatives and does not introduce a new jet representation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

private def scalarFlatValue (D : ReferenceData) (f : PolarPoint → ℝ) : Prop :=
  ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ r θ, r ∈ Ioo D.a D.b → θ ∈ Icc (0 : ℝ) Real.pi →
      endpointDistance D r < δ → |endpointDistance D r ^ (-(k : ℤ)) * f (r, θ)| < ε

private theorem scalarFlatValue_add {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : scalarFlatValue D f) (hg : scalarFlatValue D g) :
    scalarFlatValue D (fun p => f p + g p) := by
  intro k ε hε
  obtain ⟨δf, hδf, hfb⟩ := hf k (ε / 2) (half_pos hε)
  obtain ⟨δg, hδg, hgb⟩ := hg k (ε / 2) (half_pos hε)
  refine ⟨min δf δg, lt_min hδf hδg, fun r θ hr hθ hnear => ?_⟩
  rw [mul_add]
  exact (abs_add_le _ _).trans_lt (by
    have h₁ := hfb r θ hr hθ (hnear.trans_le (min_le_left _ _))
    have h₂ := hgb r θ hr hθ (hnear.trans_le (min_le_right _ _))
    linarith only [h₁, h₂])

private theorem scalarFlatValue_mul_continuous {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : scalarFlatValue D f) (hg : Continuous g) :
    scalarFlatValue D (fun p => f p * g p) := by
  have hcompact : IsCompact (Icc D.a D.b ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hg.abs.continuousOn
  let C : ℝ := max M 0 + 1
  have hC : 0 < C := by dsimp only [C]; linarith only [le_max_right M 0]
  intro k ε hε
  obtain ⟨δ, hδ, hb⟩ := hf k (ε / C) (div_pos hε hC)
  refine ⟨δ, hδ, fun r θ hr hθ hnear => ?_⟩
  have hgBound : |g (r, θ)| ≤ C := by
    apply (hM ⟨(r, θ), ⟨⟨hr.1.le, hr.2.le⟩, hθ⟩, rfl⟩).trans
    exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  calc
    _ = |endpointDistance D r ^ (-(k : ℤ)) * f (r, θ)| * |g (r, θ)| := by
      rw [← mul_assoc, abs_mul]
    _ ≤ |endpointDistance D r ^ (-(k : ℤ)) * f (r, θ)| * C :=
      mul_le_mul_of_nonneg_left hgBound (abs_nonneg _)
    _ < (ε / C) * C := mul_lt_mul_of_pos_right (hb r θ hr hθ hnear) hC
    _ = ε := div_mul_cancel₀ ε hC.ne'

theorem UniformFlatJets.radialPartial {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : UniformFlatJets D f) (hcf : ContDiff ℝ ∞ f) :
    UniformFlatJets D (radialPartial f) := by
  intro a b k ε hε
  obtain ⟨δ, hδ, hb⟩ := hf (a + 1) b k ε hε
  refine ⟨δ, hδ, fun r θ hr hθ hnear => ?_⟩
  rw [mixedDerivative_radialPartial isOpen_univ hcf.contDiffOn a b (mem_univ _)]
  exact hb r θ hr hθ hnear

private theorem scalarFlatValue_mixed_mul {D : ReferenceData} (a b : ℕ)
    {f g : PolarPoint → ℝ} (hf : UniformFlatJets D f)
    (hcf : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) :
    scalarFlatValue D (mixedDerivative a b (fun p => f p * g p)) := by
  induction a generalizing f g with
  | zero =>
    induction b generalizing f g with
    | zero =>
      have hflat : scalarFlatValue D f := by
        simpa only [scalarFlatValue, mixedDerivative, iteratedDeriv_zero] using hf 0 0
      have he : mixedDerivative 0 0 (fun p => f p * g p) = (fun p => f p * g p) := by
        funext p
        simp only [mixedDerivative, iteratedDeriv_zero]
      rw [he]
      exact scalarFlatValue_mul_continuous hflat hcg.continuous
    | succ b ih =>
      have hcfθ : ContDiff ℝ ∞ (angularPartial f) :=
        contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hcf.contDiffAt (by simp)
      have hcgθ : ContDiff ℝ ∞ (angularPartial g) :=
        contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hcg.contDiffAt (by simp)
      have hprod : angularPartial (fun p => f p * g p) =
          fun p => angularPartial f p * g p + f p * angularPartial g p := by
        funext p
        exact angularPartial_mul (hcf.differentiable (by simp) p) (hcg.differentiable (by simp) p)
      have he : mixedDerivative 0 (b + 1) (fun p => f p * g p) =
          fun p => mixedDerivative 0 b (fun q => angularPartial f q * g q) p +
            mixedDerivative 0 b (fun q => f q * angularPartial g q) p := by
        funext p
        rw [← mixedDerivative_angularPartial isOpen_univ (hcf.mul hcg).contDiffOn
          0 b (mem_univ p), hprod,
          mixedDerivative_add_of_contDiff (hcfθ.mul hcg) (hcf.mul hcgθ)]
      rw [he]
      exact scalarFlatValue_add (ih (hf.angularPartial hcf) hcfθ hcg) (ih hf hcf hcgθ)
  | succ a ih =>
    have hcfr : ContDiff ℝ ∞ (radialPartial f) :=
      contDiff_iff_contDiffAt.mpr fun p => contDiffAt_radialPartial hcf.contDiffAt (by simp)
    have hcgr : ContDiff ℝ ∞ (radialPartial g) :=
      contDiff_iff_contDiffAt.mpr fun p => contDiffAt_radialPartial hcg.contDiffAt (by simp)
    have hprod : radialPartial (fun p => f p * g p) =
        fun p => radialPartial f p * g p + f p * radialPartial g p := by
      funext p
      exact radialPartial_mul (hcf.differentiable (by simp) p) (hcg.differentiable (by simp) p)
    have he : mixedDerivative (a + 1) b (fun p => f p * g p) =
        fun p => mixedDerivative a b (fun q => radialPartial f q * g q) p +
          mixedDerivative a b (fun q => f q * radialPartial g q) p := by
      funext p
      rw [← mixedDerivative_radialPartial isOpen_univ (hcf.mul hcg).contDiffOn
        a b (mem_univ p), hprod,
        mixedDerivative_add_of_contDiff (hcfr.mul hcg) (hcf.mul hcgr)]
    rw [he]
    exact scalarFlatValue_add (ih (hf.radialPartial hcf) hcfr hcg) (ih hf hcf hcgr)

/-- Every smooth multiplier preserves uniform flatness on the physical
rectangle.  The multiplier need not vanish or be globally bounded. -/
theorem UniformFlatJets.mul_smooth {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : UniformFlatJets D f) (hcf : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) :
    UniformFlatJets D (fun p => f p * g p) := by
  intro a b
  exact scalarFlatValue_mixed_mul a b hf hcf hcg

end ContinuousFlexibility.Statements
