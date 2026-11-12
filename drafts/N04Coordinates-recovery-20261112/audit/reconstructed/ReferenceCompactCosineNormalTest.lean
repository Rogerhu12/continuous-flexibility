import ContinuousFlexibility.Analysis.N07bReferenceGraphFromDecay
import ContinuousFlexibility.Analysis.N01aReferenceNormalWeighted
import ContinuousFlexibility.Radial.ReferenceSmoothSourceCalculus
import ContinuousFlexibility.Radial.ReferenceColumnSmooth
import ContinuousFlexibility.Radial.R11bCompactSources

/-!
# Genuine compact cosine tests for the same reference inverse

The forcing is the actual radial Jacobi expression of a compact smooth
radial function.  Its scalar source datum is the actual border row.  Green's
identity puts this pair in the original graph, so uniqueness identifies it
with the supplied inverse.  The original first-normal constant then bounds
the ordinary derivative of every such test, uniformly before its choice.
No pointwise optical lower bound or replacement reference is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def referenceCompactCosine (u : ℝ → ℝ) (p : PolarPoint) : ℝ :=
  u p.1 * cosineMode 2 p.2

def referenceCompactCosineSource (D : ReferenceData) (u : ℝ → ℝ) : RadialSource :=
  (referenceCompactCosine (radialJacobi 4 D.w u), referenceRow D (referenceCompactCosine u))

private theorem compactJacobi_contDiff {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (radialJacobi 4 D.w u) := by
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hflux : ContDiff ℝ ∞ (deriv (fun r => D.w r * deriv u r)) :=
    (contDiff_infty_iff_deriv.mp (hgeom.2.2.1.1.mul hdu)).2
  change ContDiff ℝ ∞ (fun r =>
    deriv (fun t => D.w t * deriv u t) r - 4 * deriv D.w r / r * u r)
  simp_rw [mul_div_assoc]
  exact hflux.sub ((contDiff_const.mul
    (reference_contDiff_flat_deriv_div hgeom.1 hgeom.2.2.1)).mul hu)

private theorem compactJacobi_tsupport {D : ReferenceData} (u : ℝ → ℝ) :
    tsupport (radialJacobi 4 D.w u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro r hr
  by_contra hnot
  have hfluxSupport : tsupport (fun t => D.w t * deriv u t) ⊆ tsupport u :=
    tsupport_mul_subset_right.trans tsupport_deriv_subset
  have hflux : deriv (fun t => D.w t * deriv u t) r = 0 :=
    deriv_of_notMem_tsupport (fun h => hnot (hfluxSupport h))
  exact hr (by simp only [radialJacobi, hflux, image_eq_zero_of_notMem_tsupport hnot,
    mul_zero, sub_zero])

private theorem compactCosine_smoothSource {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ radialCore D) :
    ReferenceSmoothFiniteSource D (referenceCompactCosineSource D u) := by
  classical
  refine ⟨{0}, (fun _ => 0), (fun _ => radialJacobi 4 D.w u), ?_, ?_, ?_, ?_⟩
  · refine ⟨contDiff_const, ?_, ?_⟩
    · change IsCompact (tsupport (fun _ : ℝ => (0 : ℝ)))
      simp only [tsupport_zero, isCompact_empty]
    · simp only [tsupport_zero, empty_subset]
  · intro n hn
    exact ⟨compactJacobi_contDiff hD.choose_spec.1 hu,
      hc.of_isClosed_subset (isClosed_tsupport _) (compactJacobi_tsupport u),
      (compactJacobi_tsupport u).trans hs⟩
  · exact intervalIntegral.integral_zero
  · intro r θ
    simp only [referenceCompactCosineSource, referenceCompactCosine,
      Finset.sum_singleton, zero_add, Nat.zero_add, Nat.mul_one]

/-- Compact second-mode tests satisfy the actual graph, including its true
border row, for every fixed pair of cell weights. -/
theorem referenceCompactCosine_graph {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ radialCore D) (γ M₀ M₁ : ℝ) :
    ReferenceGraph D γ M₀ M₁ (referenceCompactCosine u, 0)
      (referenceCompactCosineSource D u) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hcos : ContDiff ℝ ∞ (cosineMode 2) := r11b_contDiff_cosineMode 2
  have huc : ContDiff ℝ ∞ (referenceCompactCosine u) :=
    (hu.comp contDiff_fst).mul (hcos.comp contDiff_snd)
  have hout := r11b_compact_output_cell_summable hD hc hs huc.continuous
    (fun r _ hr θ => by
      simp only [referenceCompactCosine, image_eq_zero_of_notMem_tsupport hr, zero_mul]) γ M₁
  have hreal : OutputRealization D γ M₁ 0 (referenceCompactCosine u, 0) :=
    outputRealization_cosine_lift_of_summable hpart hu.continuous hout.2
  have hsource := (compactCosine_smoothSource hD hu hc hs).sourceMember hD γ M₀
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have heq : EqOn (referenceCompactCosineSource D u).1
      (fun p => radialPDE D.w (fun r θ => referenceCompactCosine u (r, θ)) p.1 p.2 +
        (0 : ℝ) * referenceColumn D p.1 * cosineMode 2 p.2) (annularOpen D) := by
    intro p hp
    have he := radialPDE_cosine_lift (w := D.w) (u := u) (r := p.1) (θ := p.2) 2
      (Eventually.of_forall (hu.differentiable (by simp)))
      ((hgeom.2.2.1.1.mul hdu).differentiable (by simp) p.1)
    simpa only [referenceCompactCosineSource, referenceCompactCosine, Nat.cast_ofNat,
      show (2 : ℝ) ^ 2 = 4 by norm_num, zero_mul, add_zero] using he.symm
  refine ⟨⟨0, hreal⟩, hsource, rfl, ?_⟩
  intro ψ hψ
  exact n07b_c2_reference_weak_of_eqOn hgeom hborder (huc.of_le (by simp))
    hreal.2.2.1 heq hψ

/-- The normal estimate of the supplied inverse controls the genuine
ordinary derivatives of all compact radial tests, with one original
constant chosen before the radial test. -/
theorem FirstNormalInverseEstimate.compactCosine_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ radialCore D →
      RadialRepresentativeEq D (G (referenceCompactCosineSource D u))
        (referenceCompactCosine u, 0) ∧
      OutputRealization D γ M₁ 0 (referenceCompactCosine (deriv u), 0) ∧
      outputNormSquare D γ M₁ 0 (referenceCompactCosine (deriv u), 0) ≤
        C ^ 2 * (sourceNormSquare D γ M₀ (referenceCompactCosineSource D u) +
          sourceNormSquare D γ M₀ (angularPartial (referenceCompactCosineSource D u).1, 0)) := by
  obtain ⟨C, hC, hbound⟩ := hNormal
  refine ⟨C, hC, ?_⟩
  intro u hu hc hs
  let F : RadialSource := referenceCompactCosineSource D u
  have hfinite : ReferenceSmoothFiniteSource D F := compactCosine_smoothSource hD hu hc hs
  have hgraph := referenceCompactCosine_graph hD hborder hu hc hs γ M₀ M₁
  have he : RadialRepresentativeEq D (G F) (referenceCompactCosine u, 0) :=
    hG.2.1 _ F hgraph
  obtain ⟨ur, hweak, hreal, hnorm⟩ := hbound F (angularPartial F.1)
    (hfinite.sourceMember hD γ M₀)
    (weakAngularDerivative_of_contDiff hfinite.contDiff (hfinite.radialTest hD).2.1)
    (hfinite.sourceDerivativeMember hD γ M₀)
  have hmode : referenceMode (G F).1 2 =ᵐ[volume.restrict (radialCore D)] u := by
    apply (referenceMode_congr_ae he.2 2).trans
    exact Eventually.of_forall fun r => by
      simpa only [referenceCompactCosine, ite_true, mul_one] using
        referenceMode_cosine_field u 2 2 (by decide) (by decide) r
  -- Only the unused phi slot of the elementary projection lemma is changed.
  -- All measures, weights, weak equations, the graph and G remain those of D.
  let Dtest : ReferenceData := { D with phi := u }
  have hflat : EndpointFlat Dtest Dtest.phi := by
    refine ⟨hu, ?_⟩
    intro r hr
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    rcases hr with hl | hr
    · exact (not_lt_of_ge hl) (hs hmem).1
    · exact (not_lt_of_ge hr) (hs hmem).2
  have hpart : RadialPartition Dtest := hD.choose_spec.2.1
  have hab : Dtest.a ≤ Dtest.b := hD.choose_spec.1.2.1.le
  have hderiv : OutputRealization D γ M₁ 0 (referenceCompactCosine (deriv u), 0) :=
    weakNormalDerivative_reference_output (D := Dtest) hab hpart hflat hweak hmode hreal
  have hcells : RadialCellIntegrable Dtest ur := by
    simpa only [outputRemainder, zero_mul, sub_zero] using hreal.1
  have hweighted (m : ℕ) :
      outputCellSquare D γ M₁ (referenceCompactCosine (deriv u)) m ≤
        outputCellSquare D γ M₁ ur m := by
    exact mul_le_mul_of_nonneg_left
      (weakNormalDerivative_reference_cell_square_le
        (D := Dtest) hab hpart hflat hweak hmode hcells m) (Real.exp_pos _).le
  have hds : Summable (outputCellSquare D γ M₁ (referenceCompactCosine (deriv u))) := by
    simpa only [outputRemainder, zero_mul, sub_zero] using hderiv.2.1
  have hus : Summable (outputCellSquare D γ M₁ ur) := by
    simpa only [outputRemainder, zero_mul, sub_zero] using hreal.2.1
  have hnormle : outputNormSquare D γ M₁ 0 (referenceCompactCosine (deriv u), 0) ≤
      outputNormSquare D γ M₁ 0 (ur, 0) := by
    simpa only [outputNormSquare, outputRemainder, zero_mul, sub_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add] using hds.tsum_le_tsum hweighted hus
  exact ⟨he, hderiv, hnormle.trans hnorm⟩

end ContinuousFlexibility.Statements
