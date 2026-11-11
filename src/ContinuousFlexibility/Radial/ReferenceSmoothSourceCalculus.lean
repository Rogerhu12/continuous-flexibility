import ContinuousFlexibility.Radial.ReferenceGraphProjection
import ContinuousFlexibility.Radial.ReferenceSmoothSources
import ContinuousFlexibility.Radial.ReferenceRadialSmoothExtension

/-!
# Differential and finite-spectrum properties of smooth core sources

The finite-source predicate supplies an actual smooth polar field, compact
radial support for every coefficient, a finite projection fixing the
field, and a legitimate first-normal input using its ordinary angular
derivative.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

theorem ReferenceSmoothFiniteSource.contDiff {D : ReferenceData} {F : RadialSource}
    (hF : ReferenceSmoothFiniteSource D F) : ContDiff ℝ ∞ F.1 := by
  obtain ⟨J, f₀, f, h₀, hf, _, heq⟩ := hF
  have he : F.1 = fun x : PolarPoint =>
      f₀ x.1 + ∑ n ∈ J, f n x.1 * referenceAngularBasis (n + 1) x.2 :=
    funext fun x => heq x.1 x.2
  rw [he]
  apply (h₀.1.comp contDiff_fst).add
  apply ContDiff.sum
  intro n hn
  exact ((hf n hn).1.comp contDiff_fst).mul
    ((contDiff_referenceAngularBasis (n + 1)).comp contDiff_snd)

theorem ReferenceSmoothFiniteSource.radialTest {D : ReferenceData} {F : RadialSource}
    (hF : ReferenceSmoothFiniteSource D F) (hD : IsAccumulatingProfile D) :
    RadialTest D F.1 :=
  ⟨hF.contDiff, reference_periodic_two_pi (hF.sourceMember hD 0 0).2.2.1,
    hF.radialCompactSupport⟩

theorem ReferenceSmoothFiniteSource.coefficient_compact {D : ReferenceData} {F : RadialSource}
    (hF : ReferenceSmoothFiniteSource D F) (hD : IsAccumulatingProfile D) (n : ℕ) :
    ContDiff ℝ ∞ (referenceRadialCoefficient F.1 n) ∧
      HasCompactSupport (referenceRadialCoefficient F.1 n) ∧
      tsupport (referenceRadialCoefficient F.1 n) ⊆ radialCore D :=
  ⟨contDiff_referenceRadialCoefficient hF.contDiff n,
    referenceRadialCoefficient_compact_support (hF.radialTest hD) n⟩

theorem ReferenceSmoothFiniteSource.coefficient_jets_rapid {D : ReferenceData} {F : RadialSource}
    (hF : ReferenceSmoothFiniteSource D F) (hD : IsAccumulatingProfile D) (n k : ℕ) :
    ReferenceRapid D (iteratedDeriv k (referenceRadialCoefficient F.1 n)) := by
  obtain ⟨hs, hc, hcore⟩ := hF.coefficient_compact hD n
  exact referenceRapid_compact_jets hD hs hc hcore k

theorem angularBasisProjection_constant_add_cosines (I J : Finset ℕ)
    (h0 : 0 ∈ I) (hJ : J.image Nat.succ ⊆ I) (c₀ : ℝ) (c : ℕ → ℝ) :
    angularBasisProjection I
      (fun θ => c₀ + ∑ n ∈ J, c n * referenceAngularBasis (n + 1) θ) =
        (fun θ => c₀ + ∑ n ∈ J, c n * referenceAngularBasis (n + 1) θ) := by
  have he : (fun θ => ∑ n ∈ J, c n * referenceAngularBasis (n + 1) θ) =
      (fun θ => ∑ n ∈ J.image Nat.succ, c (n - 1) * referenceAngularBasis n θ) := by
    funext θ
    rw [Finset.sum_image]
    · simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    · intro a _ha b _hb hab
      exact Nat.succ.inj hab
  have hsum := memLp_referenceAngular_interval_of_continuous
    (continuous_sum_referenceAngularBasis (J.image Nat.succ) (fun n => c (n - 1)))
  rw [he, angularBasisProjection_add
    (memLp_referenceAngular_interval_of_continuous continuous_const) hsum I,
    angularBasisProjection_const h0,
    angularBasisProjection_sum_basis I (J.image Nat.succ) hJ]

theorem ReferenceSmoothFiniteSource.exists_fixed_projection {D : ReferenceData}
    {F : RadialSource} (hF : ReferenceSmoothFiniteSource D F) :
    ∃ I : Finset ℕ, 0 ∈ I ∧ 1 ∈ I ∧ referenceBasisProjection I F.1 = F.1 := by
  classical
  obtain ⟨J, f₀, f, _, _, _, heq⟩ := hF
  let I : Finset ℕ := insert 0 (insert 1 (J.image Nat.succ))
  have h0 : 0 ∈ I := Finset.mem_insert_self _ _
  have h1 : 1 ∈ I := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hJ : J.image Nat.succ ⊆ I :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  refine ⟨I, h0, h1, ?_⟩
  funext x
  have he : (fun θ => F.1 (x.1, θ)) =
      (fun θ => f₀ x.1 + ∑ n ∈ J, f n x.1 * referenceAngularBasis (n + 1) θ) :=
    funext fun θ => heq x.1 θ
  change angularBasisProjection I (fun θ => F.1 (x.1, θ)) x.2 = F.1 x
  rw [he, angularBasisProjection_constant_add_cosines I J h0 hJ]
  exact (heq x.1 x.2).symm

/-- Ordinary smooth angular differentiation satisfies the frozen weak
definition, by integration by parts over the actual angular period. -/
theorem weakAngularDerivative_of_contDiff {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u (0, 2 * Real.pi)) :
    WeakAngularDerivative D u (angularPartial u) := by
  intro ψ hψ
  have hud : ContDiff ℝ ∞ (angularPartial u) := r11b_contDiff_directionalPartial hu (0, 1)
  have hψd : ContDiff ℝ ∞ (angularPartial ψ) := r11b_contDiff_directionalPartial hψ.1 (0, 1)
  have he (r : ℝ) :
      radialAngularMean (fun θ => u (r, θ) * angularPartial ψ (r, θ)) =
        -radialAngularMean (fun θ => angularPartial u (r, θ) * ψ (r, θ)) := by
    have hub : u (r, 2 * Real.pi) = u (r, 0) := by
      simpa only [Prod.fst_add, Prod.snd_add, add_zero, zero_add] using hp (r, 0)
    have hψb : ψ (r, 2 * Real.pi) = ψ (r, 0) := by
      simpa only [Prod.fst_add, Prod.snd_add, add_zero, zero_add] using hψ.2.1 (r, 0)
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := fun θ => u (r, θ)) (v := fun θ => ψ (r, θ))
      (u' := fun θ => angularPartial u (r, θ))
      (v' := fun θ => angularPartial ψ (r, θ))
      (fun θ _ => hasDerivAt_angular_slice (hu.differentiable (by simp) (r, θ)))
      (fun θ _ => hasDerivAt_angular_slice (hψ.1.differentiable (by simp) (r, θ)))
      ((hud.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hψd.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    rw [hub, hψb, sub_self, zero_sub] at h
    unfold radialAngularMean
    rw [h, mul_neg]
  simp_rw [he]
  exact intervalIntegral.integral_neg _

theorem ReferenceSmoothFiniteSource.sourceDerivativeMember {D : ReferenceData}
    {F : RadialSource} (hF : ReferenceSmoothFiniteSource D F)
    (hD : IsAccumulatingProfile D) (γ M : ℝ) :
    SourceDerivativeMember D γ M (angularPartial F.1) := by
  have ht := r11b_radialTest_angularPartial (hF.radialTest hD)
  obtain ⟨K, hK, hcore, hz⟩ := ht.2.2
  exact ⟨radialCellIntegrable_of_continuous hD.choose_spec.2.1 ht.1.continuous,
    sourceCellSquare_summable_of_radialCompactSupport hD hK hcore hz γ M⟩

theorem ReferenceSmoothFiniteSource.exists_normal {D : ReferenceData}
    {F : RadialSource} (hF : ReferenceSmoothFiniteSource D F)
    (hD : IsAccumulatingProfile D) {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur ∧
      OutputRealization D γ M₁ 0 (ur, 0) := by
  obtain ⟨C, hC, hN⟩ := hNormal
  obtain ⟨ur, hd, hU, _hbound⟩ := hN F (angularPartial F.1) (hF.sourceMember hD γ M₀)
    (weakAngularDerivative_of_contDiff hF.contDiff (hF.radialTest hD).2.1)
    (hF.sourceDerivativeMember hD γ M₀)
  exact ⟨ur, hd, hU⟩

end

end ContinuousFlexibility.Radial
