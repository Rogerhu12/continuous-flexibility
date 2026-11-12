import ContinuousFlexibility.Analysis.N05ReferenceSourceCompatibility
import ContinuousFlexibility.Analysis.N05ReferenceLowAngularWeak

/-!
# Angular jets of the actual auxiliary normalizer

The prescribed normalizer need not be radial. Its compact radial support
makes its actual angular derivatives admissible in every fixed reference
source weight. The corrected source therefore has the literal derivative
`f_j - λ ∂θ^j ψ`, with the same scalar λ at every angular order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Radial

theorem n05_compact_annular_contDiff {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hsupp : HasCompactRadialSupport D f) : ContDiff ℝ ∞ f := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := hsupp
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ annularOpen D
  · exact hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  · have hpJ : p.1 ∉ J := fun h => hp ⟨hJcore h, mem_univ _⟩
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ J :=
      (hJ.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpJ
    have heq : f =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnear] with q hq
      exact hzero q.1 hq q.2
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Angular differentiation preserves the same radial support set. -/
theorem n05_angularJet_compact_radial_support {D : ReferenceData}
    {f : PolarPoint → ℝ} (hsupp : HasCompactRadialSupport D f) (j : ℕ) :
    HasCompactRadialSupport D (mixedDerivative 0 j f) := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := hsupp
  refine ⟨J, hJ, hJcore, fun r hr θ => ?_⟩
  have hz : (fun t : ℝ => f (r, t)) = (0 : ℝ → ℝ) :=
    funext (fun t => hzero r hr t)
  simp only [mixedDerivative, iteratedDeriv_zero, hz,
    iteratedDeriv_const_zero, Pi.zero_apply]

theorem n05_physicalNormalizer_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    ContDiff ℝ ∞ ((S.height (3 / 4 : ℝ)).decode S.psi) := by
  have hψ := (hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi
  have hsupp : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode S.psi) := by
    rcases hS with ⟨_, _, _, _, _, _, _, _, hsupp, _⟩
    exact hsupp
  exact n05_compact_annular_contDiff hψ.1 hsupp

/-- The material exponent is fixed before the angular order. -/
theorem n05_physicalNormalizer_angular_sourceDerivativeMember
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (γ M : ℝ) (j : ℕ) :
    SourceDerivativeMember D γ M
      (mixedDerivative 0 j ((S.height (3 / 4 : ℝ)).decode S.psi)) := by
  have hsupp : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode S.psi) := by
    rcases hS with ⟨_, _, _, _, _, _, _, _, hsupp, _⟩
    exact hsupp
  obtain ⟨J, hJ, hJcore, hzero⟩ := n05_angularJet_compact_radial_support hsupp j
  exact r11b_compact_sourceDerivativeMember hD hJ hJcore
    (contDiff_mixedDerivative (n05_physicalNormalizer_contDiff hS) 0 j).continuous
    (fun r _ hr => hzero r hr) γ M

/-- Integration by parts is tested against the actual full-period physical
test class, including tests that are not π-periodic. -/
theorem n05_physicalNormalizer_weak_angularJet
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (j : ℕ) :
    n05_weakReferenceAngularJet D ((S.height (3 / 4 : ℝ)).decode S.psi)
      (mixedDerivative 0 j ((S.height (3 / 4 : ℝ)).decode S.psi)) j := by
  have hψ := (hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi
  apply n05_referenceAngularJet_weak_of_smooth_slices
  · intro r
    exact (n05_physicalNormalizer_contDiff hS).comp
      (contDiff_const.prodMk contDiff_id)
  · intro r θ
    change (S.height (3 / 4 : ℝ)).decode S.psi (r, θ + 2 * Real.pi) =
      (S.height (3 / 4 : ℝ)).decode S.psi (r, θ)
    have hp (x : ℝ) : (S.height (3 / 4 : ℝ)).decode S.psi (r, x + Real.pi) =
        (S.height (3 / 4 : ℝ)).decode S.psi (r, x) := by
      simpa only [Prod.mk_add_mk, add_zero] using hψ.2.2.1 (r, x)
    rw [show θ + 2 * Real.pi = (θ + Real.pi) + Real.pi by ring, hp, hp]

theorem n05_referenceMeanPairing_const_mul (D : ReferenceData)
    (f g : PolarPoint → ℝ) (c : ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => (c * f (r, θ)) * g (r, θ))) =
      c * ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * g (r, θ)) := by
  simp only [radialAngularMean, mul_assoc, intervalIntegral.integral_const_mul]
  ring

theorem n05_weakReferenceAngularJet_const_mul {D : ReferenceData}
    {u d : PolarPoint → ℝ} {j : ℕ}
    (h : n05_weakReferenceAngularJet D u d j) (c : ℝ) :
    n05_weakReferenceAngularJet D (fun p => c * u p) (fun p => c * d p) j := by
  intro φ hφ
  rw [n05_referenceMeanPairing_const_mul, n05_referenceMeanPairing_const_mul, h φ hφ]
  ring

/-- The correction keeps every actual angular derivative of ψ. -/
theorem n05_normalizedSource_weak_angularJet
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    {u d : PolarPoint → ℝ} {j : ℕ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (h : n05_weakReferenceAngularJet D u d j) (c : ℝ) :
    n05_weakReferenceAngularJet D
      (fun p => u p - c * (S.height (3 / 4 : ℝ)).decode S.psi p)
      (fun p => d p - c * mixedDerivative 0 j ((S.height (3 / 4 : ℝ)).decode S.psi) p) j := by
  have hψ := n05_physicalNormalizer_contDiff hS
  have hψLp := r11b_continuous_memLp (D := D) hψ.continuous
  have hψjLp := r11b_continuous_memLp (D := D)
    (contDiff_mixedDerivative hψ 0 j).continuous
  have hs := n05_weakReferenceAngularJet_add hab hu (hψLp.const_mul (-c))
    hd (hψjLp.const_mul (-c)) h
    (n05_weakReferenceAngularJet_const_mul (n05_physicalNormalizer_weak_angularJet hS j) (-c))
  convert hs using 1 <;> funext p <;> simp only [Pi.add_apply] <;> ring

/-- The first angular jet is exactly the frozen first-normal hypothesis. -/
theorem n05_weakAngularDerivative_of_weakReferenceJet
    {D : ReferenceData} {u d : PolarPoint → ℝ}
    (h : n05_weakReferenceAngularJet D u d 1) : WeakAngularDerivative D u d := by
  intro φ hφ
  have he := h φ hφ
  have hzero : mixedDerivative 0 0 φ = φ := by
    funext p
    simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
  have hder : mixedDerivative 0 1 φ = angularPartial φ := by
    simpa only [Nat.zero_add, hzero] using (angularPartial_mixedDerivative hφ.1 0 0).symm
  rw [hder, pow_one, neg_one_mul] at he
  linarith only [he]

end ContinuousFlexibility.Statements
