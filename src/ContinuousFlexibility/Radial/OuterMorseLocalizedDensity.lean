module

public import ContinuousFlexibility.Radial.OuterMorseLocalizedOperator

/-!
# The actual localized ordinary Morse inverse

The weighted operator is the genuine two-multiplier composition with the
constructed Robin inverse. Its density transport gives the same localized
ordinary kernel with a minus sign. The exponent depends only on the common
geometric constants and the position-kernel exponent. Localizers of zero
physical label give the zero operator on the actual outer interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements

def outerMorseOrdinaryExponent (a b : ℝ) (C : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) : ℝ :=
  outerMorseOperatorExponent a b C A hA + outerCellDensityExponent b C

theorem outerMorseOrdinaryExponent_pos {a b : ℝ} {C : ℕ → ℝ}
    (hC : 0 < C 0) (ha : 0 < a) (hab : a < b) (A : ℝ) (hA : 0 ≤ A) :
    0 < outerMorseOrdinaryExponent a b C A hA :=
  add_pos (outerMorseOperatorExponent_pos hC ha hab A hA) (outerCellDensityExponent_pos b hC)

private theorem morseOuter_zero_localized_ordinary_kernel
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) {entry η K : ℝ} {right : Bool} {j N k m : ℕ}
    (hN : M.index + 3 ≤ N) (hlabels : MorseOuterLocalizerLabels M D N)
    (hz : D.cellIndex k = 0 ∨ D.cellIndex m = 0) (kernel : ℝ → ℝ → ℝ)
    (f : Lp ℝ 2 (volume.restrict
      (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
        (outerOutwardRadius right (tailPhysicalEndpoint D right))))) :
    ((0 : Lp ℝ 2 (volume.restrict
        (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
          (outerOutwardRadius right (tailPhysicalEndpoint D right))))) : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))] fun x =>
      -(∫ y, outerWholeLocalizedKernel D right k m kernel x y * f y
        ∂volume.restrict
          (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))) := by
  let μ : Measure ℝ := volume.restrict
    (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
  have hkernel : ∀ x ∈ Ioo
      (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
      (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      ∀ y ∈ Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
        outerWholeLocalizedKernel D right k m kernel x y = 0 := by
    intro x hx y hy
    rcases hz with hk | hm
    · simp only [outerWholeLocalizedKernel,
        morseOuter_localizer_zero_on_whole (j := j) (η := η) (K := K) h hN hlabels hk hx, zero_mul]
    · simp only [outerWholeLocalizedKernel,
        morseOuter_localizer_zero_on_whole (j := j) (η := η) (K := K) h hN hlabels hm hy, mul_zero]
  filter_upwards [Lp.coeFn_zero ℝ 2 μ, ae_restrict_mem measurableSet_Ioo] with x hzero hx
  rw [hzero]
  have hI : (∫ y, outerWholeLocalizedKernel D right k m kernel x y * f y ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [hkernel x hx y hy, zero_mul, Pi.zero_apply]
  rw [hI, neg_zero, Pi.zero_apply]

/-- For every actual pair of localizers, the same whole Green kernel
defines a bounded ordinary operator with the full physical-index decay. -/
theorem MorseOuterGreenData.exists_localized_ordinary
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {right : Bool} {j N : ℕ} {entry η K lam Cbound Co a b A action : ℝ}
    (F : MorseOuterGreenData M D right N j entry η K lam Cbound Co)
    (h : MorseChainRealization M σ D C) (ha : D.a = a) (hb : D.b = b)
    (he : entry ∈ morseInitialMiddle M) (hN : M.index + 3 ≤ N)
    (hlabels : MorseOuterLocalizerLabels M D N) (hA : 0 ≤ A) (hact : 0 ≤ action)
    (hpoint : ∀ p q x y, MorseOuterPoint M D entry right j N η K p x →
      MorseOuterPoint M D entry right j N η K q y →
      |outerGreenKernel lam F.pair.U F.pair.V x y| ≤
        radialE p ^ A * radialE q ^ A * action * exp (-|radialS p - radialS q|))
    (k m : ℕ) :
    ∃ G : Lp ℝ 2 (volume.restrict
          (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))) →L[ℝ]
        Lp ℝ 2 (volume.restrict
          (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))),
      ‖G‖ ≤ radialE (D.cellIndex k) ^ outerMorseOrdinaryExponent a b C A hA *
        radialE (D.cellIndex m) ^ outerMorseOrdinaryExponent a b C A hA * action *
          exp (-|radialS (D.cellIndex k) - radialS (D.cellIndex m)|) ∧
      ∀ f : Lp ℝ 2 (volume.restrict
          (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))),
        (G f : ℝ → ℝ) =ᵐ[volume.restrict
          (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))] fun x =>
            -(∫ y, outerWholeLocalizedKernel D right k m
                (outerGreenKernel lam F.pair.U F.pair.V) x y * f y
              ∂volume.restrict
                (Ioo (outerOutwardRadius right (morseTransitionPhysicalEntry M entry right N))
                  (outerOutwardRadius right (tailPhysicalEndpoint D right)))) := by
  have hentry := morseTransitionPhysicalEntry_mem_core h he right N (by omega)
  by_cases hk : 1 ≤ D.cellIndex k
  · by_cases hm : 1 ≤ D.cellIndex m
    · let R := outerWholeLocalizedOperator h.accumulating.2.1 right
        (morseTransitionPhysicalEntry M entry right N) k m F.inverse.operator
      have hRn := F.localized_norm_le h ha hb he hN hlabels hA hact hpoint k m
      have hRkernel := outerWholeLocalizedOperator_kernel h.accumulating.2.1 right
        (morseTransitionPhysicalEntry M entry right N) k m F.inverse.operator
        (outerGreenKernel lam F.pair.U F.pair.V) F.inverse.kernel
      obtain ⟨G, hGn, hGkernel⟩ := outerWholeLocalizedDensity_transport h.accumulating hb right
        hentry k m hk hm R (outerGreenKernel lam F.pair.U F.pair.V) hRn hRkernel
      refine ⟨G, hGn.trans_eq ?_, hGkernel⟩
      dsimp only [outerMorseOrdinaryExponent]
      rw [rpow_add (show 0 < radialE (D.cellIndex k) from exp_pos _)
          (outerMorseOperatorExponent a b C A hA) (outerCellDensityExponent b C),
        rpow_add (show 0 < radialE (D.cellIndex m) from exp_pos _)
          (outerMorseOperatorExponent a b C A hA) (outerCellDensityExponent b C)]
      ring
    · refine ⟨0, ?_, ?_⟩
      · rw [norm_zero]
        exact outerMorse_localized_envelope_nonneg _ _ _ hact
      · intro f
        simpa only [ContinuousLinearMap.zero_apply] using
          morseOuter_zero_localized_ordinary_kernel (j := j) (η := η) (K := K)
            h hN hlabels (Or.inr (by omega)) (outerGreenKernel lam F.pair.U F.pair.V) f
  · refine ⟨0, ?_, ?_⟩
    · rw [norm_zero]
      exact outerMorse_localized_envelope_nonneg _ _ _ hact
    · intro f
      simpa only [ContinuousLinearMap.zero_apply] using
        morseOuter_zero_localized_ordinary_kernel (j := j) (η := η) (K := K)
          h hN hlabels (Or.inl (by omega)) (outerGreenKernel lam F.pair.U F.pair.V) f

end ContinuousFlexibility.Radial
