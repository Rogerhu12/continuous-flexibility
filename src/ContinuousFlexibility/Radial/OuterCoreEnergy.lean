import ContinuousFlexibility.Radial.OuterRealizedCellEnergy
import ContinuousFlexibility.Radial.OuterCoreIntervals
import ContinuousFlexibility.Radial.OuterJoinTransfer

/-!
# Transfer across the actual glue and retained transition cell

The ordinary physical state is used throughout.  The core is split at
the actual matched seam, and the same two-direction estimate covers both
ends of the annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

def outerPositivePhysicalFactor (D : ReferenceData) (j scale l r : ℝ) : ℝ :=
  let a := ∫ x in l..r, scale / D.w x
  let b := ∫ x in l..r, j ^ 2 * deriv D.w x / (scale * x)
  (1 + a + b) ^ 4 * exp (2 * sqrt (a * b) + 2)

theorem outerPositivePhysicalFactor_nonneg (D : ReferenceData) (j scale l r : ℝ) :
    0 ≤ outerPositivePhysicalFactor D j scale l r := by
  unfold outerPositivePhysicalFactor
  positivity

theorem outer_positive_physical_energy {D : ReferenceData} {j scale l r : ℝ} {u z : ℝ → ℝ}
    (hD : RadialProfileGeometry D) (hscale : 0 < scale) (hlr : l < r)
    (hsub : Icc l r ⊆ radialCore D)
    (hslope : ∀ x ∈ Ioo l r, 2 / x ≤ deriv D.w x / D.w x)
    (hstate : ∀ x ∈ Icc l r, HasDerivAt u (scale / D.w x * z x) x ∧
      HasDerivAt z (j ^ 2 * deriv D.w x / (scale * x) * u x) x) :
    (u r ^ 2 + z r ^ 2 ≤ (u l ^ 2 + z l ^ 2) * outerPositivePhysicalFactor D j scale l r) ∧
      (u l ^ 2 + z l ^ 2 ≤ (u r ^ 2 + z r ^ 2) * outerPositivePhysicalFactor D j scale l r) := by
  have hw := hD.2.2.1.1
  have hdc : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hwp (x : ℝ) (hx : x ∈ Icc l r) : 0 < D.w x := hD.2.2.2.2.1 x (hsub hx)
  have hxp (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := hD.1.trans (hsub hx).1
  have hmono := morseConnector_monotone_of_logSlope hw
    (hxp l (left_mem_Icc.mpr hlr.le)) hwp hslope
  have hderiv₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ deriv D.w x := by
    have h := hmono.derivWithin_nonneg (x := x)
    rwa [((hw.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hlr x hx)] at h
  have hα : ContinuousOn (fun x => scale / D.w x) (Icc l r) :=
    continuousOn_const.div hw.continuous.continuousOn (fun x hx => (hwp x hx).ne')
  have hβ : ContinuousOn (fun x => j ^ 2 * deriv D.w x / (scale * x)) (Icc l r) :=
    (continuousOn_const.mul hdc.continuousOn).div (continuousOn_const.mul continuousOn_id)
      (fun x hx => (mul_pos hscale (hxp x hx)).ne')
  exact transfer_positive_piece_regularized hlr.le hα hβ
    (fun x hx => div_nonneg hscale.le (hwp x hx).le)
    (fun x hx => div_nonneg (mul_nonneg (sq_nonneg j) (hderiv₀ x hx))
      (mul_nonneg hscale.le (hxp x hx).le)) hstate

theorem morseOuterCore_contains_pieces {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index < n) :
    Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n)) ⊆
        Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) ∧
      Icc (T.joinLeft side (n - 1)) (T.joinRight side (n - 1)) ⊆
        Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n) := by
  have hn₀ : T.index ≤ n - 1 := by omega
  have hn₁ : n - 1 + 1 = n := by omega
  have he := morseRealized_retained_endpoints h side n hn.le
  have hj := h.join_data side (n - 1) hn₀
  cases side with
  | false =>
      simp only [Bool.false_eq_true, ite_false, hn₁] at hj
      change (Icc (T.radius false n (T.leftX false n)) (T.radius false n (T.rightX false n)) ⊆
          Icc (T.radius false n (T.leftX false n)) (T.joinRight false (n - 1))) ∧
        (Icc (T.joinLeft false (n - 1)) (T.joinRight false (n - 1)) ⊆
          Icc (T.radius false n (T.leftX false n)) (T.joinRight false (n - 1)))
      constructor
      · apply Icc_subset_Icc_right
        rw [← hj.2.1]
        exact hj.1.le
      · apply Icc_subset_Icc_left
        rw [hj.2.1]
        exact he.2.2.le
  | true =>
      simp only [ite_true, hn₁] at hj
      change (Icc (T.radius true n (T.leftX true n)) (T.radius true n (T.rightX true n)) ⊆
          Icc (T.joinLeft true (n - 1)) (T.radius true n (T.rightX true n))) ∧
        (Icc (T.joinLeft true (n - 1)) (T.joinRight true (n - 1)) ⊆
          Icc (T.joinLeft true (n - 1)) (T.radius true n (T.rightX true n)))
      constructor
      · apply Icc_subset_Icc_left
        rw [← hj.2.2.1]
        exact hj.1.le
      · apply Icc_subset_Icc_right
        rw [hj.2.2.1]
        exact he.2.2.le

def morseOuterCoreEnergyFactor (T : MorseChainData) (D : ReferenceData)
    (side : Bool) (n : ℕ) (j scale M : ℝ) : ℝ :=
  (M ^ 4 * morseCellEnergyFactor (morseChainA T n) (morseChainB T n) j (1 / 100)) *
    outerPositivePhysicalFactor D j scale (T.joinLeft side (n - 1)) (T.joinRight side (n - 1))

/-- Both physical endpoint energies are bounded by the same factor
derived from the actual three cell pieces and preceding connector. -/
theorem morseOuterCore_endpoint_energy {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {j scale M : ℝ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (hM : 1 ≤ M)
    (side : Bool) (n : ℕ) (hn : T.index < n)
    (hhi : scale / morseChainAmplitude T σ n ≤ M)
    (hlo : morseChainAmplitude T σ n / scale ≤ M)
    (hstate : ∀ r ∈ Icc (morseOuterCoreLeft T side n) (morseOuterCoreRight T side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z (j ^ 2 * deriv D.w r / (scale * r) * u r) r) :
    let l := morseOuterCoreLeft T side n
    let r := morseOuterCoreRight T side n
    let F := morseOuterCoreEnergyFactor T D side n j scale M
    (u r ^ 2 + z r ^ 2 ≤ (u l ^ 2 + z l ^ 2) * F) ∧
      (u l ^ 2 + z l ^ 2 ≤ (u r ^ 2 + z r ^ 2) * F) := by
  let E (r : ℝ) := u r ^ 2 + z r ^ 2
  let Kc := M ^ 4 * morseCellEnergyFactor (morseChainA T n) (morseChainB T n) j (1 / 100)
  let Kj := outerPositivePhysicalFactor D j scale (T.joinLeft side (n - 1)) (T.joinRight side (n - 1))
  have hn₀ : T.index ≤ n - 1 := by omega
  have hn₁ : n - 1 + 1 = n := by omega
  have hpieces := morseOuterCore_contains_pieces h side n hn
  have hcore := morseOuterCore_interval h side n hn
  have hj := h.join_data side (n - 1) hn₀
  have hcell :
      E (T.radius side n (T.rightX side n)) ≤ E (T.radius side n (T.leftX side n)) * Kc ∧
      E (T.radius side n (T.leftX side n)) ≤ E (T.radius side n (T.rightX side n)) * Kc :=
    morseRealized_cell_endpoint_energy h hσ hscale hM side n hn.le hhi hlo
      (fun r hr => hstate r (hpieces.1 hr))
  have hjoin :
      E (T.joinRight side (n - 1)) ≤ E (T.joinLeft side (n - 1)) * Kj ∧
      E (T.joinLeft side (n - 1)) ≤ E (T.joinRight side (n - 1)) * Kj :=
    outer_positive_physical_energy h.geometry hscale hj.1 (hpieces.2.trans hcore.2)
      hj.2.2.2.2 (fun r hr => hstate r (hpieces.2 hr))
  have hKc : 0 ≤ Kc := mul_nonneg (by positivity) (morseCellEnergyFactor_nonneg _ _ _ _)
  have hKj : 0 ≤ Kj := outerPositivePhysicalFactor_nonneg _ _ _ _ _
  cases side with
  | false =>
      have hs : T.joinLeft false (n - 1) = T.radius false n (T.rightX false n) := by
        simpa only [Bool.false_eq_true, ite_false, hn₁] using hj.2.1
      rw [hs] at hjoin
      constructor
      · exact hjoin.1.trans (by
          simpa only [morseOuterCoreEnergyFactor, Kc, Kj, mul_assoc] using
            mul_le_mul_of_nonneg_right hcell.1 hKj)
      · exact hcell.2.trans (by
          have hb := mul_le_mul_of_nonneg_right hjoin.2 hKc
          simpa only [morseOuterCoreEnergyFactor, Kc, Kj, mul_assoc, mul_comm, mul_left_comm] using hb)
  | true =>
      have hs : T.joinRight true (n - 1) = T.radius true n (T.leftX true n) := by
        simpa only [ite_true, hn₁] using hj.2.2.1
      rw [hs] at hjoin
      constructor
      · exact hcell.1.trans (by
          have hb := mul_le_mul_of_nonneg_right hjoin.1 hKc
          simpa only [morseOuterCoreEnergyFactor, Kc, Kj, mul_assoc, mul_comm, mul_left_comm] using hb)
      · exact hjoin.2.trans (by
          simpa only [morseOuterCoreEnergyFactor, Kc, Kj, mul_assoc] using
            mul_le_mul_of_nonneg_right hcell.2 hKj)

end ContinuousFlexibility.Radial
