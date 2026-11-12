import ContinuousFlexibility.Analysis.MorseRealizedOpticalEnvelope
import ContinuousFlexibility.Analysis.OpticalLowerRadiusScaling
import ContinuousFlexibility.Analysis.MaterialCellOverlapRadialPolynomial

/-!
# The scaled Morse coefficient in the actual host material weight

An actual midpoint lies both in a transported model cell and in the
host cell. Their overlap compares the model radial scale to the host
sample without identifying or replacing their indices.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem morseRealization_scaled_material_optical_envelope
    {Q : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    {T : MaterialData} {l h R H : ℝ}
    (hreal : MorseChainRealization Q σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (hstart : 100 ≤ Q.index) (hT : IsMaterialData E T) (hE : IsAccumulatingProfile E)
    (hR : 0 < R) (hH : H ≠ 0)
    (hprofile : ∀ r ∈ Ioo l h, E.w (R * r) = H * R * D.w r)
    (hcell : ∀ m r, r ∈ Ioo l h → r ∈ D.cells m → R * r ∈ E.cells m)
    (hindex : ∀ m, D.cellIndex m ≤ E.cellIndex m) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ side n, Q.index ≤ n → ∀ j,
      let a := Q.radius side n (morseLeftTurn (morseChainA Q n) (morseChainB Q n))
      let b := Q.radius side n (morseRightTurn (morseChainA Q n) (morseChainB Q n))
      Ioo a b ⊆ Ioo l h → Ioo (R * a) (R * b) ⊆ E.cells j →
      0 < morseRealizationOpticalLower Q D n / R ^ 3 ∧
      (morseRealizationOpticalLower Q D n / R ^ 3)⁻¹ ≤ K * T.E0 (T.sample j) ^ A ∧
      ∀ r ∈ Ioo (R * a) (R * b),
        (morseRealizationOpticalLower Q D n / R ^ 3) *
          min (r - R * a) (R * b - r) ≤ -deriv E.w r / (r * E.w r) := by
  obtain ⟨K₀, hK₀, hoptical⟩ := morseRealization_uniform_optical_envelope hreal hσ hstart
  obtain ⟨K₁, A, hK₁, hA, hmaterial⟩ :=
    materialCells_overlap_radialE_power_bound hT hE (by norm_num : (0 : ℝ) ≤ 6)
  refine ⟨R ^ 3 * K₀ * K₁, A, mul_pos (mul_pos (pow_pos hR 3) hK₀) hK₁, hA, ?_⟩
  intro side n hn j
  dsimp only
  intro hsub hhost
  let a := Q.radius side n (morseLeftTurn (morseChainA Q n) (morseChainB Q n))
  let b := Q.radius side n (morseRightTurn (morseChainA Q n) (morseChainB Q n))
  have hmodel := morseRealization_model_return hreal hσ side hn
  have hcomponent : NegativeRadialComponent D a b := hmodel.1
  let x := (a + b) / 2
  have hx : x ∈ Ioo a b := by dsimp only [x]; constructor <;> linarith only [hcomponent.2.1]
  obtain ⟨m, hm, hxm⟩ := hmodel.2.2 x hx
  have hxE : R * x ∈ E.cells m := hcell m x (hsub hx) hxm
  have hxj : R * x ∈ E.cells j := hhost
    ⟨mul_lt_mul_of_pos_left hx.1 hR, mul_lt_mul_of_pos_left hx.2 hR⟩
  have hnE : n ≤ E.cellIndex m := by rw [← hm]; exact hindex m
  have hmat := hmaterial m j n (R * x) hxE hxj hnE
  obtain ⟨hκ, hinv, hlower⟩ := hoptical side n hn
  have hscaled := optical_lower_scaled_inverse hκ hR
  refine ⟨hscaled.1, ?_, ?_⟩
  · rw [hscaled.2]
    calc
      _ ≤ R ^ 3 * (K₀ * radialE n ^ (6 : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hR.le _)
      _ ≤ R ^ 3 * (K₀ * (K₁ * T.E0 (T.sample j) ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmat hK₀.le) (pow_nonneg hR.le _)
      _ = (R ^ 3 * K₀ * K₁) * T.E0 (T.sample j) ^ A := by ring
  · exact optical_lower_of_radius_scaling hR hH hreal.geometry.2.2.1.1
      hE.choose_spec.1.2.2.1.1 (fun t ht => hprofile t (hsub ht))
      (fun t ht => by
        have hcore : t ∈ radialCore D :=
          ⟨hcomponent.1.trans ht.1, ht.2.trans hcomponent.2.2.1⟩
        exact ⟨(hreal.geometry.1.trans hcore.1).ne',
          (hreal.geometry.2.2.2.2.1 t hcore).ne'⟩) hlower

end ContinuousFlexibility.Radial
