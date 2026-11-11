import ContinuousFlexibility.Analysis.N01NormalizedRadialCoefficientJets
import ContinuousFlexibility.Analysis.RootCoefficientValueBounds

/-!
# State-independent values of the actual normalized radial coefficient

N01's numerical profile, Q/profile, and discriminant intervals imply
reference bounds for the original radial coefficient. Dividing by the
fixed radial normalization δ keeps a positive interval common to every
sector state and every lifted angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem scaled_radial_coefficient_reference_bounds
    {wref w Q D δ : ℝ} (hwref : 0 < wref) (hδ : 0 < δ)
    (hwl : (1 / 2 : ℝ) ≤ w / wref) (hwu : w / wref ≤ 2)
    (hQl : (7 / 8 : ℝ) ≤ Q / w) (hQu : Q / w ≤ (9 / 8 : ℝ))
    (hDl : (1 / 2 : ℝ) ≤ D) (hDu : D ≤ (3 / 2 : ℝ)) :
    Q * inverseDThreeHalves D / δ ∈ Icc (wref / (8 * δ)) (16 * wref / δ) := by
  have hwl' := (le_div_iff₀ hwref).mp hwl
  have hwu' := (div_le_iff₀ hwref).mp hwu
  have hw : 0 < w := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hwref).trans_le hwl'
  have ha := root_radial_coefficient_relative_bounds hw hQl hQu hDl hDu
  have hlo : wref / 8 ≤ Q * inverseDThreeHalves D := by linarith [ha.1]
  have hhi : Q * inverseDThreeHalves D ≤ 16 * wref := by linarith [ha.2]
  constructor
  · rw [← div_div]
    exact div_le_div_of_nonneg_right hlo hδ.le
  · exact div_le_div_of_nonneg_right hhi hδ.le

theorem n01_scaledRadialCoefficient_root_values
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r σ δ : ℝ}
    (hN : N01Properties D T S C base loss ε) (hr : r ∈ Ioo D.a D.b) (hδ : 0 < δ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (θ : ℝ) :
    rootScaledRadialCoefficient D S C z r σ δ (0, θ) ∈
      Icc (D.w r / (8 * δ)) (16 * D.w r / δ) := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : 0 < D.w r := hD.1.2.2.2.2.1 r hr
  have hnum := hN.2.2.2.2.2.2.2.2.2.1 z hz hs (r, θ) ⟨hr, mem_univ _⟩
  have hb := scaled_radial_coefficient_reference_bounds hwref hδ
    hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2.1 hnum.2.2.2.2.1 hnum.2.2.2.2.2
  change (originalCoefficients D S C z).a (r + (σ * δ) * 0, θ) / δ ∈ _
  simp only [mul_zero, add_zero]
  exact hb

end ContinuousFlexibility.Analysis
