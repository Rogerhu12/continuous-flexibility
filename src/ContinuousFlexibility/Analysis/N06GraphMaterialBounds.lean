import ContinuousFlexibility.Analysis.N06MaterialAbsorption
import ContinuousFlexibility.Analysis.N06UnitWeakGraphData

/-!
# Material absorption for the actual five weak graph fields

The local graph constant is allowed the explicit material growth
K_m <= C E0_m^C. Multiplying a physical graph field by E0_m^A then
retains an H_m^beta factor from the physical solution/source rows.
That factor absorbs both this coefficient growth and the fixed N05 loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ENNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The fifth power of the primitive scalar graph constant is an explicit
material power; no such bound is inferred from the frozen N04 contract. -/
theorem n06_graph_material_power_le {E κ C A : ℝ}
    (hE : 0 < E) (hκ : 0 ≤ κ) (hκC : κ ≤ C * E ^ C) :
    E ^ A * κ ^ 5 ≤ C ^ 5 * E ^ (A + C * 5) := by
  calc
    E ^ A * κ ^ 5 ≤ E ^ A * (C * E ^ C) ^ 5 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ hκC 5) (Real.rpow_nonneg hE.le A)
    _ = C ^ 5 * E ^ (A + C * 5) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hE.le C 5, Real.rpow_add hE]
      ring

/-- The actual material hypotheses give a uniform graph-row majorant.
Only the primitive scalar geometry bound is an additional input. -/
theorem n06_material_graph_row_absorb {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (β A loss C : ℝ) (hβ : 0 < β) (hC : 0 < C) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ r ∈ Ioo D.a D.b, ∀ κ x y : ℝ,
      0 ≤ κ → κ ≤ C * T.E0 r ^ C → 0 ≤ x → 0 ≤ y →
      T.E0 r ^ A * (128 * κ ^ 5) * T.H r ^ β *
        (x + T.M r ^ loss * y) ≤ Q * (x + y) := by
  obtain ⟨Q₀, hQ₀, hzero⟩ := n06_material_loss_absorb hT β (A + C * 5) 0 hβ
  obtain ⟨Q₁, hQ₁, hloss⟩ := n06_material_loss_absorb hT β (A + C * 5) loss hβ
  let Q : ℝ := 128 * C ^ 5 * (Q₀ + Q₁)
  have hQ : 0 < Q := mul_pos (mul_pos (by norm_num) (pow_pos hC 5)) (add_pos hQ₀ hQ₁)
  refine ⟨Q, hQ, ?_⟩
  intro r hr κ x y hκ hκC hx hy
  have hpos := hT.2.1 r hr
  have hH : 0 ≤ T.H r ^ β := Real.rpow_nonneg hpos.2.1.le β
  have hM : 0 ≤ T.M r ^ loss := Real.rpow_nonneg (zero_le_one.trans hpos.2.2.2) loss
  have h₀ : T.H r ^ β * T.E0 r ^ (A + C * 5) ≤ Q₀ := by
    simpa only [Real.rpow_zero, mul_one] using hzero r hr
  have h₁ := hloss r hr
  have hpower := n06_graph_material_power_le hpos.2.2.1 hκ hκC (A := A)
  calc
    _ = 128 * ((T.E0 r ^ A * κ ^ 5) * T.H r ^ β *
        (x + T.M r ^ loss * y)) := by ring
    _ ≤ 128 * ((C ^ 5 * T.E0 r ^ (A + C * 5)) * T.H r ^ β *
        (x + T.M r ^ loss * y)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpower hH) (add_nonneg hx (mul_nonneg hM hy)))
        (by norm_num)
    _ = (128 * C ^ 5) *
        ((T.H r ^ β * T.E0 r ^ (A + C * 5)) * x +
          (T.H r ^ β * T.E0 r ^ (A + C * 5) * T.M r ^ loss) * y) := by ring
    _ ≤ (128 * C ^ 5) * (Q₀ * x + Q₁ * y) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right h₀ hx) (mul_le_mul_of_nonneg_right h₁ hy))
        (mul_nonneg (by norm_num) (pow_nonneg hC.le 5))
    _ ≤ (128 * C ^ 5) * ((Q₀ + Q₁) * (x + y)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (pow_nonneg hC.le 5))
      nlinarith only [mul_nonneg hQ₀.le hy, mul_nonneg hQ₁.le hx]
    _ = Q * (x + y) := by dsimp only [Q]; ring

/-- Assemble arbitrary-parity weak graph rows in the original canonical lp.
Unlike the even source submodule, the five individual field arrays may be odd. -/
theorem n06_graphJets_of_piecewise_sum_bound
    {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
    (F W : CanonicalVolumeJets S K b)
    (J : ∀ m, PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    {Q : ℝ} (hQ : 0 ≤ Q) (hbound : ∀ m, ‖J m‖ ≤ Q * (‖F m‖ + ‖W m‖)) :
    ∃ Y : CanonicalVolumeJets S K b,
      (∀ m, Y m = J m) ∧ ‖Y‖ ≤ Q * (‖F‖ + ‖W‖) := by
  have hJ : Memℓp J 2 :=
    (((lp.memℓp F).norm.add (lp.memℓp W).norm).const_mul Q).mono hbound
  let Y : CanonicalVolumeJets S K b := ⟨J, hJ⟩
  let major : lp (fun _ : ℕ => ℝ) 2 := Q • (lp.toNorm F + lp.toNorm W)
  have hcoordinate (m : ℕ) : ‖Y m‖ ≤ ‖major m‖ := by
    change ‖J m‖ ≤ ‖Q * (‖F m‖ + ‖W m‖)‖
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hQ (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
    exact hbound m
  have hnorm : ‖Y‖ ≤ ‖major‖ :=
    lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hcoordinate
  refine ⟨Y, fun _ => rfl, hnorm.trans ?_⟩
  calc
    ‖major‖ = Q * ‖lp.toNorm F + lp.toNorm W‖ := by
      simp only [major, norm_smul, Real.norm_eq_abs, abs_of_nonneg hQ]
    _ ≤ Q * (‖lp.toNorm F‖ + ‖lp.toNorm W‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hQ
    _ = Q * (‖F‖ + ‖W‖) := by rw [lp.norm_toNorm, lp.norm_toNorm]

end ContinuousFlexibility.Analysis
