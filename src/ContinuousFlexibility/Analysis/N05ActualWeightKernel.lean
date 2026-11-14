module

public import ContinuousFlexibility.Analysis.N05MaterialLogComparison
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# The kernel with actual sampled material weights

One discrete material power absorbs every fixed coefficient exponent and
the logarithmic error between the actual sample weight and its reference
index. With loss four, the two absorbed powers leave one reciprocal
material factor at each end of the kernel.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- This estimate uses the actual material function at each point of a
reference cell. Its constant may depend on the two real exponents, while
the single additional discrete material power is fixed. -/
theorem n05_actualMaterial_power_coefficient_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (p c : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ j r, r ∈ D.cells j →
      T.M r ^ p * radialE (D.cellIndex j) ^ c ≤
        K * Real.exp ((p + 1) * Radial.logM (D.cellIndex j)) := by
  obtain ⟨C, _, hlog⟩ := n05_material_reference_logM_bound hD hT
  let A : ℝ := |p| * C + |c|
  obtain ⟨B, hB⟩ := Radial.radialQ_le_logM_add A
  refine ⟨Real.exp (B + |p| * C), Real.exp_pos _, fun j r hrj => ?_⟩
  have hr : r ∈ Ioo D.a D.b := hD.choose_spec.2.1.2.2.2.1 j hrj
  have hM : 0 < T.M r := zero_lt_one.trans_le (hT.2.1 r hr).2.2.2
  have hQ : 0 ≤ radialQ (D.cellIndex j) := Radial.radialQ_nonneg _
  have herror : p * (Real.log (T.M r) - Radial.logM (D.cellIndex j)) ≤
      |p| * C * (radialQ (D.cellIndex j) + 1) := by
    calc
      _ ≤ |p * (Real.log (T.M r) - Radial.logM (D.cellIndex j))| := le_abs_self _
      _ = |p| * |Real.log (T.M r) - Radial.logM (D.cellIndex j)| := abs_mul _ _
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hlog j r hrj) (abs_nonneg p)
  have hc : c * radialQ (D.cellIndex j) ≤ |c| * radialQ (D.cellIndex j) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hQ
  have hcoef := hB (D.cellIndex j)
  dsimp only [A] at hcoef
  have hupper : p * Real.log (T.M r) + c * radialQ (D.cellIndex j) ≤
      (p + 1) * Radial.logM (D.cellIndex j) + (B + |p| * C) := by
    nlinarith only [herror, hc, hcoef]
  calc
    T.M r ^ p * radialE (D.cellIndex j) ^ c =
        Real.exp (p * Real.log (T.M r) + c * radialQ (D.cellIndex j)) := by
      rw [Real.rpow_def_of_pos hM, radialE, ← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + 1) * Radial.logM (D.cellIndex j) + (B + |p| * C)) :=
      Real.exp_le_exp.mpr hupper
    _ = Real.exp (B + |p| * C) *
        Real.exp ((p + 1) * Radial.logM (D.cellIndex j)) := by
      rw [Real.exp_add]
      ring

def n05ActualWeightKernel (D : ReferenceData) (T : MaterialData)
    (cell : ℕ → ℕ) (t c ε : ℝ) (k m : ℕ) : ℝ :=
  T.M (T.sample (cell k)) ^ (t - 4) *
    T.M (T.sample (cell m)) ^ (-t) *
    radialE (D.cellIndex (cell k)) ^ c *
    radialE (D.cellIndex (cell m)) ^ c *
    Real.exp (-ε * |radialS (D.cellIndex (cell k)) - radialS (D.cellIndex (cell m))|)

/-- The pointwise majorant is a product of reciprocal discrete material
weights. Neither the actual samples nor the indexing map are replaced. -/
theorem n05_actualWeightKernel_pointwise {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (cell : ℕ → ℕ) (t c ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ k m,
      0 ≤ n05ActualWeightKernel D T cell t c ε k m ∧
      n05ActualWeightKernel D T cell t c ε k m ≤
        K * Real.exp (-Radial.logM (D.cellIndex (cell k))) *
          Real.exp (-Radial.logM (D.cellIndex (cell m))) := by
  obtain ⟨Kl, hKl, hl⟩ := n05_actualMaterial_power_coefficient_bound hD hT (t - 4) c
  obtain ⟨Kr, hKr, hr⟩ := n05_actualMaterial_power_coefficient_bound hD hT (-t) c
  obtain ⟨A, hA⟩ := Radial.absorb_logM (2 - t) ε hε
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  have hM (k : ℕ) : 0 < T.M (T.sample (cell k)) :=
    zero_lt_one.trans_le (hT.2.1 _ (hD.choose_spec.2.1.2.2.2.1 _ (hsample _))).2.2.2
  let K : ℝ := Kl * Kr * Real.exp A
  refine ⟨K, by dsimp only [K]; positivity, fun k m => ?_⟩
  have hleft := hl (cell k) (T.sample (cell k)) (hsample _)
  have hright := hr (cell m) (T.sample (cell m)) (hsample _)
  have hMk := hM k
  have hMm := hM m
  have hEk : 0 < radialE (D.cellIndex (cell k)) := Real.exp_pos _
  have hEm : 0 < radialE (D.cellIndex (cell m)) := Real.exp_pos _
  refine ⟨by unfold n05ActualWeightKernel; positivity, ?_⟩
  have hprod :
      (T.M (T.sample (cell k)) ^ (t - 4) * radialE (D.cellIndex (cell k)) ^ c) *
        (T.M (T.sample (cell m)) ^ (-t) * radialE (D.cellIndex (cell m)) ^ c) ≤
      (Kl * Real.exp ((t - 4 + 1) * Radial.logM (D.cellIndex (cell k)))) *
        (Kr * Real.exp ((-t + 1) * Radial.logM (D.cellIndex (cell m)))) :=
    mul_le_mul hleft hright (by positivity) (by positivity)
  have hexponent :
      (t - 3) * Radial.logM (D.cellIndex (cell k)) +
        (1 - t) * Radial.logM (D.cellIndex (cell m)) -
        ε * |radialS (D.cellIndex (cell k)) - radialS (D.cellIndex (cell m))| ≤
      A - Radial.logM (D.cellIndex (cell k)) - Radial.logM (D.cellIndex (cell m)) := by
    nlinarith only [hA (D.cellIndex (cell k)) (D.cellIndex (cell m))]
  calc
    n05ActualWeightKernel D T cell t c ε k m =
        ((T.M (T.sample (cell k)) ^ (t - 4) * radialE (D.cellIndex (cell k)) ^ c) *
          (T.M (T.sample (cell m)) ^ (-t) * radialE (D.cellIndex (cell m)) ^ c)) *
        Real.exp (-ε * |radialS (D.cellIndex (cell k)) - radialS (D.cellIndex (cell m))|) := by
      unfold n05ActualWeightKernel
      ring
    _ ≤ ((Kl * Real.exp ((t - 4 + 1) * Radial.logM (D.cellIndex (cell k)))) *
          (Kr * Real.exp ((-t + 1) * Radial.logM (D.cellIndex (cell m))))) *
        Real.exp (-ε * |radialS (D.cellIndex (cell k)) - radialS (D.cellIndex (cell m))|) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ = (Kl * Kr) *
        (Real.exp ((t - 4 + 1) * Radial.logM (D.cellIndex (cell k))) *
          Real.exp ((-t + 1) * Radial.logM (D.cellIndex (cell m))) *
          Real.exp (-ε * |radialS (D.cellIndex (cell k)) - radialS (D.cellIndex (cell m))|)) := by
      ring
    _ = (Kl * Kr) * Real.exp
        ((t - 3) * Radial.logM (D.cellIndex (cell k)) +
          (1 - t) * Radial.logM (D.cellIndex (cell m)) -
          ε * |radialS (D.cellIndex (cell k)) - radialS (D.cellIndex (cell m))|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ (Kl * Kr) * Real.exp
        (A - Radial.logM (D.cellIndex (cell k)) - Radial.logM (D.cellIndex (cell m))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (mul_pos hKl hKr).le
    _ = K * Real.exp (-Radial.logM (D.cellIndex (cell k))) *
        Real.exp (-Radial.logM (D.cellIndex (cell m))) := by
      dsimp only [K]
      simp only [sub_eq_add_neg, Real.exp_add]
      ring

end ContinuousFlexibility.Statements

