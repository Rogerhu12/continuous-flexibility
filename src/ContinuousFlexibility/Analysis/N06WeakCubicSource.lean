import ContinuousFlexibility.Analysis.N06CubicMultiplierJets
import ContinuousFlexibility.Analysis.N06WeakJetProduct
import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# Cubic weak source in the original volume level

The five actual cubic multipliers act on five arrays of weak angular
jets with signs [even, odd, even, even, odd]. A positive scale on each
column is divided out of the coefficients. The resulting source lies
in the original even volume graph, with all stored angular jets and an
explicit norm bound. The final identity records the material scaling
that recovers the physical cubic source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The source made from the genuine five cubic multipliers. The input
fields have weak angular jets, and need not have smooth representatives. -/
theorem n06Volume_weakCubicSource
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (d e : ℕ → ℝ → ℝ) (A B C : ℕ → PolarPoint → ℝ)
    (hd : ∀ m, ContDiffOn ℝ ∞ (d m) (Ioo (K.left m) (K.right m)))
    (he : ∀ m, ContDiffOn ℝ ∞ (e m) (Ioo (K.left m) (K.right m)))
    (hdpos : ∀ m x, x ∈ Ioo (K.left m) (K.right m) → 0 < d m x)
    (hdle : ∀ m x, x ∈ Ioo (K.left m) (K.right m) → d m x ≤ 1)
    (hele : ∀ m x, x ∈ Ioo (K.left m) (K.right m) → |e m x| ≤ 1)
    (hA : ∀ m, ContDiffOn ℝ ∞ (A m) (canonicalOpen S K m))
    (hB : ∀ m, ContDiffOn ℝ ∞ (B m) (canonicalOpen S K m))
    (hC : ∀ m, ContDiffOn ℝ ∞ (C m) (canonicalOpen S K m))
    (hAp : ∀ m p, p ∈ canonicalOpen S K m → A m (p + (0, Real.pi)) = A m p)
    (hBp : ∀ m p, p ∈ canonicalOpen S K m → B m (p + (0, Real.pi)) = B m p)
    (hCp : ∀ m p, p ∈ canonicalOpen S K m → C m (p + (0, Real.pi)) = C m p)
    (hAe : ∀ m p, p ∈ canonicalOpen S K m → A m (p.1, Real.pi - p.2) = A m p)
    (hBo : ∀ m p, p ∈ canonicalOpen S K m → B m (p.1, Real.pi - p.2) = -B m p)
    (hCe : ∀ m p, p ∈ canonicalOpen S K m → C m (p.1, Real.pi - p.2) = C m p)
    (scale : ℕ → ℝ) (hscale : ∀ m, 0 < scale m) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : ∀ m a j, a + j ≤ b + 1 → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative a j (A m) p| ≤ δ * scale m ∧
      |mixedDerivative a j (B m) p| ≤ δ * scale m ∧
      |mixedDerivative a j (C m) p| ≤ δ * scale m)
    (f : Fin 5 → CanonicalVolumeJets S K b)
    (hf : ∀ i m (j : Fin (b + 1)),
      WeakCanonicalAngularDerivative S K m (f i m 0) (f i m j) j.val)
    (hfpar : ∀ i m, (fun p : PolarPoint => f i m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => n06CubicGraphParity i * f i m 0 p) :
    ∃ G : V.level γ t b,
      (∀ m, (V.forget γ t b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => ∑ i : Fin 5,
          (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) *
            ((scale m)⁻¹ * n06CubicGraphMultipliers (d m) (e m) (A m) (B m) (C m) i p *
              f i m 0 p)) ∧
      ‖G‖ ≤ (5 * n06WeakAngularMultiplierCost b) * δ * ∑ i : Fin 5, ‖f i‖ := by
  let a : Fin 5 → ℕ → PolarPoint → ℝ := fun i m p =>
    (scale m)⁻¹ * n06CubicGraphMultipliers (d m) (e m) (A m) (B m) (C m) i p
  have ha (i : Fin 5) (m : ℕ) : ContDiffOn ℝ ∞ (a i m) (canonicalOpen S K m) :=
    contDiffOn_const.mul (n06CubicGraphMultipliers_contDiffOn_strip
      (hd m) (he m) (hdpos m) (hA m) (hB m) (hC m) i)
  have hp (i : Fin 5) (m : ℕ) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      a i m (p + (0, Real.pi)) = a i m p := by
    exact congrArg (fun v => (scale m)⁻¹ * v)
      (n06CubicGraphMultipliers_periodicOn_strip (d m) (e m)
        (fun q hq => hAp m q ⟨hq, mem_univ _⟩)
        (fun q hq => hBp m q ⟨hq, mem_univ _⟩)
        (fun q hq => hCp m q ⟨hq, mem_univ _⟩) i p hpU.1)
  have hpar (i : Fin 5) (m : ℕ) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      a i m (p.1, Real.pi - p.2) = n06CubicGraphParity i * a i m p := by
    dsimp only [a]
    rw [n06CubicGraphMultipliers_reflectionOn_strip (d m) (e m) (hA m) (hB m) (hC m)
      (fun q hq => hAe m q ⟨hq, mem_univ _⟩)
      (fun q hq => hBo m q ⟨hq, mem_univ _⟩)
      (fun q hq => hCe m q ⟨hq, mem_univ _⟩) i p hpU.1]
    ring
  have habound (i : Fin 5) (m j : ℕ) (hj : j ≤ b)
      (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      |mixedDerivative 0 j (a i m) p| ≤ 5 * δ := by
    have hMj := n06CubicGraphMultipliers_angularJet_abs_leOn_strip
      (d m) (e m) (hA m) (hB m) (hC m) (mul_nonneg hδ (hscale m).le)
      p hpU.1 (hdpos m p.1 hpU.1).le (hdle m p.1 hpU.1) (hele m p.1 hpU.1)
      (fun u v huv => hsmall m u v huv p hpU) j hj i
    change |mixedDerivative 0 j (fun q => (scale m)⁻¹ *
      n06CubicGraphMultipliers (d m) (e m) (A m) (B m) (C m) i q) p| ≤ _
    rw [spaces_mixedDerivative_const_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (hscale m).le)]
    calc
      _ ≤ (scale m)⁻¹ * (5 * (δ * scale m)) :=
        mul_le_mul_of_nonneg_left hMj (inv_nonneg.mpr (hscale m).le)
      _ = (5 * δ) * ((scale m)⁻¹ * scale m) := by ring
      _ = 5 * δ := by rw [inv_mul_cancel₀ (hscale m).ne', mul_one]
  obtain ⟨G, hGfield, hGnorm⟩ := n06Volume_weakJetProduct_sum hV γ t b a ha hp
    (fun i _ => n06CubicGraphParity i) (fun i _ => n06CubicGraphParity_sq i) hpar
    (fun _ => 5 * δ) (fun _ => mul_nonneg (by norm_num) hδ) habound f hf hfpar
  refine ⟨G, hGfield, ?_⟩
  calc
    ‖G‖ ≤ n06WeakAngularMultiplierCost b * ∑ i : Fin 5, (5 * δ) * ‖f i‖ := hGnorm
    _ = (5 * n06WeakAngularMultiplierCost b) * δ * ∑ i : Fin 5, ‖f i‖ := by
      rw [← Finset.mul_sum]
      ring

/-- The normalization `H^β E^A` on the coefficients and the factor `E^A`
in the stored graph fields cancel against the original volume forget
weight. The resulting function is the unscaled physical five-field sum. -/
theorem n06Volume_materialCubicSource_identity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (β A : ℝ) (b : ℕ) (G : V.level β 0 b)
    (M : Fin 5 → ℕ → PolarPoint → ℝ)
    (f : Fin 5 → CanonicalVolumeJets S K b)
    (g : Fin 5 → ∀ m, CanonicalL2 S K m)
    (hfields : ∀ i m, (f i m 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => T.E0 (T.sample (K.cell m)) ^ A * g i m p)
    (hsource : ∀ m, (V.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => ∑ i : Fin 5,
        (T.M (T.sample (K.cell m)) ^ (-(0 : ℝ)) * T.H (T.sample (K.cell m)) ^ β) *
          ((T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A)⁻¹ *
            M i m p * f i m 0 p)) :
    ∀ m, (V.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => ∑ i : Fin 5, M i m p * g i m p := by
  intro m
  have hsample : T.sample (K.cell m) ∈ Ioo D.a D.b :=
    spaces_trace_sample_mem hD hT (K.cell m)
  have hH : T.H (T.sample (K.cell m)) ^ β ≠ 0 :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hsample).2.1 β).ne'
  have hE : T.E0 (T.sample (K.cell m)) ^ A ≠ 0 :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hsample).2.2.1 A).ne'
  have hfields' : ∀ᵐ p ∂canonicalMeasure S K m,
      ∀ i : Fin 5, f i m 0 p = T.E0 (T.sample (K.cell m)) ^ A * g i m p :=
    ae_all_iff.mpr (fun i => hfields i m)
  filter_upwards [hsource m, hfields'] with p hp hfp
  rw [hp]
  apply Finset.sum_congr rfl
  intro i _
  rw [hfp i]
  simp only [neg_zero, Real.rpow_zero, one_mul]
  field_simp [hH, hE]
  <;> ring

end ContinuousFlexibility.Statements
