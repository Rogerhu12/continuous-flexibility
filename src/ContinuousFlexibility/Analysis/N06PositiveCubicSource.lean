module

public import ContinuousFlexibility.Analysis.N06PositiveCubicMultipliers
public import ContinuousFlexibility.Analysis.N06PositiveWeakGraph
public import ContinuousFlexibility.Analysis.N06WeakCubicSource

/-!
# The all-piece cubic source with one fixed constant

The actual positive graph package supplies five original lp arrays. The
normalized actual cubic multipliers produce a member of the original
volume level. Its forgetful image is the unscaled physical five-field
sum. The constant is fixed before the perturbing coefficient family and
before the original source and height rows.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem n06Volume_positiveCubicSource_of_fields
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (β : ℝ) (b : ℕ)
    (hl : ∀ m, K.positive m = true → K.left m = 0)
    (hr : ∀ m, K.positive m = true → K.right m = 1)
    (scale : ℕ → ℝ) (hscale : ∀ m, 0 < scale m)
    (δ : ℝ) (hδ : 0 ≤ δ) (A B C : ℕ → PolarPoint → ℝ)
    (hcoeff : N06PositiveCubicControl K b scale δ A B C)
    (f : Fin 5 → CanonicalVolumeJets S K b)
    (hf : ∀ i m (j : Fin (b + 1)),
      WeakCanonicalAngularDerivative S K m (f i m 0) (f i m j) j.val)
    (hfpar : ∀ i m, (fun p : PolarPoint => f i m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => n06CubicGraphParity i * f i m 0 p) :
    ∃ G : V.level β 0 b,
      (∀ m, (V.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => ∑ i : Fin 5,
          (T.M (T.sample (K.cell m)) ^ (-(0 : ℝ)) * T.H (T.sample (K.cell m)) ^ β) *
            ((scale m)⁻¹ * n06PositiveCubicMultipliers K A B C i m p * f i m 0 p)) ∧
      ‖G‖ ≤ (5 * n06WeakAngularMultiplierCost b) * δ * ∑ i : Fin 5, ‖f i‖ := by
  let a : Fin 5 → ℕ → PolarPoint → ℝ := fun i m p =>
    (scale m)⁻¹ * n06PositiveCubicMultipliers K A B C i m p
  have ha (i : Fin 5) (m : ℕ) : ContDiffOn ℝ ∞ (a i m) (canonicalOpen S K m) :=
    contDiffOn_const.mul (hcoeff.multiplier_smooth hl hr i m)
  have hp (i : Fin 5) (m : ℕ) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      a i m (p + (0, Real.pi)) = a i m p :=
    congrArg (fun v => (scale m)⁻¹ * v) (hcoeff.multiplier_periodic i m p hpU)
  have hpar (i : Fin 5) (m : ℕ) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      a i m (p.1, Real.pi - p.2) = n06CubicGraphParity i * a i m p := by
    dsimp only [a]
    rw [hcoeff.multiplier_reflection i m p hpU]
    ring
  have habound (i : Fin 5) (m j : ℕ) (hj : j ≤ b)
      (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      |mixedDerivative 0 j (a i m) p| ≤ 5 * δ := by
    change |mixedDerivative 0 j (fun q => (scale m)⁻¹ *
      n06PositiveCubicMultipliers K A B C i m q) p| ≤ _
    rw [spaces_mixedDerivative_const_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (hscale m).le)]
    calc
      _ ≤ (scale m)⁻¹ * (5 * (δ * scale m)) :=
        mul_le_mul_of_nonneg_left
          (hcoeff.multiplier_jet_bound hl hr (fun n => (hscale n).le) hδ i m j hj p hpU)
          (inv_nonneg.mpr (hscale m).le)
      _ = (5 * δ) * ((scale m)⁻¹ * scale m) := by ring
      _ = 5 * δ := by rw [inv_mul_cancel₀ (hscale m).ne', mul_one]
  obtain ⟨G, hGfield, hGnorm⟩ := n06Volume_weakJetProduct_sum hV β 0 b a ha hp
    (fun i _ => n06CubicGraphParity i) (fun i _ => n06CubicGraphParity_sq i) hpar
    (fun _ => 5 * δ) (fun _ => mul_nonneg (by norm_num) hδ) habound f hf hfpar
  refine ⟨G, hGfield, ?_⟩
  calc
    ‖G‖ ≤ n06WeakAngularMultiplierCost b * ∑ i : Fin 5, (5 * δ) * ‖f i‖ := hGnorm
    _ = (5 * n06WeakAngularMultiplierCost b) * δ * ∑ i : Fin 5, ‖f i‖ := by
      rw [← Finset.mul_sum]
      ring

/-- The full material estimate and actual physical source. The input
geometry consists of scalar reference coefficient bounds and the weak
reference equation. No bound for a relative operator is assumed. -/
theorem n06_positiveCubicSource_material_family
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Vol : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hVol : IsVolumeModel T S K Vol)
    (β Aexp loss : ℝ) (hβ : 0 < β) (b : ℕ)
    (a c V q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c V q κ Cref) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ A B C : ℕ → PolarPoint → ℝ,
      N06PositiveCubicControl K b
        (fun m => T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ Aexp) δ A B C →
      ∀ F : Vol.level β 0 b, ∀ W : Vol.level β (-loss) b,
      (∀ m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
        (∫ p, n06MaterialJetRow T K β (-loss) W.val m 0 p *
          n06UnitReferenceTestOperator (a m) (c m) (V m) φ p ∂canonicalMeasure S K m) =
            ∫ p, n06MaterialJetRow T K β 0 F.val m 0 p * φ p ∂canonicalMeasure S K m) →
      ∃ P : N06PositiveWeakGraphFamily T K β loss F.val W.val a c V κ,
      ∃ G : Vol.level β 0 b,
        (∀ m, (Vol.forget β 0 b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          fun p => ∑ i : Fin 5, n06PositiveCubicMultipliers K A B C i m p *
            n06PositivePhysicalGraphFields P i m 0 p) ∧
        ‖G‖ ≤ (Q * δ) * (‖F‖ + ‖W‖) := by
  obtain ⟨Qgraph, hQgraph, hpack⟩ := n06_positiveWeakGraph_material_package
    hD hT hVol β Aexp loss hβ b a c V q κ Cref hgeometry
  let Q : ℝ := 25 * n06WeakAngularMultiplierCost b * Qgraph
  have hQ : 0 ≤ Q := mul_nonneg
    (mul_nonneg (by norm_num) (n06WeakAngularMultiplierCost_nonneg b)) hQgraph.le
  let scale : ℕ → ℝ := fun m =>
    T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ Aexp
  have hscale (m : ℕ) : 0 < scale m := by
    have hpos := hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))
    exact mul_pos (Real.rpow_pos_of_pos hpos.2.1 β) (Real.rpow_pos_of_pos hpos.2.2.1 Aexp)
  refine ⟨Q, hQ, ?_⟩
  intro δ hδ A B C hcoeff F W hweak
  obtain ⟨P, f, hfields, hjets, hparity, hfnorm⟩ := hpack F W hweak
  obtain ⟨G, hGfield, hGnorm⟩ := n06Volume_positiveCubicSource_of_fields hVol β b
    hgeometry.left hgeometry.right scale hscale δ hδ A B C hcoeff f hjets hparity
  refine ⟨P, G, ?_, ?_⟩
  · apply n06Volume_materialCubicSource_identity hD hT β Aexp b G
      (n06PositiveCubicMultipliers K A B C) f
      (fun i m => n06PositivePhysicalGraphFields P i m 0) _ hGfield
    intro i m
    rw [hfields i m]
    filter_upwards [Lp.coeFn_smul (T.E0 (T.sample (K.cell m)) ^ Aexp)
      (n06PositivePhysicalGraphFields P i m 0)] with p hp
    simpa only [PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] using hp
  · have hsum : (∑ i : Fin 5, ‖f i‖) ≤ 5 * (Qgraph * (‖F‖ + ‖W‖)) := by
      calc
        _ ≤ ∑ _i : Fin 5, Qgraph * (‖F‖ + ‖W‖) :=
          Finset.sum_le_sum (fun i _ => hfnorm i)
        _ = _ := by simp
    calc
      ‖G‖ ≤ (5 * n06WeakAngularMultiplierCost b) * δ * ∑ i : Fin 5, ‖f i‖ := hGnorm
      _ ≤ (5 * n06WeakAngularMultiplierCost b) * δ * (5 * (Qgraph * (‖F‖ + ‖W‖))) :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (mul_nonneg (by norm_num) (n06WeakAngularMultiplierCost_nonneg b)) hδ)
      _ = (Q * δ) * (‖F‖ + ‖W‖) := by dsimp only [Q]; ring

end ContinuousFlexibility.Statements
