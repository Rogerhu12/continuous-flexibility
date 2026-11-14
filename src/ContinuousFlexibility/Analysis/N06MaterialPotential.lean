module

public import ContinuousFlexibility.Analysis.N06WeakAngularMultiplierMap
public import ContinuousFlexibility.Analysis.N06VolumeLevelTransfer
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# A material-small potential between the actual volume weight levels

The coefficient's H^beta factor absorbs a fixed material loss. Only the
identity isometry of stored weak jets is used to change weight labels;
the compensating material factor remains in the physical multiplier.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem n06Volume_materialPotentialMultiplier
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hV : IsVolumeModel T S K V)
    (β A loss : ℝ) (hβ : 0 < β) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ a : ℕ → PolarPoint → ℝ,
      (∀ m, ContDiffOn ℝ ∞ (a m) (canonicalOpen S K m)) →
      (∀ m p, p ∈ canonicalOpen S K m → a m (p + (0, Real.pi)) = a m p) →
      (∀ m p, p ∈ canonicalOpen S K m → a m (p.1, Real.pi - p.2) = a m p) →
      (∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 i (a m) p| ≤
          δ * T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A) →
      ∃ P : V.level β (-loss) b →L[ℝ] V.level β 0 b,
        ‖P‖ ≤ Q * δ ∧
        ∀ W m, (V.forget β 0 b (P W) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          fun p => a m p * V.forget β (-loss) b W m p := by
  obtain ⟨Qmat, hQmat, habsorb⟩ := n06_material_loss_absorb hT β A loss hβ
  let I := n06VolumeLevelEquiv hV β (-loss) β 0 b
  let Q : ℝ := n06WeakAngularMultiplierCost b * Qmat
  have hQ : 0 ≤ Q := mul_nonneg (n06WeakAngularMultiplierCost_nonneg b) hQmat.le
  refine ⟨Q, hQ, ?_⟩
  intro δ hδ a ha hp heven hsmall
  let scale (m : ℕ) : ℝ := T.M (T.sample (K.cell m)) ^ loss
  have hsample (m : ℕ) : T.sample (K.cell m) ∈ Ioo D.a D.b :=
    spaces_trace_sample_mem hD hT (K.cell m)
  have hscale (m : ℕ) : 0 ≤ scale m :=
    Real.rpow_nonneg (zero_le_one.trans (hT.2.1 _ (hsample m)).2.2.2) _
  let c : ℕ → PolarPoint → ℝ := fun m p => scale m * a m p
  have hc (m : ℕ) : ContDiffOn ℝ ∞ (c m) (canonicalOpen S K m) :=
    contDiffOn_const.mul (ha m)
  have hcp (m : ℕ) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      c m (p + (0, Real.pi)) = c m p :=
    congrArg (fun v => scale m * v) (hp m p hpU)
  have hce (m : ℕ) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      c m (p.1, Real.pi - p.2) = c m p :=
    congrArg (fun v => scale m * v) (heven m p hpU)
  have hcsmall (m i : ℕ) (hi : i ≤ b) (p : PolarPoint) (hpU : p ∈ canonicalOpen S K m) :
      |mixedDerivative 0 i (c m) p| ≤ Qmat * δ := by
    change |mixedDerivative 0 i (fun q => scale m * a m q) p| ≤ _
    rw [spaces_mixedDerivative_const_mul, abs_mul, abs_of_nonneg (hscale m)]
    calc
      _ ≤ scale m *
          (δ * T.H (T.sample (K.cell m)) ^ β * T.E0 (T.sample (K.cell m)) ^ A) :=
        mul_le_mul_of_nonneg_left (hsmall m i hi p hpU) (hscale m)
      _ = δ * (T.H (T.sample (K.cell m)) ^ β *
          T.E0 (T.sample (K.cell m)) ^ A * scale m) := by ring
      _ ≤ δ * Qmat := mul_le_mul_of_nonneg_left (habsorb _ (hsample m)) hδ
      _ = Qmat * δ := mul_comm _ _
  obtain ⟨M, hMnorm, hMfield, _⟩ := n06Volume_exists_weakAngularMultiplierMap
    hV β 0 b c hc hcp hce (Qmat * δ) (mul_nonneg hQmat.le hδ) hcsmall
  let P : V.level β (-loss) b →L[ℝ] V.level β 0 b :=
    M.comp I.toLinearIsometry.toContinuousLinearMap
  refine ⟨P, ?_, ?_⟩
  · apply P.opNorm_le_bound (mul_nonneg hQ hδ)
    intro W
    calc
      ‖P W‖ = ‖M (I W)‖ := rfl
      _ ≤ (n06WeakAngularMultiplierCost b * (Qmat * δ)) * ‖I W‖ :=
        (M.le_opNorm _).trans (mul_le_mul_of_nonneg_right hMnorm (norm_nonneg _))
      _ = (n06WeakAngularMultiplierCost b * (Qmat * δ)) * ‖W‖ :=
        congrArg (fun r => (n06WeakAngularMultiplierCost b * (Qmat * δ)) * r) (I.norm_map W)
      _ = Q * δ * ‖W‖ := by dsimp only [Q]; ring
  · intro W m
    have hweight : V.forget β (-loss) b W m = scale m • V.forget β 0 b (I W) m :=
      n06VolumeLevelEquiv_material_forget hV β loss b W m
    have hweightAE : (V.forget β (-loss) b W m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] fun p => scale m * V.forget β 0 b (I W) m p := by
      have hco : (V.forget β (-loss) b W m : PolarPoint → ℝ) =
          ((scale m • V.forget β 0 b (I W) m : CanonicalL2 S K m) : PolarPoint → ℝ) :=
        congrArg (fun f : CanonicalL2 S K m => (f : PolarPoint → ℝ)) hweight
      exact (Filter.EventuallyEq.of_eq hco).trans (Lp.coeFn_smul (scale m) _)
    change (V.forget β 0 b (M (I W)) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a m p * V.forget β (-loss) b W m p
    filter_upwards [hMfield (I W) m, hweightAE] with p hprod hs
    rw [hprod, hs]
    change (scale m * a m p) * V.forget β 0 b (I W) m p =
      a m p * (scale m * V.forget β 0 b (I W) m p)
    ring

end ContinuousFlexibility.Statements
