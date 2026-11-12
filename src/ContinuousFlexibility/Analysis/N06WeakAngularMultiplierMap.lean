import ContinuousFlexibility.Analysis.N06WeakAngularMultiplier

/-!
# The continuous linear weak angular multiplier

The actual product in the selected volume level is unique because its
original forget map is injective. This proves linearity of the constructed
weak product and retains its explicit operator norm and every binomial jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Multiplication is a bounded endomorphism of the same actual source
level, including all weak angular jets through the chosen fixed order. -/
theorem n06Volume_exists_weakAngularMultiplierMap
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (a : ℕ → PolarPoint → ℝ)
    (ha : ∀ m, ContDiffOn ℝ ∞ (a m) (canonicalOpen S K m))
    (hp : ∀ m p, p ∈ canonicalOpen S K m → a m (p + (0, Real.pi)) = a m p)
    (heven : ∀ m p, p ∈ canonicalOpen S K m → a m (p.1, Real.pi - p.2) = a m p)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i (a m) p| ≤ δ) :
    ∃ M : V.level γ t b →L[ℝ] V.level γ t b,
      ‖M‖ ≤ n06WeakAngularMultiplierCost b * δ ∧
      (∀ F m, (V.forget γ t b (M F) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => a m p * V.forget γ t b F m p) ∧
      (∀ F m (k : Fin (b + 1)),
        ((M F).val m k : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          fun p => ∑ i ∈ Finset.range (k.val + 1),
            (k.val.choose i : ℝ) * mixedDerivative 0 i (a m) p *
              n06CanonicalJetExtend (F.val m) (k.val - i) p) := by
  choose W hWjets hWfield hWnorm using
    (fun F : V.level γ t b =>
      n06Volume_weakAngularMultiplier hV γ t b a ha hp heven δ hδ0 hδ F)
  let W₀ : V.level γ t b →ₗ[ℝ] V.level γ t b :=
    { toFun := W
      map_add' := by
        intro F G
        apply hV.2.2.1 γ t b
        funext m
        simp only [map_add, Pi.add_apply]
        apply Lp.ext
        have hsum := hWfield (F + G) m
        simp only [map_add, Pi.add_apply] at hsum
        filter_upwards [hsum, hWfield F m, hWfield G m,
          Lp.coeFn_add (V.forget γ t b F m) (V.forget γ t b G m),
          Lp.coeFn_add (V.forget γ t b (W F) m) (V.forget γ t b (W G) m)]
          with p hsum hF hG hin hout
        rw [hsum, hout]
        simp only [Pi.add_apply]
        rw [hF, hG, hin]
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c F
        apply hV.2.2.1 γ t b
        funext m
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
        apply Lp.ext
        have hsmul := hWfield (c • F) m
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] at hsmul
        filter_upwards [hsmul, hWfield F m,
          Lp.coeFn_smul c (V.forget γ t b F m),
          Lp.coeFn_smul c (V.forget γ t b (W F) m)] with p hc hF hin hout
        rw [hc, hout]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hF, hin]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
  have hbound : ∀ F, ‖W₀ F‖ ≤ (n06WeakAngularMultiplierCost b * δ) * ‖F‖ :=
    hWnorm
  let M := W₀.mkContinuous (n06WeakAngularMultiplierCost b * δ) hbound
  refine ⟨M, W₀.mkContinuous_norm_le
    (mul_nonneg (n06WeakAngularMultiplierCost_nonneg b) hδ0) hbound, ?_, ?_⟩
  · exact hWfield
  · exact hWjets

/-- Physical multiplication determines this operator uniquely, so its
construction introduces no choice of product or of weak representatives. -/
theorem n06Volume_weakAngularMultiplierMap_unique
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {b : ℕ} {a : ℕ → PolarPoint → ℝ}
    {M N : V.level γ t b →L[ℝ] V.level γ t b}
    (hM : ∀ F m, (V.forget γ t b (M F) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a m p * V.forget γ t b F m p)
    (hN : ∀ F m, (V.forget γ t b (N F) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a m p * V.forget γ t b F m p) : M = N := by
  apply ContinuousLinearMap.ext
  intro F
  apply hV.2.2.1 γ t b
  funext m
  exact Lp.ext ((hM F m).trans (hN F m).symm)

end ContinuousFlexibility.Statements
