module

public import ContinuousFlexibility.Analysis.N06WeakAngularMultiplier

/-!
# Products of weak jets with a common reflection sign

The input is the original canonical lp array of weak angular jets, with
no evenness assumption. A coefficient with the same reflection sign as
its zeroth field makes an even product. This covers both even times even
and odd times odd, without introducing a new source space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}

/-- The two real reflection factors have the same sign, encoded exactly
by its square being one. Representatives are transported through the
actual measure-preserving angular reflection before multiplication. -/
theorem n06CanonicalJetMultiply_sameParity (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (σ : ℝ) (hσ : σ ^ 2 = 1)
    (haσ : ∀ p ∈ canonicalOpen S K m, a (p.1, Real.pi - p.2) = σ * a p)
    (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (hfσ : (fun p : PolarPoint => f 0 (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
      fun p => σ * f 0 p) :
    (fun p : PolarPoint => n06CanonicalJetMultiply a ha δ hδ f 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (n06CanonicalJetMultiply a ha δ hδ f 0 : PolarPoint → ℝ) := by
  have hproduct := n06CanonicalJetMultiply_zero_ae a ha δ hδ f
  have hreflect := n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp
    hproduct
  filter_upwards [hreflect, hproduct, hfσ,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hr hp hfp hpU
  change n06CanonicalJetMultiply a ha δ hδ f 0 (p.1, Real.pi - p.2) =
    a (p.1, Real.pi - p.2) * f 0 (p.1, Real.pi - p.2) at hr
  rw [hr, hp, haσ p ⟨hpU.1, mem_univ _⟩, hfp]
  calc
    (σ * a p) * (σ * f 0 p) = σ ^ 2 * (a p * f 0 p) := by ring
    _ = a p * f 0 p := by rw [hσ, one_mul]

/-- A coefficient product of matching-parity weak jets belongs to the
selected even volume level. The source array itself need not be even. -/
theorem n06Volume_weakJetProduct
    {T : MaterialData} {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (a : ℕ → PolarPoint → ℝ)
    (ha : ∀ m, ContDiffOn ℝ ∞ (a m) (canonicalOpen S K m))
    (hp : ∀ m p, p ∈ canonicalOpen S K m → a m (p + (0, Real.pi)) = a m p)
    (σ : ℕ → ℝ) (hσ : ∀ m, σ m ^ 2 = 1)
    (haσ : ∀ m p, p ∈ canonicalOpen S K m → a m (p.1, Real.pi - p.2) = σ m * a m p)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i (a m) p| ≤ δ)
    (f : CanonicalVolumeJets S K b)
    (hf : ∀ m (j : Fin (b + 1)), WeakCanonicalAngularDerivative S K m (f m 0) (f m j) j.val)
    (hfσ : ∀ m, (fun p : PolarPoint => f m 0 (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
      fun p => σ m * f m 0 p) :
    ∃ G : V.level γ t b,
      (∀ m (k : Fin (b + 1)),
        (G.val m k : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          fun p => ∑ i ∈ Finset.range (k.val + 1),
            (k.val.choose i : ℝ) * mixedDerivative 0 i (a m) p *
              n06CanonicalJetExtend (f m) (k.val - i) p) ∧
      (∀ m, (V.forget γ t b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) *
          (a m p * f m 0 p)) ∧
      ‖G‖ ≤ n06WeakAngularMultiplierCost b * δ * ‖f‖ := by
  let J : ∀ m, PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m) :=
    fun m => n06CanonicalJetMultiply (a m) (ha m) δ (hδ m) (f m)
  have hJnorm (m : ℕ) : ‖J m‖ ≤
      (n06WeakAngularMultiplierCost b * δ) * (‖f m‖ + ‖(0 : CanonicalVolumeJets S K b) m‖) := by
    simpa only [lp.coeFn_zero, Pi.zero_apply, norm_zero, add_zero, mul_assoc] using
      n06CanonicalJetMultiply_norm_le (a m) (ha m) δ hδ0 (hδ m) (f m)
  have hJreflection (m : ℕ) :
      (fun p : PolarPoint => J m 0 (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
        (J m 0 : PolarPoint → ℝ) :=
    n06CanonicalJetMultiply_sameParity (a m) (ha m) (σ m) (hσ m) (haσ m)
      δ (hδ m) (f m) (hfσ m)
  have hJweak (m : ℕ) (k : Fin (b + 1)) :
      WeakCanonicalAngularDerivative S K m (J m 0) (J m k) k.val :=
    n06CanonicalJetMultiply_weak (a m) (ha m) (hp m) δ (hδ m) (f m) (hf m) k
  obtain ⟨G, hG, hforget, hnorm⟩ := n06Volume_of_piecewise_sum_bound hV γ t b f 0 J
    (mul_nonneg (n06WeakAngularMultiplierCost_nonneg b) hδ0) hJnorm hJreflection hJweak
  refine ⟨G, ?_, ?_, ?_⟩
  · intro m k
    rw [hG m]
    exact n06CanonicalJetMultiply_ae (a m) (ha m) δ (hδ m) (f m) k
  · intro m
    let w : ℝ := T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ
    rw [hforget m]
    filter_upwards [Lp.coeFn_smul w (J m 0),
      n06CanonicalJetMultiply_zero_ae (a m) (ha m) δ (hδ m) (f m)] with p hs hbase
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul]
    change w * J m 0 p = w * (a m p * f m 0 p)
    exact congrArg (fun v => w * v) hbase
  · simpa only [norm_zero, add_zero, mul_assoc] using hnorm

/-- A finite sum of same-parity products remains in the original source.
Taking the index type to be `Fin 5` gives the five graph-field synthesis. -/
theorem n06Volume_weakJetProduct_sum
    {T : MaterialData} {V : VolumeModelData S K} {ι : Type*} [Fintype ι]
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (b : ℕ)
    (a : ι → ℕ → PolarPoint → ℝ)
    (ha : ∀ i m, ContDiffOn ℝ ∞ (a i m) (canonicalOpen S K m))
    (hp : ∀ i m p, p ∈ canonicalOpen S K m → a i m (p + (0, Real.pi)) = a i m p)
    (σ : ι → ℕ → ℝ) (hσ : ∀ i m, σ i m ^ 2 = 1)
    (haσ : ∀ i m p, p ∈ canonicalOpen S K m →
      a i m (p.1, Real.pi - p.2) = σ i m * a i m p)
    (δ : ι → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hδ : ∀ i m j, j ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 j (a i m) p| ≤ δ i)
    (f : ι → CanonicalVolumeJets S K b)
    (hf : ∀ i m (j : Fin (b + 1)),
      WeakCanonicalAngularDerivative S K m (f i m 0) (f i m j) j.val)
    (hfσ : ∀ i m, (fun p : PolarPoint => f i m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => σ i m * f i m 0 p) :
    ∃ G : V.level γ t b,
      (∀ m, (V.forget γ t b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => ∑ i, (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) *
          (a i m p * f i m 0 p)) ∧
      ‖G‖ ≤ n06WeakAngularMultiplierCost b * ∑ i, δ i * ‖f i‖ := by
  classical
  choose Y _hYjets hYfield hYnorm using
    (fun i => n06Volume_weakJetProduct hV γ t b (a i) (ha i) (hp i) (σ i) (hσ i)
      (haσ i) (δ i) (hδ0 i) (hδ i) (f i) (hf i) (hfσ i))
  let G : V.level γ t b := ∑ i, Y i
  refine ⟨G, ?_, ?_⟩
  · intro m
    have hforget : V.forget γ t b G m = ∑ i, V.forget γ t b (Y i) m := by
      simp only [G, map_sum, Finset.sum_apply]
    rw [hforget]
    have hsum := eventuallyEq_sum (s := Finset.univ) (fun i _ => hYfield i m)
    refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => V.forget γ t b (Y i) m)).trans ?_
    filter_upwards [hsum] with p hp
    simpa only [Finset.sum_apply] using hp
  · calc
      ‖G‖ ≤ ∑ i, ‖Y i‖ := norm_sum_le _ _
      _ ≤ ∑ i, n06WeakAngularMultiplierCost b * δ i * ‖f i‖ :=
        Finset.sum_le_sum (fun i _ => hYnorm i)
      _ = n06WeakAngularMultiplierCost b * ∑ i, δ i * ‖f i‖ := by
        simp only [Finset.mul_sum, mul_assoc]

end ContinuousFlexibility.Statements
