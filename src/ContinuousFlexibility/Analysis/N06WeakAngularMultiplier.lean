module

public import ContinuousFlexibility.Analysis.N06WeakAngularLeibniz
public import ContinuousFlexibility.Analysis.N06MaterialAbsorption
public import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Bounded multiplication on the actual finite weak angular source level

Only coefficient derivatives through the fixed order are used. The
coefficient is smooth on each open canonical strip, and the source is an
arbitrary member of the original weak-jet subspace. The finite binomial
construction has a uniform piece norm bound, which sums in the original
canonical volume norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}

theorem n06_canonical_aestronglyMeasurable_of_continuousOn
    {a : PolarPoint → ℝ} (ha : ContinuousOn a (canonicalOpen S K m)) :
    AEStronglyMeasurable a (canonicalMeasure S K m) :=
  (ha.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
    (measurableSet_Ioo.prod measurableSet_Ioc)

/-- The genuine bounded coefficient product in the original canonical L² space. -/
def n06CanonicalMul (a : PolarPoint → ℝ)
    (ha : ContinuousOn a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ p ∈ canonicalOpen S K m, |a p| ≤ δ)
    (f : CanonicalL2 S K m) : CanonicalL2 S K m :=
  (n06_canonicalMemLp_bounded_mul
    (n06_canonical_aestronglyMeasurable_of_continuousOn ha)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      exact hδ p ⟨hp.1, mem_univ _⟩) f).toLp (fun p => a p * f p)

theorem n06CanonicalMul_ae (a : PolarPoint → ℝ)
    (ha : ContinuousOn a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ p ∈ canonicalOpen S K m, |a p| ≤ δ) (f : CanonicalL2 S K m) :
    (n06CanonicalMul a ha δ hδ f : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a p * f p := MemLp.coeFn_toLp _

theorem n06CanonicalMul_norm_le (a : PolarPoint → ℝ)
    (ha : ContinuousOn a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ p ∈ canonicalOpen S K m, |a p| ≤ δ) (f : CanonicalL2 S K m) :
    ‖n06CanonicalMul a ha δ hδ f‖ ≤ δ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [n06CanonicalMul_ae a ha δ hδ f,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpU
  rw [hp]
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hδ p ⟨hpU.1, mem_univ _⟩) (abs_nonneg _)

/-- A natural-index notation for a finite jet. Indices beyond its prescribed
order are zero and are never used in a binomial row through that order. -/
def n06CanonicalJetExtend
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) (j : ℕ) :
    CanonicalL2 S K m :=
  if hj : j < b + 1 then f ⟨j, hj⟩ else 0

theorem n06CanonicalJetExtend_apply
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (j : ℕ) (hj : j < b + 1) : n06CanonicalJetExtend f j = f ⟨j, hj⟩ := by
  simp only [n06CanonicalJetExtend, dif_pos hj]

@[simp] theorem n06CanonicalJetExtend_zero
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    n06CanonicalJetExtend f 0 = f 0 := by
  rw [n06CanonicalJetExtend_apply f 0 (Nat.zero_lt_succ b)]
  rfl

theorem n06CanonicalJetExtend_norm_le
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) (j : ℕ) :
    ‖n06CanonicalJetExtend f j‖ ≤ ‖f‖ := by
  by_cases hj : j < b + 1
  · rw [n06CanonicalJetExtend_apply f j hj]
    exact PiLp.norm_apply_le f ⟨j, hj⟩
  · simp only [n06CanonicalJetExtend, dif_neg hj, norm_zero]
    exact norm_nonneg _

/-- All coefficient/source products needed by the finite triangular formula. -/
def n06CanonicalJetProduct (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (i j : ℕ) : CanonicalL2 S K m :=
  if hi : i ≤ b then
    n06CanonicalMul (mixedDerivative 0 i a)
      (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) ha 0 i).continuousOn
      δ (hδ i hi) (n06CanonicalJetExtend f j)
  else 0

theorem n06CanonicalJetProduct_ae (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (i j : ℕ) (hi : i ≤ b) :
    (n06CanonicalJetProduct a ha δ hδ f i j : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => mixedDerivative 0 i a p * n06CanonicalJetExtend f j p := by
  rw [n06CanonicalJetProduct, dif_pos hi]
  exact n06CanonicalMul_ae _ _ _ _ _

theorem n06CanonicalJetProduct_norm_le (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (i j : ℕ) (hi : i ≤ b) :
    ‖n06CanonicalJetProduct a ha δ hδ f i j‖ ≤ δ * ‖f‖ := by
  rw [n06CanonicalJetProduct, dif_pos hi]
  exact (n06CanonicalMul_norm_le _ _ _ _ _).trans
    (mul_le_mul_of_nonneg_left (n06CanonicalJetExtend_norm_le f j) hδ0)

/-- The actual finite L² jet of the coefficient product. -/
def n06CanonicalJetMultiply (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m) :=
  WithLp.toLp 2 (fun k => n06WeakLeibnizRow (n06CanonicalJetProduct a ha δ hδ f) k.val)

theorem n06CanonicalJetMultiply_ae (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) (k : Fin (b + 1)) :
    (n06CanonicalJetMultiply a ha δ hδ f k : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => ∑ i ∈ Finset.range (k.val + 1),
        (k.val.choose i : ℝ) * mixedDerivative 0 i a p * n06CanonicalJetExtend f (k.val - i) p := by
  apply n06WeakLeibnizRow_ae
  intro i hi
  apply n06CanonicalJetProduct_ae
  have hi' := Finset.mem_range.mp hi
  have hk := k.isLt
  omega

theorem n06CanonicalJetMultiply_zero_ae (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    (n06CanonicalJetMultiply a ha δ hδ f 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => a p * f 0 p := by
  simpa only [Fin.val_zero, Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, one_mul, spaces_mixedDerivative_zero, Nat.sub_self,
    n06CanonicalJetExtend_zero] using n06CanonicalJetMultiply_ae a ha δ hδ f 0

theorem n06CanonicalJetMultiply_weak (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (hp : ∀ p ∈ canonicalOpen S K m, a (p + (0, Real.pi)) = a p)
    (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (hf : ∀ j : Fin (b + 1), WeakCanonicalAngularDerivative S K m (f 0) (f j) j.val) :
    ∀ k : Fin (b + 1), WeakCanonicalAngularDerivative S K m
      (n06CanonicalJetMultiply a ha δ hδ f 0)
      (n06CanonicalJetMultiply a ha δ hδ f k) k.val := by
  have hf' (j : ℕ) (hj : j < b) : WeakCanonicalAngularDerivative S K m
      (n06CanonicalJetExtend f j) (n06CanonicalJetExtend f (j + 1)) 1 := by
    have hj0 : j < b + 1 := by omega
    have hj1 : j + 1 < b + 1 := by omega
    rw [n06CanonicalJetExtend_apply f j hj0, n06CanonicalJetExtend_apply f (j + 1) hj1]
    exact (hf ⟨j, hj0⟩).n06_successive (hf ⟨j + 1, hj1⟩)
  intro k
  have h := n06_weakAngularLeibniz ha hp (n06CanonicalJetExtend f) b hf'
    (n06CanonicalJetProduct a ha δ hδ f) (n06CanonicalJetProduct_ae a ha δ hδ f)
    k.val (Nat.le_of_lt_succ k.isLt)
  change WeakCanonicalAngularDerivative S K m
    (n06WeakLeibnizRow (n06CanonicalJetProduct a ha δ hδ f) 0)
    (n06WeakLeibnizRow (n06CanonicalJetProduct a ha δ hδ f) k.val) k.val
  simpa only [n06WeakLeibnizRow_zero] using h

/-- A finite explicit cost, independent of the canonical cylinder. -/
def n06WeakAngularMultiplierCost (b : ℕ) : ℝ :=
  Real.sqrt (∑ k : Fin (b + 1), ((2 : ℝ) ^ k.val) ^ 2)

theorem n06WeakAngularMultiplierCost_nonneg (b : ℕ) :
    0 ≤ n06WeakAngularMultiplierCost b := Real.sqrt_nonneg _

private theorem n06CanonicalJetMultiply_row_norm_le (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) (k : Fin (b + 1)) :
    ‖n06CanonicalJetMultiply a ha δ hδ f k‖ ≤ (2 : ℝ) ^ k.val * (δ * ‖f‖) := by
  change ‖∑ i ∈ Finset.range (k.val + 1),
    k.val.choose i • n06CanonicalJetProduct a ha δ hδ f i (k.val - i)‖ ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range (k.val + 1),
        ‖k.val.choose i • n06CanonicalJetProduct a ha δ hδ f i (k.val - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k.val + 1), (k.val.choose i : ℝ) * (δ * ‖f‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hib : i ≤ b := by
        have hi' := Finset.mem_range.mp hi
        have hk := k.isLt
        omega
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (n06CanonicalJetProduct_norm_le a ha δ hδ0 hδ f i (k.val - i) hib)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose k.val

theorem n06CanonicalJetMultiply_norm_le (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    ‖n06CanonicalJetMultiply a ha δ hδ f‖ ≤ n06WeakAngularMultiplierCost b * δ * ‖f‖ := by
  have hsum : 0 ≤ ∑ k : Fin (b + 1), ((2 : ℝ) ^ k.val) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsquare : ‖n06CanonicalJetMultiply a ha δ hδ f‖ ^ 2 ≤
      (n06WeakAngularMultiplierCost b * δ * ‖f‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ k : Fin (b + 1), ((2 : ℝ) ^ k.val * (δ * ‖f‖)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
          (n06CanonicalJetMultiply_row_norm_le a ha δ hδ0 hδ f k)
      _ = (∑ k : Fin (b + 1), ((2 : ℝ) ^ k.val) ^ 2) * (δ * ‖f‖) ^ 2 := by
        simp only [mul_pow, Finset.sum_mul]
      _ = _ := by
        simp only [n06WeakAngularMultiplierCost, mul_pow, Real.sq_sqrt hsum]
        ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (n06WeakAngularMultiplierCost_nonneg b) hδ0) (norm_nonneg _))).mp hsquare

/-- Angular reflection preserves the exact half-period canonical measure,
including its endpoint convention up to null sets. -/
theorem n06_measurePreserving_canonicalAngularReflection :
    MeasurePreserving (fun p : PolarPoint => (p.1, Real.pi - p.2))
      (canonicalMeasure S K m) (canonicalMeasure S K m) := by
  letI : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hμ : canonicalMeasure S K m =
      ((volume : Measure ℝ).restrict (Ioo (K.left m) (K.right m))).prod angleMeasure := by
    change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) =
      ((volume : Measure ℝ).restrict (Ioo (K.left m) (K.right m))).prod
        ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) Real.pi))
    rw [← Measure.prod_restrict]
  rw [hμ]
  exact (MeasurePreserving.id _).prod measurePreserving_angleReflection

theorem n06CanonicalJetMultiply_reflection (a : PolarPoint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (canonicalOpen S K m))
    (heven : ∀ p ∈ canonicalOpen S K m, a (p.1, Real.pi - p.2) = a p)
    (δ : ℝ)
    (hδ : ∀ i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i a p| ≤ δ)
    (f : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m))
    (hf : (fun p : PolarPoint => f 0 (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
      (f 0 : PolarPoint → ℝ)) :
    (fun p : PolarPoint => n06CanonicalJetMultiply a ha δ hδ f 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (n06CanonicalJetMultiply a ha δ hδ f 0 : PolarPoint → ℝ) := by
  have hproduct := n06CanonicalJetMultiply_zero_ae a ha δ hδ f
  have hreflect := n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp
    hproduct
  filter_upwards [hreflect, hproduct, hf,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hr hp hfp hpU
  change n06CanonicalJetMultiply a ha δ hδ f 0 (p.1, Real.pi - p.2) =
    a (p.1, Real.pi - p.2) * f 0 (p.1, Real.pi - p.2) at hr
  rw [hr, hp, heven p ⟨hpU.1, mem_univ _⟩, hfp]

/-- A bounded strip-local smooth even coefficient acts on the actual
selected volume level. The output carries every binomial weak jet and
has the expected physical zeroth field after the original forget map. -/
theorem n06Volume_weakAngularMultiplier
    {T : MaterialData} {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (a : ℕ → PolarPoint → ℝ)
    (ha : ∀ m, ContDiffOn ℝ ∞ (a m) (canonicalOpen S K m))
    (hp : ∀ m p, p ∈ canonicalOpen S K m → a m (p + (0, Real.pi)) = a m p)
    (heven : ∀ m p, p ∈ canonicalOpen S K m → a m (p.1, Real.pi - p.2) = a m p)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m, |mixedDerivative 0 i (a m) p| ≤ δ)
    (F : V.level γ t b) :
    ∃ G : V.level γ t b,
      (∀ m (k : Fin (b + 1)),
        (G.val m k : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          fun p => ∑ i ∈ Finset.range (k.val + 1),
            (k.val.choose i : ℝ) * mixedDerivative 0 i (a m) p *
              n06CanonicalJetExtend (F.val m) (k.val - i) p) ∧
      (∀ m, (V.forget γ t b G m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => a m p * V.forget γ t b F m p) ∧
      ‖G‖ ≤ n06WeakAngularMultiplierCost b * δ * ‖F‖ := by
  have hF : F.val ∈ canonicalVolumeGraph S K b := by
    rw [← hV.1 γ t b]
    exact F.property
  let J : ∀ m, PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m) :=
    fun m => n06CanonicalJetMultiply (a m) (ha m) δ (hδ m) (F.val m)
  have hJnorm (m : ℕ) : ‖J m‖ ≤
      (n06WeakAngularMultiplierCost b * δ) * (‖F.val m‖ + ‖(0 : CanonicalVolumeJets S K b) m‖) := by
    simpa only [lp.coeFn_zero, Pi.zero_apply, norm_zero, add_zero, mul_assoc] using
      n06CanonicalJetMultiply_norm_le (a m) (ha m) δ hδ0 (hδ m) (F.val m)
  have hJreflection (m : ℕ) :
      (fun p : PolarPoint => J m 0 (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
        (J m 0 : PolarPoint → ℝ) :=
    n06CanonicalJetMultiply_reflection (a m) (ha m) (heven m) δ (hδ m) (F.val m) (hF.1 m)
  have hJweak (m : ℕ) (k : Fin (b + 1)) :
      WeakCanonicalAngularDerivative S K m (J m 0) (J m k) k.val :=
    n06CanonicalJetMultiply_weak (a m) (ha m) (hp m) δ (hδ m) (F.val m) (hF.2 m) k
  obtain ⟨G, hG, hforget, hnorm⟩ := n06Volume_of_piecewise_sum_bound hV γ t b F.val 0 J
    (mul_nonneg (n06WeakAngularMultiplierCost_nonneg b) hδ0) hJnorm hJreflection hJweak
  refine ⟨G, ?_, ?_, ?_⟩
  · intro m k
    rw [hG m]
    exact n06CanonicalJetMultiply_ae (a m) (ha m) δ (hδ m) (F.val m) k
  · intro m
    let w : ℝ := T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ
    rw [hforget m, hV.2.2.2 γ t b F m]
    filter_upwards [Lp.coeFn_smul w (J m 0), Lp.coeFn_smul w (F.val m 0),
      n06CanonicalJetMultiply_zero_ae (a m) (ha m) δ (hδ m) (F.val m)] with p hleft hright hbase
    change (w • J m 0) p = a m p * (w • F.val m 0) p
    rw [hleft, hright]
    simp only [Pi.smul_apply, smul_eq_mul]
    change w * J m 0 p = a m p * (w * F.val m 0 p)
    rw [hbase]
    ring
  · change ‖G‖ ≤ n06WeakAngularMultiplierCost b * δ * ‖F.val‖
    simpa only [norm_zero, add_zero, mul_assoc] using hnorm

end ContinuousFlexibility.Statements
