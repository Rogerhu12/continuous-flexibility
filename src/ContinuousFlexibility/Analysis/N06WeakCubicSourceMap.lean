import ContinuousFlexibility.Analysis.N06WeakCubicSource
import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation
import ContinuousFlexibility.Analysis.N06PairingLinearLifting

/-!
# The continuous linear source determined by its actual weak equation

The five graph fields need only exist for each input. Their actual cubic
pairing determines one source in the original volume level. Canonical
tests separate the original L2 classes, and the original forget map is
injective, so the source is linear in the input. The construction retains
the same physical source supplied by the five-field multiplication.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S}

/-- Integration against any original L2 test is a linear functional on
the original L2 field. This includes the actual divergence of a compact
canonical test for locally smooth coefficients. -/
def n06CanonicalLpPairing {m : ℕ} (φ : PolarPoint → ℝ)
    (hφ : MemLp φ 2 (canonicalMeasure S K m)) : CanonicalL2 S K m →ₗ[ℝ] ℝ where
  toFun f := ∫ p, f p * φ p ∂canonicalMeasure S K m
  map_add' f g := by
    calc
      _ = ∫ p, (f p * φ p + g p * φ p) ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with p hp
        rw [hp]
        simp only [Pi.add_apply, add_mul]
      _ = _ := integral_add ((Lp.memLp f).integrable_mul hφ) ((Lp.memLp g).integrable_mul hφ)
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    calc
      _ = ∫ p, c * (f p * φ p) ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with p hp
        rw [hp]
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      _ = _ := integral_const_mul _ _

abbrev N06CanonicalTestIndex (S : PhysicalSpacesData) (K : CanonicalData S) :=
  Σ m : ℕ, {φ : PolarPoint → ℝ // CanonicalTest S K m φ}

/-- A canonical test observes the physical zeroth field of the selected
volume level, including its material and height weight. -/
def n06VolumeTestPairing (V : VolumeModelData S K) (γ t : ℝ) (b : ℕ)
    (τ : N06CanonicalTestIndex S K) : V.level γ t b →ₗ[ℝ] ℝ :=
  (n06CanonicalPairing τ.2.val τ.2.property.1.continuous).comp
    ((LinearMap.proj τ.1).comp (V.forget γ t b))

theorem n06VolumeTestPairing_injective
    {T : MaterialData} {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) :
    Function.Injective (fun G : V.level γ t b => fun τ => n06VolumeTestPairing V γ t b τ G) := by
  intro F G h
  apply hV.2.2.1 γ t b
  funext m
  apply n06_canonicalL2_test_ext
  intro φ hφ
  exact congrFun h ⟨m, ⟨φ, hφ⟩⟩

/-- The right hand side of the distributional source equation is linear
in the original canonical height. The test operator may be the actual
cubic divergence operator; its compact-test L2 property is the only
regularity needed by this algebraic construction. -/
def n06CanonicalDistributionTestPairing
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (U : E →ₗ[ℝ] CanonicalSequence S K)
    (testOp : ℕ → (PolarPoint → ℝ) → PolarPoint → ℝ)
    (htestOp : ∀ m φ, CanonicalTest S K m φ → MemLp (testOp m φ) 2 (canonicalMeasure S K m))
    (τ : N06CanonicalTestIndex S K) : E →ₗ[ℝ] ℝ :=
  (n06CanonicalLpPairing (testOp τ.1 τ.2.val)
    (htestOp τ.1 τ.2.val τ.2.property)).comp ((LinearMap.proj τ.1).comp U)

/-- A bounded source for each input, identified by the actual weak
pairing, gives a continuous linear map on the chosen source space.
Uniqueness keeps its value equal to every source already constructed
from the five actual graph fields. -/
theorem n06Volume_sourceMap_of_weak_pairing
    {T : MaterialData} {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ t : ℝ) (b : ℕ) (U : E →ₗ[ℝ] CanonicalSequence S K)
    (testOp : ℕ → (PolarPoint → ℝ) → PolarPoint → ℝ)
    (htestOp : ∀ m φ, CanonicalTest S K m φ → MemLp (testOp m φ) 2 (canonicalMeasure S K m))
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hex : ∀ F : E, ∃ G : V.level γ t b,
      (∀ m φ, CanonicalTest S K m φ →
        (∫ p, V.forget γ t b G m p * φ p ∂canonicalMeasure S K m) =
          ∫ p, U F m p * testOp m φ p ∂canonicalMeasure S K m) ∧
      ‖G‖ ≤ Q * ‖F‖) :
    ∃ M : E →L[ℝ] V.level γ t b, ‖M‖ ≤ Q ∧
      (∀ F m φ, CanonicalTest S K m φ →
        (∫ p, V.forget γ t b (M F) m p * φ p ∂canonicalMeasure S K m) =
          ∫ p, U F m p * testOp m φ p ∂canonicalMeasure S K m) ∧
      (∀ F (G : V.level γ t b),
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget γ t b G m p * φ p ∂canonicalMeasure S K m) =
            ∫ p, U F m p * testOp m φ p ∂canonicalMeasure S K m) → M F = G) := by
  have hbounded (F : E) : ∃ G : V.level γ t b,
      (∀ τ, n06VolumeTestPairing V γ t b τ G =
        n06CanonicalDistributionTestPairing U testOp htestOp τ F) ∧
        ‖G‖ ≤ Q * ‖F‖ := by
    obtain ⟨G, hGpair, hGnorm⟩ := hex F
    exact ⟨G, (fun τ => hGpair τ.1 τ.2.val τ.2.property), hGnorm⟩
  obtain ⟨M, hMnorm, hMpair, hMunique⟩ := n06_exists_clm_of_separating_pairings
    (n06VolumeTestPairing V γ t b) (n06VolumeTestPairing_injective hV γ t b)
    (n06CanonicalDistributionTestPairing U testOp htestOp) hQ hbounded
  refine ⟨M, hMnorm, ?_, ?_⟩
  · intro F m φ hφ
    exact hMpair F ⟨m, ⟨φ, hφ⟩⟩
  · intro F G hG
    exact hMunique F G (fun τ => hG τ.1 τ.2.val τ.2.property)

/-- The graph estimate fixes `Q` before `δ` and the primitive coefficient
parameter. The linear lifting preserves this quantifier order exactly. -/
theorem n06Volume_sourceMap_family_of_weak_pairing
    {T : MaterialData} {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ t : ℝ) (b : ℕ) (U : E →ₗ[ℝ] CanonicalSequence S K)
    (admissible : ℝ → Z → Prop)
    (testOp : Z → ℕ → (PolarPoint → ℝ) → PolarPoint → ℝ)
    (htestOp : ∀ δ, 0 ≤ δ → ∀ z, admissible δ z →
      ∀ m φ, CanonicalTest S K m φ → MemLp (testOp z m φ) 2 (canonicalMeasure S K m))
    (hex : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ z : Z, admissible δ z → ∀ F : E, ∃ G : V.level γ t b,
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget γ t b G m p * φ p ∂canonicalMeasure S K m) =
            ∫ p, U F m p * testOp z m φ p ∂canonicalMeasure S K m) ∧
        ‖G‖ ≤ (Q * δ) * ‖F‖) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ z : Z, admissible δ z → ∃ M : E →L[ℝ] V.level γ t b,
        ‖M‖ ≤ Q * δ ∧
        (∀ F m φ, CanonicalTest S K m φ →
          (∫ p, V.forget γ t b (M F) m p * φ p ∂canonicalMeasure S K m) =
            ∫ p, U F m p * testOp z m φ p ∂canonicalMeasure S K m) ∧
        (∀ F (G : V.level γ t b),
          (∀ m φ, CanonicalTest S K m φ →
            (∫ p, V.forget γ t b G m p * φ p ∂canonicalMeasure S K m) =
              ∫ p, U F m p * testOp z m φ p ∂canonicalMeasure S K m) → M F = G) := by
  obtain ⟨Q, hQ, hfamily⟩ := hex
  refine ⟨Q, hQ, ?_⟩
  intro δ hδ z hz
  exact n06Volume_sourceMap_of_weak_pairing hV γ t b U (testOp z)
    (htestOp δ hδ z hz) (mul_nonneg hQ hδ) (hfamily δ hδ z hz)

end ContinuousFlexibility.Statements
