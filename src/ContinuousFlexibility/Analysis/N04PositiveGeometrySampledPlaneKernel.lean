import ContinuousFlexibility.Analysis.N04PositiveGeometryCoefficientPlaneWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFiniteCalculus
import ContinuousFlexibility.Analysis.PolynomialJetComposition

/-!
# One sample envelope for finite coefficient kernels on the plane

The ordinary kernel bounds are collected on their actual evaluation
set before choosing a state, a word or its directions. All coefficients
and finite partition factors are absorbed into one material power; the
parameter height and the saved word cost remain outside that power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E F Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem n04PositiveGeometry_sampledPlaneKernel_saved_prefix
    (E₀ : I → ℝ) (hE : ∀ i, 1 ≤ E₀ i)
    (V Ω : I → Set (F × ℝ)) (g : I → F × ℝ → Z)
    (hV : ∀ i, IsOpen (V i)) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (V i))
    (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A)
    (hkernel : ∀ k : ℕ, k ≤ N → ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i y, y ∈ Ω i → ‖iteratedFDeriv ℝ k (g i) y‖ ≤ C * E₀ i ^ P) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (U : Set E), IsOpen U → ∀ f : E × ℝ → F,
      ∀ J : SmoothDirections (U ×ˢ univ) f, ∀ i,
      MapsTo (fun z : E × PolarPoint => (f (z.1, z.2.2), z.2.1)) (U ×ˢ univ) (V i) →
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun z : E × PolarPoint => g i (f (z.1, z.2.2), z.2.1)),
      ∀ (p q : Seminorm ℝ E) (R H t : ℝ), 0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ (K s shift : ℕ) (x : E), x ∈ U → ∀ y : PolarPoint,
      (f (x, y.2), y.1) ∈ Ω i →
      N04BoundaryWordBounds J K (s + K) 1 x y.2
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * E₀ i ^ A) H t shift →
      ∀ n : ℕ, 0 < n → n ≤ N → n ≤ K + s + 1 →
      ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × PolarPoint,
      (∀ j, if w.isState j then (v j).2 = 0 else (v j).1 = 0) →
      (∀ j, p (v j).1 ≤ 1 ∧ q (v j).1 ≤ R ∧ ‖(v j).2‖ ≤ 1) →
        ‖Q.D n (x, y) v‖ ≤ B * E₀ i ^ B * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := by
  classical
  obtain ⟨C, P, _, _, houter⟩ := finite_polynomial_majorant E₀ hE Ω
    (fun k i y => ‖iteratedFDeriv ℝ k (g i) y‖) N hkernel
  obtain ⟨B₀, _, hpackOuter⟩ := coefficientEnvelope_pack C P
  let D : ℝ := max 1 (max A (max B₀ RH))
  have hD : 1 ≤ D := le_max_left _ _
  have hAD : A ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hB₀D : B₀ ≤ D := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hRHD : RH ≤ D := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let count : ℝ := 1 + ∑ j : Fin (N + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)
  have hcount : 1 ≤ count := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hcard (n : ℕ) (hn : n ≤ N) : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ count :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition j.val)))
      (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (N + 1)))).trans
        (le_add_of_nonneg_left zero_le_one)
  obtain ⟨B₁, _, hpack⟩ := n04PositiveGeometry_polynomial_sample_pack count D (2 * N + 1)
  let B : ℝ := max 1 B₁
  have hB : 1 ≤ B := le_max_left _ _
  have hB₁ : B₁ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro U hU f J i hmap Q p q R H t hR hH hHR ht K s shift x hx y hy hraw
    n hn hnN hns w hw v hpure hbox
  let M : ℝ := D * E₀ i ^ D
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow (hE i) (zero_le_one.trans hD))
  have hraise {a : ℝ} (ha : a ≤ D) : a * E₀ i ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le (hE i) ha)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) (zero_le_one.trans hD)
  have hDM : D ≤ M := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_rpow (hE i) (zero_le_one.trans hD)) (zero_le_one.trans hD)
  have hJM : N04BoundaryWordBounds J K (s + K) 1 x y.2
      (fun a => p a ≤ 1 ∧ q a ≤ R) M H t shift :=
    hraw.enlarge hH (zero_le_one.trans ht) (hraise hAD)
  have houterM (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (g i) (f (x, y.2), y.1)‖ ≤ M :=
    (houter j (hj.trans hnN) i _ hy).trans ((hpackOuter (E₀ i) (hE i)).trans (hraise hB₀D))
  have hb := n04PositiveGeometry_boundaryKernel_plane_saved_bound hU J (hV i) (hg i)
    hmap Q p q hR (zero_le_one.trans hM) hM hH (hHR.trans (hRHD.trans hDM)) ht
    K s shift x hx y hJM hn hns w hw houterM v hpure hbox
  have hcost : (Fintype.card (OrderedFinpartition n) : ℝ) * M * M ^ n * M ^ n ≤
      B * E₀ i ^ B := by
    calc
      _ = (Fintype.card (OrderedFinpartition n) : ℝ) * M ^ (2 * n + 1) := by
        rw [show 2 * n + 1 = (n + n) + 1 by omega, pow_succ, pow_add]
        ring
      _ ≤ count * M ^ (2 * N + 1) := mul_le_mul (hcard n hnN)
        (pow_le_pow_right₀ hM (by omega)) (pow_nonneg (zero_le_one.trans hM) _)
        (zero_le_one.trans hcount)
      _ ≤ B₁ * E₀ i ^ B₁ := hpack (E₀ i) (hE i)
      _ ≤ B * E₀ i ^ B := mul_le_mul hB₁
        (Real.rpow_le_rpow_of_exponent_le (hE i) hB₁)
        (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) (zero_le_one.trans hB)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
