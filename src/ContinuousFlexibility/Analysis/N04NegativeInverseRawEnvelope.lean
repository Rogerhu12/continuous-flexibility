import ContinuousFlexibility.Analysis.N04NegativeInverseFiniteEnvelope
import ContinuousFlexibility.Analysis.N04NegativeInverseRawPrefixBridge

/-!
# Common material constants for normalized point and height jets

The constant is selected before the sample and before any geometric
inverse system. This is the coefficient closure needed to apply the
pointwise raw bridge simultaneously to all negative components.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem n04NegativeInverse_partitionMajorant_prefix_envelope
    (N : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ E : ℝ, 1 ≤ E → ∀ C M L : ℝ,
      0 ≤ C → 0 ≤ M → 0 ≤ L →
      C ≤ B * E ^ B → M ≤ B * E ^ B → L ≤ B * E ^ B →
      ∀ n : ℕ, n ≤ N →
        n04NegativeInverse_partitionMajorant C M L n ≤ D * E ^ D := by
  classical
  choose d hd hb using
    (fun i : Fin (N + 1) => n04NegativeInverse_partitionMajorant_envelope i.val hB)
  let D : ℝ := 1 + ∑ i : Fin (N + 1), d i
  have hD : 1 ≤ D := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => (hd i).le))
  refine ⟨D, hD, ?_⟩
  intro E hE C M L hC hM hL hCB hMB hLB n hn
  let i : Fin (N + 1) := ⟨n, by omega⟩
  have hi : d i ≤ D := by
    have hs := Finset.single_le_sum (fun j _ => (hd j).le) (Finset.mem_univ i)
    dsimp only [D]
    linarith
  exact (hb i E hE C M L hC hM hL hCB hMB hLB).trans
    (n04NegativeInverse_envelope_mono (zero_le_one.trans hD) hi hE)

/-- Both finite inverse and pulled-height majorants, including every
fixed affine target cost through order `N`, admit a common material
envelope chosen independently of the sample. -/
theorem n04NegativeInverse_normalizedMajorants_envelope
    (N : ℕ) {B L : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ E : ℝ, 1 ≤ E →
      let C := B * E ^ B
      let M := n04NegativeInverse_prefixMajorant (2 * C * C) C L N
      M * C ^ N ≤ D * E ^ D ∧
      ∀ n : ℕ, n ≤ N →
        n04NegativeInverse_partitionMajorant C M L n * C ^ N ≤ D * E ^ D := by
  obtain ⟨A₀, hA₀, ha⟩ := coefficientEnvelope_pack (2 * B * B) (B + B)
  let A : ℝ := max 1 (max B A₀)
  have hA : 1 ≤ A := le_max_left _ _
  have hBA : B ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hA₀A : A₀ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨M₀, hM₀, hprefix⟩ :=
    n04NegativeInverse_prefixMajorant_envelope_fixed_height N hA hL
  let A' : ℝ := max 1 (max B (max M₀ L))
  have hA' : 1 ≤ A' := le_max_left _ _
  have hBA' : B ≤ A' := (le_max_left _ _).trans (le_max_right _ _)
  have hMA' : M₀ ≤ A' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLA' : L ≤ A' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨P₀, hP₀, hpartition⟩ :=
    n04NegativeInverse_partitionMajorant_prefix_envelope N hA'
  let D₀ : ℝ := max M₀ P₀
  have hD₀ : 1 ≤ D₀ := hP₀.trans (le_max_right _ _)
  obtain ⟨D₁, hD₁, hpack⟩ :=
    coefficientEnvelope_pack (D₀ * B ^ N) (D₀ + B * (N : ℝ))
  let D : ℝ := max 1 D₁
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D, hD, ?_⟩
  intro E hE
  let C : ℝ := B * E ^ B
  let M : ℝ := n04NegativeInverse_prefixMajorant (2 * C * C) C L N
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hC : 1 ≤ C := n04NegativeInverse_envelope_one_le hB hE
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have ha0 : 0 ≤ 2 * C * C := mul_nonneg (mul_nonneg (by norm_num) hC0) hC0
  have hCA : C ≤ A * E ^ A :=
    n04NegativeInverse_envelope_mono (zero_le_one.trans hA) hBA hE
  have haA : 2 * C * C ≤ A * E ^ A := by
    have he : 2 * C * C = (2 * B * B) * E ^ (B + B) := by
      dsimp only [C]
      rw [Real.rpow_add (zero_lt_one.trans_le hE)]
      ring
    rw [he]
    exact (ha E hE).trans
      (n04NegativeInverse_envelope_mono (zero_le_one.trans hA) hA₀A hE)
  have hM : 1 ≤ M :=
    n04NegativeInverse_prefixMajorant_one_le ha0 hC0 (zero_le_one.trans hL) N
  have hMbound : M ≤ M₀ * E ^ M₀ := hprefix E hE _ _ ha0 hC0 haA hCA
  have hCA' : C ≤ A' * E ^ A' :=
    n04NegativeInverse_envelope_mono (zero_le_one.trans hA') hBA' hE
  have hMA'bound : M ≤ A' * E ^ A' := hMbound.trans
    (n04NegativeInverse_envelope_mono (zero_le_one.trans hA') hMA' hE)
  have hLA'bound : L ≤ A' * E ^ A' := hLA'.trans
    (le_mul_of_one_le_right (zero_le_one.trans hA')
      (Real.one_le_rpow hE (zero_le_one.trans hA')))
  have hMcommon : M ≤ D₀ * E ^ D₀ := hMbound.trans
    (n04NegativeInverse_envelope_mono (zero_le_one.trans hD₀) (le_max_left _ _) hE)
  have hPcommon (n : ℕ) (hn : n ≤ N) :
      n04NegativeInverse_partitionMajorant C M L n ≤ D₀ * E ^ D₀ :=
    (hpartition E hE C M L hC0 (zero_le_one.trans hM) (zero_le_one.trans hL)
      hCA' hMA'bound hLA'bound n hn).trans
      (n04NegativeInverse_envelope_mono (zero_le_one.trans hD₀) (le_max_right _ _) hE)
  have hfinal : (D₀ * E ^ D₀) * C ^ N ≤ D * E ^ D := by
    have he : (D₀ * E ^ D₀) * C ^ N =
        (D₀ * B ^ N) * E ^ (D₀ + B * (N : ℝ)) := by
      dsimp only [C]
      rw [Real.rpow_add (zero_lt_one.trans_le hE), Real.rpow_mul_natCast hE0,
        mul_pow]
      ring
    rw [he]
    exact (hpack E hE).trans
      (n04NegativeInverse_envelope_mono (zero_le_one.trans hD) (le_max_right _ _) hE)
  change M * C ^ N ≤ D * E ^ D ∧
    ∀ n : ℕ, n ≤ N →
      n04NegativeInverse_partitionMajorant C M L n * C ^ N ≤ D * E ^ D
  refine ⟨(mul_le_mul_of_nonneg_right hMcommon (pow_nonneg hC0 _)).trans hfinal, ?_⟩
  intro n hn
  exact (mul_le_mul_of_nonneg_right (hPcommon n hn) (pow_nonneg hC0 _)).trans hfinal

end ContinuousFlexibility.Analysis
