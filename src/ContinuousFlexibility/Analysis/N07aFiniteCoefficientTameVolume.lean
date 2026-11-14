module

public import ContinuousFlexibility.Analysis.N07aFiniteCoefficientVolume
public import ContinuousFlexibility.Analysis.N07aSampleJetBounds

/-!
# One-high weighted norms on a fixed finite set of pieces

The estimate uses the actual coefficient representatives and actual
weighted volume graph. Compact support makes the material constants
finite; monotonicity of the parameter grading keeps one fixed loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aFiniteTameVolumeLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aFiniteTameVolumeLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem exists_n07aFiniteCoefficientVolume_tame
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {U : Set E} {d : ℕ}
    {f : E → ℕ → PolarPoint → ℝ}
    (hf : N07aSampleJetBounds T K p U (canonicalOpen S K) d f)
    (χ : ∀ z, z ∈ U → ∀ m, N07aCanonicalOpenCoefficient S K m)
    (hχ : ∀ z hz m, (χ z hz m).value = f z m)
    (heven : ∀ z ∈ U, ∀ m y, y ∈ canonicalOpen S K m →
      f z m (y.1, -y.2) = f z m y)
    (I : Finset ℕ)
    (hzero : ∀ z ∈ U, ∀ m, m ∉ I → EqOn (f z m) (fun _ => (0 : ℝ)) (canonicalOpen S K m))
    (γ t : ℝ) (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z (hz : z ∈ U),
      ∃ W : V.level γ t s, V.forget γ t s W = (fun m => (χ z hz m).toLp) ∧
        ‖W‖ ≤ A * (1 + p (s + d) z) := by
  classical
  let e : Fin (s + 1) → ℕ → ℝ := fun j => (hf 0 j.val).choose
  have he0 (j : Fin (s + 1)) (m : ℕ) : 0 ≤ e j m :=
    (hf 0 j.val).choose_spec.2.1 m
  let c : ℕ → Fin (s + 1) → ℝ :=
    fun m j => Real.sqrt (Real.pi * (K.right m - K.left m)) * e j m
  let A : ℝ := ∑ m ∈ I, (n07aVolumeWeight T K γ t m)⁻¹ * ∑ j, c m j
  have hc0 (m : ℕ) (j : Fin (s + 1)) : 0 ≤ c m j :=
    mul_nonneg (Real.sqrt_nonneg _) (he0 j m)
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun m hm =>
    mul_nonneg (inv_nonneg.mpr (n07aVolumeWeight_pos hD hT γ t m).le)
      (Finset.sum_nonneg fun j _ => hc0 m j)
  refine ⟨A + 1, by linarith, fun z hz => ?_⟩
  let g := 1 + p (s + d) z
  have hg : 0 ≤ g := add_nonneg zero_le_one (apply_nonneg _ _)
  have hjet (m : ℕ) (j : Fin (s + 1)) : ‖((χ z hz m).jet 0 j.val).toLp‖ ≤ c m j * g := by
    have hpoint : ∀ᵐ y ∂canonicalMeasure S K m,
        |((χ z hz m).jet 0 j.val).value y| ≤ e j m * g := by
      filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with y hy
      change |mixedDerivative 0 j.val (χ z hz m).value y| ≤ _
      rw [hχ z hz m]
      have hb := (hf 0 j.val).choose_spec.2.2 z hz m y hy
      have hmono : p (0 + j.val + d) z ≤ p (s + d) z :=
        hp (by omega) z
      exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmono) (he0 j m))
    have hn := ((χ z hz m).jet 0 j.val).toLp_norm_le (hI m)
      (mul_nonneg (he0 j m) hg) hpoint
    exact hn.trans_eq (by dsimp only [c]; ring)
  have hsym (m : ℕ) (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) :
      (χ z hz m).value (y.1, -y.2) = (χ z hz m).value y := by
    rw [hχ z hz m]
    exact heven z hz m y hy
  have hsupport (m : ℕ) (hm : m ∉ I) :
      EqOn (χ z hz m).value (fun _ => (0 : ℝ)) (canonicalOpen S K m) := by
    rw [hχ z hz m]
    exact hzero z hz m hm
  obtain ⟨W, hW, hnorm⟩ := exists_n07aFiniteCoefficientVolume hD hT hV γ t s
    (χ z hz) hsym I hsupport
  refine ⟨W, hW, hnorm.trans ?_⟩
  calc
    _ ≤ ∑ m ∈ I, (n07aVolumeWeight T K γ t m)⁻¹ * ∑ j, c m j * g := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hjet m j)
        (inv_nonneg.mpr (n07aVolumeWeight_pos hD hT γ t m).le)
    _ = A * g := by
      simp only [A, Finset.sum_mul, mul_assoc]
    _ ≤ (A + 1) * g := mul_le_mul_of_nonneg_right (by linarith) hg

end ContinuousFlexibility.Analysis
