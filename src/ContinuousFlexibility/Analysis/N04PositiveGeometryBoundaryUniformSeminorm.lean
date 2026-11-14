module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaPrefix
public import ContinuousFlexibility.Analysis.N01cGradedJetContinuity
public import ContinuousFlexibility.Analysis.SmoothDirectionsBoundedLimit

/-!
# Uniform angular seminorm bounds from saved endpoint words

One common low-order unit neighborhood suffices for every parameter and
angular order. Taking the normalization radius to be one plus the high
seminorm gives linear growth, and genuine multilinearity restores the
product of direction seminorms, including seminorm kernels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem N04BoundaryWordBounds.restrict
    {U V : Set E} {f : E × ℝ → F} {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hb : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hV : IsOpen V) (hVU : V ⊆ U) (hx : x ∈ V)
    (Q : SmoothDirections (V ×ˢ univ) f) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  let J' := smoothDirectionsRestrict J (hV.prod isOpen_univ)
    (fun y hy => ⟨hVU hy.1, hy.2⟩)
  intro n w hk ha v hv hp
  have he := J'.unique Q n (x, θ) ⟨hx, mem_univ θ⟩
  exact (congrArg norm (congrArg (fun A : (E × ℝ) [×n]→L[ℝ] F => A v) he.symm)).trans_le
    (hb n w hk ha v hv hp)

theorem n04PositiveGeometry_boundaryPrefix_uniformSeminormBounds
    (p : ℕ → Seminorm ℝ E) (hp : ∀ n, Continuous (p n)) (hmono : Monotone p)
    {U V : Set E} {f : E × ℝ → ℝ} (J : SmoothDirections (U ×ˢ univ) f)
    (low : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hprefix : ∀ K : ℕ, ∃ shift : ℕ, ∀ s : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ U, p low x ≤ 1 → ∀ θ R : ℝ, 1 ≤ R →
      p (low + s + shift * K + 1) x ≤ R →
      N04BoundaryWordBounds J K s 1 x θ
        (fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R)
        M H (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift)
    (hV : IsOpen V) (hVU : V ⊆ U) (hunit : ∀ x ∈ V, p low x ≤ 1)
    (Q : SmoothDirections (V ×ˢ univ) f) (b : ℕ) :
    UniformScalarJetSeminormBounds (smoothDirections_angularStateSlice Q b) := by
  intro n
  obtain ⟨shift, hs⟩ := hprefix n
  obtain ⟨M, hM, hb⟩ := hs b
  let high : ℕ := low + b + shift * n + 1
  let q : Seminorm ℝ E := p high
  let B : ℝ := M * parameterHeightWeight H n
  have hB : 0 ≤ B := mul_nonneg hM (parameterHeightWeight_nonneg hH n)
  refine ⟨q, B, hp high, hB, ?_⟩
  intro θ x hx v
  have hqx : 0 ≤ q x := apply_nonneg q x
  apply multilinear_abs_le_product_of_unitBound
    ((smoothDirections_angularStateSlice Q b θ).D n x) q
    (mul_nonneg hB (by positivity)) ?_ v
  intro w hw
  let R : ℝ := 1 + q x
  have hR : 1 ≤ R := le_add_of_nonneg_right hqx
  have hxR : p high x ≤ R := le_add_of_nonneg_left zero_le_one
  have hlo : low ≤ high := by dsimp only [high]; omega
  have hdirs (i : Fin n) : p low (w i) ≤ 1 ∧ p high (w i) ≤ R :=
    ⟨(hmono hlo (w i)).trans (hw i).le, (hw i).le.trans hR⟩
  have hzero : p low (0 : E) ≤ 1 ∧ p high (0 : E) ≤ R := by
    simp only [map_zero]; exact ⟨zero_le_one, zero_le_one.trans hR⟩
  have hword := (hb x (hVU hx) (hunit x hx) θ R hR hxR).restrict hV hVU hx Q
  have hraw := n04PositiveGeometry_boundaryWord_to_angular_reserve Q
    (smoothDirections_angularStateSlice Q) hx θ _ hzero hword n b le_rfl
    (Nat.le_add_right _ _) w hdirs
  have hexponent : (((b - 1) + shift * n : ℕ) : ℝ) ≤
      ((b + shift * n : ℕ) : ℝ) + 1 := by
    have hnat : (b - 1) + shift * n ≤ b + shift * n :=
      Nat.add_le_add_right (Nat.sub_le _ _) _
    have hcast : (((b - 1) + shift * n : ℕ) : ℝ) ≤ ((b + shift * n : ℕ) : ℝ) :=
      Nat.cast_le.mpr hnat
    linarith
  have hpower : (R ^ (1 / (((b + shift * n : ℕ) : ℝ) + 1))) ^
      ((b - 1) + shift * n) ≤ R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    calc
      _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR (by
        rw [one_div, inv_mul_eq_div]
        exact (div_le_one (by positivity)).mpr hexponent)
      _ = R := Real.rpow_one _
  have hnorm : |(smoothDirections_angularStateSlice Q b θ).D n x w| ≤
      B * (R ^ (1 / (((b + shift * n : ℕ) : ℝ) + 1))) ^ ((b - 1) + shift * n) := by
    simpa only [Real.norm_eq_abs] using hraw
  exact hnorm.trans (mul_le_mul_of_nonneg_left hpower hB)

end ContinuousFlexibility.Analysis
