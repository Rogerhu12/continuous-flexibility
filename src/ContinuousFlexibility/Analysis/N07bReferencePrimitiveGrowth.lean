import ContinuousFlexibility.Analysis.N07bReferenceAngularBound
import ContinuousFlexibility.Analysis.N07bSourceBoundNeighborhood
import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# Uniform reference coefficient density from primitive geometric growth

One material subpower estimate absorbs the whole finite outer chain. Its
exponent is the reciprocal of `4 * (b + 1)`. One common smaller state
neighborhood bounds the fixed state polynomial. All constants and the
neighborhood are chosen before the state, piece, point, or coefficient.

The inputs concern only actual geometric fields and their finite jets.
This does not assert that qualitative canonical geometry already supplies
these quantitative bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Regularity of the actual geometric fields in the reference formula. -/
def N07bReferenceGeometricRegularity (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (Xr Xθ : (AnnularState S × ℝ) → ℕ → PolarPoint → PolarPoint)
    (c : (AnnularState S × ℝ) → ℕ → PolarPoint → ℝ)
    (α : (AnnularState S × ℝ) → ℕ → Fin 3 → PolarPoint → ℝ)
    (base : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
    ContDiffOn ℝ ∞ (Xr z m) (physicalPieceOpen S K z m) ∧
    ContDiffOn ℝ ∞ (Xθ z m) (physicalPieceOpen S K z m) ∧
    ContDiffOn ℝ ∞ (c z m) (physicalPieceOpen S K z m) ∧
    ∀ k, ContDiffOn ℝ ∞ (α z m k) (physicalPieceOpen S K z m)

/-- A single source-free growth estimate on primitive geometric jets.
Its exponent may be any real number; `E0 >= 1` is not assumed. -/
def N07bReferencePrimitiveE0Growth (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (β : ℝ)
    (Xr Xθ : (AnnularState S × ℝ) → ℕ → PolarPoint → PolarPoint)
    (c : (AnnularState S × ℝ) → ℕ → PolarPoint → ℝ)
    (α : (AnnularState S × ℝ) → ℕ → Fin 3 → PolarPoint → ℝ)
    (base : ℕ) (ε : ℝ) (b : ℕ) : Prop :=
  ∃ r d : ℕ, ∃ C₀ σ : ℝ, 0 ≤ C₀ ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m y, y ∈ n07bSourceMaterialPiece T K z m →
        N07bReferencePrimitiveJetBound T K z m β (Xr z m) (Xθ z m) (c z m) (α z m)
          (b + 2)
          (C₀ * T.E0 (T.radius y.1) ^ σ *
            (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d) y

private theorem primitive_radius_le
    {C₀ C E P Q Qmax : ℝ} (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hE : E ≤ C * P) (hQQ : Q ≤ Qmax) :
    C₀ * E * Q ≤ max 1 (C₀ * C * Qmax) * P := by
  calc
    _ ≤ C₀ * (C * P) * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hC₀) hQ
    _ ≤ C₀ * (C * P) * Qmax :=
      mul_le_mul_of_nonneg_left hQQ (mul_nonneg hC₀ (mul_nonneg hC hP))
    _ = (C₀ * C * Qmax) * P := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hP

private theorem reference_radius_power (b : ℕ) (C M : ℝ) (hM : 0 ≤ M) :
    (C * M ^ (1 / (n07bReferenceAngularPower b : ℝ))) ^ n07bReferenceAngularPower b =
      C ^ n07bReferenceAngularPower b * M := by
  have hden : (n07bReferenceAngularPower b : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (n07bReferenceAngularPower_pos b)).ne'
  have hroot : (M ^ (1 / (n07bReferenceAngularPower b : ℝ))) ^ n07bReferenceAngularPower b = M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM,
      div_mul_cancel₀ (1 : ℝ) hden, Real.rpow_one]
  rw [mul_pow, hroot]

private theorem square_mul_assoc (a c M : ℝ) :
    (a * (c * M)) ^ 2 = (a * c) ^ 2 * M ^ 2 := by ring

/-- Pure primitive geometric growth gives the uniform actual coefficient
density bound. The material subpower theorem is applied exactly once. -/
theorem n07b_exists_referenceAngular_M_bound_of_primitive_E0
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base b : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε) (β : ℝ)
    {Xr Xθ : (AnnularState S × ℝ) → ℕ → PolarPoint → PolarPoint}
    {c : (AnnularState S × ℝ) → ℕ → PolarPoint → ℝ}
    {α : (AnnularState S × ℝ) → ℕ → Fin 3 → PolarPoint → ℝ}
    (hreg : N07bReferenceGeometricRegularity S C K Xr Xθ c α base ε)
    (hgeom : N07bReferencePrimitiveE0Growth T S C K β Xr Xθ c α base ε b) :
    ∃ base' : ℕ, ∃ ε' A₀ : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧ 0 ≤ A₀ ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K z m →
          ∀ j : ℕ, j ≤ b → ∀ i : n07bReferenceMaterialSeed × n07bAngularChainIndex j,
            (n07bSourceNormalizer T K z m β x *
              n07bReferenceAngularCoefficient T K z m β (Xr z m) (Xθ z m)
                (c z m) (α z m) j i x) ^ 2 ≤ A₀ * T.M x.1 ^ 2 := by
  obtain ⟨r, d, C₀, σ, hC₀, hjets⟩ := hgeom
  let e : ℝ := 1 / (n07bReferenceAngularPower b : ℝ)
  have he : 0 < e := one_div_pos.mpr (Nat.cast_pos.mpr (n07bReferenceAngularPower_pos b))
  obtain ⟨CE, hCE, hE⟩ := materialE0_rpow_le_subpowerM hT σ he
  let C₁ : ℝ := max 1 (C₀ * CE * (2 : ℝ) ^ d)
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  refine ⟨max base r, min ε (1 / 2),
    (n07bReferenceAngularBoundConstant b * C₁ ^ n07bReferenceAngularPower b) ^ 2,
    le_max_left _ _, lt_min hε (by norm_num), min_le_left _ _, min_le_right _ _,
    sq_nonneg _, ?_⟩
  intro z hz hs m x hx j hj i
  have hzold := n06_stateNeighborhood_mono (C := C)
    (le_max_left base r) (min_le_left ε (1 / 2)) hz
  have hxcore := ((hK.domains z hzold hs m).2.2.1 hx).1
  have hM : 1 ≤ T.M x.1 := (hT.2.1 x.1 hxcore).2.2.2
  have hM0 : 0 ≤ T.M x.1 := zero_le_one.trans hM
  have hy : n07bMaterialChart T x ∈ n07bSourceMaterialPiece T K z m := by
    change n07bMaterialRadiusChart T (n07bMaterialChart T x) ∈ physicalPieceOpen S K z m
    rw [n07bMaterialRadiusChart_materialChart hT hxcore]
    exact hx
  have hradius : T.radius (n07bMaterialChart T x).1 = x.1 := by
    change T.radius (T.rho x.1) = x.1
    exact hT.2.2.2.2.2.2.2.2.1 x.1 hxcore
  have hraw := hjets z hzold hs m (n07bMaterialChart T x) hy
  rw [hradius] at hraw
  have hQ : 0 ≤ 1 + stateGrading S r (z.1 - C.referenceState) + |z.2| :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  have hQpow := n07b_stateWeight_pow_le_two_pow (d := d)
    (le_max_right base r) (min_le_right ε (1 / 2)) hz
  have hrad : C₀ * T.E0 x.1 ^ σ *
      (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d ≤ C₁ * T.M x.1 ^ e :=
    primitive_radius_le hC₀ hCE.le (Real.rpow_nonneg hM0 e)
      (pow_nonneg hQ d) (hE x.1 hxcore) hQpow
  have hMroot : 1 ≤ T.M x.1 ^ e := Real.one_le_rpow hM he.le
  have hR : 1 ≤ C₁ * T.M x.1 ^ e := by
    simpa only [one_mul] using mul_le_mul hC₁ hMroot zero_le_one (zero_le_one.trans hC₁)
  obtain ⟨hXr, hXθ, hc, hα⟩ := hreg z hzold hs m
  have hval := n07b_referenceAngularCoefficient_normalized_bound hD hT hK hzold hs m β
    hXr hXθ hc hα hx b hR (hraw.mono hrad) hj i
  dsimp only [e] at hval
  rw [reference_radius_power b C₁ (T.M x.1) hM0] at hval
  have hsquare := pow_le_pow_left₀ (abs_nonneg _) hval 2
  rw [sq_abs] at hsquare
  exact hsquare.trans_eq (square_mul_assoc (n07bReferenceAngularBoundConstant b)
    (C₁ ^ n07bReferenceAngularPower b) (T.M x.1))

end ContinuousFlexibility.Analysis
