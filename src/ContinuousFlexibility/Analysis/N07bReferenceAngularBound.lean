module

public import ContinuousFlexibility.Analysis.N07bNormalizedReferenceSeeds

/-!
# Actual outer angular coefficients of the reference expression

The current inverse angular vector acts on each of the twenty-one genuine
reference material seeds. The same normalizer is used before and after
these derivatives. Primitive geometric jets through order `b + 2` imply
a bound for every resulting path of length at most `b`.

Only geometric fields occur in the hypotheses. The source-independent
constant depends on `b`, and the common primitive radius has exponent
`4 * (b + 1)`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual coefficient obtained by applying the current angular
direction chain to a genuine reference seed. -/
def n07bReferenceAngularCoefficient {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (Xr Xθ : PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (A : Fin 3 → PolarPoint → ℝ)
    (j : ℕ) (i : n07bReferenceMaterialSeed × n07bAngularChainIndex j) : PolarPoint → ℝ :=
  n07bDirectionChainCoefficient T β (fun _ => n07bInverseAngleVector (K.chart z m))
    (n07bReferenceSeedCoefficient T β Xr Xθ c A i.1) j i.2

def n07bMaterialNormalizedReferenceAngularCoefficient {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (Xr Xθ : PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (A : Fin 3 → PolarPoint → ℝ)
    (j : ℕ) (i : n07bReferenceMaterialSeed × n07bAngularChainIndex j) : PolarPoint → ℝ :=
  n07bMaterialNormalizedDirectionChainCoefficient T K z m β
    (fun _ => n07bInverseAngleVector (K.chart z m))
    (n07bReferenceSeedCoefficient T β Xr Xθ c A i.1) j i.2

theorem N07bMaterialDirectionJetBound.mono
    {S : PhysicalSpacesData} {T : MaterialData} {K : CanonicalData S}
    {z : AnnularState S × ℝ} {m B : ℕ} {Y : PolarPoint → PolarPoint}
    {R R' : ℝ} {y : PolarPoint}
    (h : N07bMaterialDirectionJetBound T K z m Y B R y) (hRR : R ≤ R') :
    N07bMaterialDirectionJetBound T K z m Y B R' y := by
  intro n hn
  exact ⟨(h n hn).1.trans hRR, (h n hn).2.1.trans hRR, (h n hn).2.2.trans hRR⟩

/-- Primitive fields needed for the reference words and the current
outer direction. No final seed or chain coefficient bound is included. -/
def N07bReferencePrimitiveJetBound {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (Xr Xθ : PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (A : Fin 3 → PolarPoint → ℝ)
    (B : ℕ) (R : ℝ) (y : PolarPoint) : Prop :=
  (∀ n : ℕ, n ≤ B →
    ‖iteratedFDeriv ℝ n (fun v => n07bSourceNormalizer T K z m β
      (n07bMaterialRadiusChart T v) * c (n07bMaterialRadiusChart T v)) y‖ ≤ R) ∧
  N07bMaterialDirectionJetBound T K z m Xr B R y ∧
  N07bMaterialDirectionJetBound T K z m Xθ B R y ∧
  N07bMaterialDirectionJetBound T K z m (n07bInverseAngleVector (K.chart z m)) B R y ∧
  ∀ k : Fin 3, ∀ n : ℕ, n ≤ B →
    ‖iteratedFDeriv ℝ n (fun v => A k (n07bMaterialRadiusChart T v)) y‖ ≤ R

theorem N07bReferencePrimitiveJetBound.mono
    {S : PhysicalSpacesData} {T : MaterialData} {K : CanonicalData S}
    {z : AnnularState S × ℝ} {m B : ℕ} {β : ℝ}
    {Xr Xθ : PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    {A : Fin 3 → PolarPoint → ℝ} {R R' : ℝ} {y : PolarPoint}
    (h : N07bReferencePrimitiveJetBound T K z m β Xr Xθ c A B R y)
    (hRR : R ≤ R') :
    N07bReferencePrimitiveJetBound T K z m β Xr Xθ c A B R' y :=
  ⟨fun n hn => (h.1 n hn).trans hRR, h.2.1.mono hRR,
    h.2.2.1.mono hRR, h.2.2.2.1.mono hRR,
    fun k n hn => (h.2.2.2.2 k n hn).trans hRR⟩

def n07bReferenceAngularPower (b : ℕ) : ℕ := 4 * (b + 1)

def n07bReferenceAngularBoundConstant (b : ℕ) : ℝ :=
  n07bSourceChainJetConstant b ^ b * n07bReferenceSeedJetConstant (b + 2) ^ (b + 1)

theorem n07bReferenceAngularPower_pos (b : ℕ) : 0 < n07bReferenceAngularPower b := by
  unfold n07bReferenceAngularPower
  omega

private theorem common_radius_bounds {C R : ℝ} (hC : 1 ≤ C) (hR : 1 ≤ R) :
    1 ≤ C * R ^ 4 ∧ R ≤ C * R ^ 4 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hR4 : R ≤ R ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR (by decide : 1 ≤ 4)
  have hmul : R ^ 4 ≤ C * R ^ 4 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (pow_nonneg hR0 4)
  exact ⟨hR.trans (hR4.trans hmul), hR4.trans hmul⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- Every current outer path satisfies a bound from genuine primitive
geometric jets. The seed bound is proved inside this theorem. -/
theorem n07b_referenceAngularCoefficient_material_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {Xr Xθ : PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    {A : Fin 3 → PolarPoint → ℝ}
    (hXr : ContDiffOn ℝ ∞ Xr (physicalPieceOpen S K z m))
    (hXθ : ContDiffOn ℝ ∞ Xθ (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (physicalPieceOpen S K z m))
    {y : PolarPoint} (hy : y ∈ n07bSourceMaterialPiece T K z m)
    (b : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hprim : N07bReferencePrimitiveJetBound T K z m β Xr Xθ c A (b + 2) R y)
    {j : ℕ} (hj : j ≤ b) (i : n07bReferenceMaterialSeed × n07bAngularChainIndex j) :
    |n07bMaterialNormalizedReferenceAngularCoefficient T K z m β Xr Xθ c A j i y| ≤
      n07bReferenceAngularBoundConstant b * R ^ n07bReferenceAngularPower b := by
  have hU := (hK.domains z hz hs m).1
  have hV : ContDiffOn ℝ ∞ (n07bInverseAngleVector (K.chart z m))
      (physicalPieceOpen S K z m) := by
    intro x hx
    have hclosed := (hK.boundary z hz hs m).2.2.2.2.1 x (subset_closure hx)
    exact (n07b_contDiffAt_inverseAngleVector hclosed.1 hclosed.2.2.1).contDiffWithinAt
  have hseed : ContDiffOn ℝ ∞ (n07bReferenceSeedCoefficient T β Xr Xθ c A i.1)
      (physicalPieceOpen S K z m) := by
    intro x hx
    exact (n07bReferenceSeedCoefficient_contDiffAt hT
      ((hK.domains z hz hs m).2.2.1 hx).1 β
      (hXr.contDiffAt (hU.mem_nhds hx)) (hXθ.contDiffAt (hU.mem_nhds hx))
      (hc.contDiffAt (hU.mem_nhds hx)) (fun k => (hA k).contDiffAt (hU.mem_nhds hx))
      i.1).contDiffWithinAt
  let R₀ : ℝ := n07bReferenceSeedJetConstant (b + 2) * R ^ 4
  have hR₀ : 1 ≤ R₀ ∧ R ≤ R₀ :=
    common_radius_bounds (one_le_n07bReferenceSeedJetConstant (b + 2)) hR
  have hzero : n07bMaterialNormalizedDirectionChainCoefficient T K z m β
      (fun _ => n07bInverseAngleVector (K.chart z m))
      (n07bReferenceSeedCoefficient T β Xr Xθ c A i.1) 0 () =
        n07bMaterialNormalizedReferenceSeedCoefficient T K z m β Xr Xθ c A i.1 := by
    funext v
    change n07bSourceNormalizer T K z m β (n07bMaterialRadiusChart T v) *
      n07bReferenceSeedCoefficient T β Xr Xθ c A i.1 (n07bMaterialRadiusChart T v) = _
    exact (n07bMaterialNormalizedReferenceSeedCoefficient_eq T K z m β Xr Xθ c A i.1 v).symm
  have hinit (n : ℕ) (hn : n ≤ b) :
      ‖iteratedFDeriv ℝ n (n07bMaterialNormalizedDirectionChainCoefficient T K z m β
        (fun _ => n07bInverseAngleVector (K.chart z m))
        (n07bReferenceSeedCoefficient T β Xr Xθ c A i.1) 0 ()) y‖ ≤ R₀ := by
    rw [hzero]
    exact n07b_normalizedReferenceSeed_jets_le hD hT hK hz hs m β hXr hXθ hc hA
      hy (b + 2) hR hprim.1 hprim.2.1 hprim.2.2.1 hprim.2.2.2.2 i.1 n (by omega)
  have h := n07b_normalizedDirectionChain_value_le hD hT hK hz hs m β
    (fun _ => hV) hseed hy b hR₀.1 hinit
    (fun k n hkn => ((hprim.2.2.2.1 n (by omega)).1).trans hR₀.2)
    (fun k n hkn => ((hprim.2.2.2.1 n (by omega)).2.1).trans hR₀.2)
    (fun k n hkn => ((hprim.2.2.2.1 n (by omega)).2.2).trans hR₀.2) hj i.2
  refine h.trans_eq ?_
  dsimp only [R₀, n07bReferenceAngularBoundConstant, n07bReferenceAngularPower]
  rw [mul_pow, ← pow_mul]
  ring

/-- The material representative is exactly the normalized actual physical
coefficient at the prescribed inverse material coordinates. -/
theorem n07bMaterialNormalizedReferenceAngularCoefficient_materialChart
    (hT : IsMaterialData D T) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (Xr Xθ : PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (A : Fin 3 → PolarPoint → ℝ)
    (j : ℕ) (i : n07bReferenceMaterialSeed × n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) :
    n07bMaterialNormalizedReferenceAngularCoefficient T K z m β Xr Xθ c A j i
      (n07bMaterialChart T x) =
        n07bSourceNormalizer T K z m β x * n07bReferenceAngularCoefficient T K z m β Xr Xθ c A j i x := by
  change n07bSourceNormalizer T K z m β
      (n07bMaterialRadiusChart T (n07bMaterialChart T x)) *
    n07bReferenceAngularCoefficient T K z m β Xr Xθ c A j i
      (n07bMaterialRadiusChart T (n07bMaterialChart T x)) = _
  rw [n07bMaterialRadiusChart_materialChart hT hx]

/-- The same finite bound on the actual physical domain. -/
theorem n07b_referenceAngularCoefficient_normalized_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {Xr Xθ : PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    {A : Fin 3 → PolarPoint → ℝ}
    (hXr : ContDiffOn ℝ ∞ Xr (physicalPieceOpen S K z m))
    (hXθ : ContDiffOn ℝ ∞ Xθ (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (physicalPieceOpen S K z m))
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m)
    (b : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hprim : N07bReferencePrimitiveJetBound T K z m β Xr Xθ c A (b + 2) R
      (n07bMaterialChart T x))
    {j : ℕ} (hj : j ≤ b) (i : n07bReferenceMaterialSeed × n07bAngularChainIndex j) :
    |n07bSourceNormalizer T K z m β x * n07bReferenceAngularCoefficient T K z m β Xr Xθ c A j i x| ≤
      n07bReferenceAngularBoundConstant b * R ^ n07bReferenceAngularPower b := by
  have hxcore := ((hK.domains z hz hs m).2.2.1 hx).1
  have hy : n07bMaterialChart T x ∈ n07bSourceMaterialPiece T K z m := by
    change n07bMaterialRadiusChart T (n07bMaterialChart T x) ∈ physicalPieceOpen S K z m
    rw [n07bMaterialRadiusChart_materialChart hT hxcore]
    exact hx
  have h := n07b_referenceAngularCoefficient_material_bound hD hT hK hz hs m β
    hXr hXθ hc hA hy b hR hprim hj i
  rwa [n07bMaterialNormalizedReferenceAngularCoefficient_materialChart hT K z m β
    Xr Xθ c A j i hxcore] at h

/-- The square in the uniform bound is exactly the actual coefficient
density used in material energy, for the same current Jacobian and height. -/
theorem n07b_referenceAngularCoefficient_normalized_sq
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (β : ℝ) (Xr Xθ : PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (A : Fin 3 → PolarPoint → ℝ)
    (j : ℕ) (i : n07bReferenceMaterialSeed × n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    (n07bSourceNormalizer T K z m β x *
      n07bReferenceAngularCoefficient T K z m β Xr Xθ c A j i x) ^ 2 =
        n07bSourceMaterialJacobian T K z m x *
          (n07bSourceHeightRatio T K m x ^ β) ^ 2 *
            n07bReferenceAngularCoefficient T K z m β Xr Xθ c A j i x ^ 2 := by
  rw [mul_pow, n07bSourceNormalizer_sq hT hK hz hs m β hx]

end ContinuousFlexibility.Analysis
