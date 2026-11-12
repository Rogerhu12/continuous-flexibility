import ContinuousFlexibility.Analysis.N07bFiniteMaterialExpansion
import ContinuousFlexibility.Analysis.N07bNormalizedDirectionChainJets

/-!
# Finite jets of the actual normalized reference seeds

The three reference words have lengths one, two, and two. Their actual
normalized coefficients are multiplied by the three actual reference
multipliers, giving the twenty-one seeds of the finite material formula.
Bounds on the initial normalized coefficient, the two geometric directions,
and the three multipliers therefore control every seed. No physical scalar,
forcing, inverse, or bound on a final seed is a hypothesis.

The order budget is `n + 2 <= B`. The common bound is
`2^B * (3 * 2^B)^2 * R^4`, so `B = b + 2` controls all seed jets through
order `b`. The physical domains below are the actual current domains.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The material normalized seed, expressed as its actual multiplier
times the already normalized direction word. -/
def n07bMaterialNormalizedReferenceSeedCoefficient {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (Xr Xθ : PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (A : Fin 3 → PolarPoint → ℝ) :
    n07bReferenceMaterialSeed → PolarPoint → ℝ
  | .inl i => fun y => A 0 (n07bMaterialRadiusChart T y) *
      n07bMaterialNormalizedDirectionChainCoefficient T K z m β (fun _ => Xr) c 1 i y
  | .inr (.inl i) => fun y => A 1 (n07bMaterialRadiusChart T y) *
      n07bMaterialNormalizedDirectionChainCoefficient T K z m β (fun _ => Xr) c 2 i y
  | .inr (.inr i) => fun y => A 2 (n07bMaterialRadiusChart T y) *
      n07bMaterialNormalizedDirectionChainCoefficient T K z m β (fun _ => Xθ) c 2 i y

/-- These are exactly the normalized coefficients of the genuine finite
reference expansion, with the same density and sampled height as the source. -/
theorem n07bMaterialNormalizedReferenceSeedCoefficient_eq
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (Xr Xθ : PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (A : Fin 3 → PolarPoint → ℝ) (i : n07bReferenceMaterialSeed) (y : PolarPoint) :
    n07bMaterialNormalizedReferenceSeedCoefficient T K z m β Xr Xθ c A i y =
      n07bSourceNormalizer T K z m β (n07bMaterialRadiusChart T y) *
        n07bReferenceSeedCoefficient T β Xr Xθ c A i (n07bMaterialRadiusChart T y) := by
  rcases i with i | (i | i) <;>
    simp only [n07bMaterialNormalizedReferenceSeedCoefficient,
      n07bMaterialNormalizedDirectionChainCoefficient, Function.comp_apply,
      n07bNormalizedDirectionChainCoefficient, n07bReferenceSeedCoefficient] <;> ring

/-- Finite jets of the three actual material fields associated with a
geometric direction. This contains no recursively generated coefficient. -/
def N07bMaterialDirectionJetBound {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (Y : PolarPoint → PolarPoint) (B : ℕ) (R : ℝ) (y : PolarPoint) : Prop :=
  ∀ n : ℕ, n ≤ B →
    ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV1 T Y) y‖ ≤ R ∧
    ‖iteratedFDeriv ℝ n (n07bMaterialDirectionV2 T Y) y‖ ≤ R ∧
    ‖iteratedFDeriv ℝ n (n07bMaterialDirectionDrift T K z m Y) y‖ ≤ R

/-- The finite constant precedes the state, piece, point, and geometry. -/
def n07bReferenceSeedJetConstant (B : ℕ) : ℝ :=
  n07bFiniteJetProductConstant B * n07bSourceChainJetConstant B ^ 2

theorem one_le_n07bReferenceSeedJetConstant (B : ℕ) :
    1 ≤ n07bReferenceSeedJetConstant B := by
  have hP := one_le_n07bFiniteJetProductConstant B
  have hK := one_le_n07bSourceChainJetConstant B
  have hK2 : (1 : ℝ) ≤ n07bSourceChainJetConstant B ^ 2 := one_le_pow₀ hK
  change (1 : ℝ) ≤ n07bFiniteJetProductConstant B * n07bSourceChainJetConstant B ^ 2
  simpa only [one_mul] using mul_le_mul hP hK2 zero_le_one (zero_le_one.trans hP)

theorem n07bReferenceSeedJetConstant_eq (B : ℕ) :
    n07bReferenceSeedJetConstant B = (2 : ℝ) ^ B * (3 * (2 : ℝ) ^ B) ^ 2 := rfl

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

private theorem contDiffOn_materialCoefficient
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {a : PolarPoint → ℝ} (ha : ContDiffOn ℝ ∞ a (physicalPieceOpen S K z m)) :
    ContDiffOn ℝ ∞ (fun y => a (n07bMaterialRadiusChart T y))
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
  exact ((ha.contDiffAt ((hK.domains z hz hs m).1.mem_nhds hx)).comp y
    (n07bMaterialRadiusChart_contDiff hT).contDiffAt).contDiffWithinAt

/-- Actual smoothness of the twenty-one normalized seeds. -/
theorem n07bMaterialNormalizedReferenceSeedCoefficient_contDiffOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {Xr Xθ : PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    {A : Fin 3 → PolarPoint → ℝ}
    (hXr : ContDiffOn ℝ ∞ Xr (physicalPieceOpen S K z m))
    (hXθ : ContDiffOn ℝ ∞ Xθ (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (physicalPieceOpen S K z m))
    (i : n07bReferenceMaterialSeed) :
    ContDiffOn ℝ ∞ (n07bMaterialNormalizedReferenceSeedCoefficient T K z m β Xr Xθ c A i)
      (n07bSourceMaterialPiece T K z m) := by
  rcases i with i | (i | i)
  · exact (contDiffOn_materialCoefficient hT hK hz hs m (hA 0)).mul
      (n07bMaterialNormalizedDirectionChainCoefficient_contDiffOn
        hD hT hK hz hs m β (fun _ => hXr) hc 1 i)
  · exact (contDiffOn_materialCoefficient hT hK hz hs m (hA 1)).mul
      (n07bMaterialNormalizedDirectionChainCoefficient_contDiffOn
        hD hT hK hz hs m β (fun _ => hXr) hc 2 i)
  · exact (contDiffOn_materialCoefficient hT hK hz hs m (hA 2)).mul
      (n07bMaterialNormalizedDirectionChainCoefficient_contDiffOn
        hD hT hK hz hs m β (fun _ => hXθ) hc 2 i)

/-- Primitive geometric jets imply the normalized finite-jet bound for
every actual reference seed. Two derivatives are reserved for its word. -/
theorem n07b_normalizedReferenceSeed_jets_le
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
    (B : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hinit : ∀ n : ℕ, n ≤ B →
      ‖iteratedFDeriv ℝ n (fun v => n07bSourceNormalizer T K z m β
        (n07bMaterialRadiusChart T v) * c (n07bMaterialRadiusChart T v)) y‖ ≤ R)
    (hXrjets : N07bMaterialDirectionJetBound T K z m Xr B R y)
    (hXθjets : N07bMaterialDirectionJetBound T K z m Xθ B R y)
    (hAjets : ∀ k : Fin 3, ∀ n : ℕ, n ≤ B →
      ‖iteratedFDeriv ℝ n (fun v => A k (n07bMaterialRadiusChart T v)) y‖ ≤ R)
    (i : n07bReferenceMaterialSeed) (n : ℕ) (hn : n + 2 ≤ B) :
    ‖iteratedFDeriv ℝ n
      (n07bMaterialNormalizedReferenceSeedCoefficient T K z m β Xr Xθ c A i) y‖ ≤
        n07bReferenceSeedJetConstant B * R ^ 4 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hK1 := one_le_n07bSourceChainJetConstant B
  let D₀ : ℝ := n07bSourceChainJetConstant B ^ 2 * R ^ 3
  have hD₀ : 0 ≤ D₀ := mul_nonneg (sq_nonneg _) (pow_nonneg hR0 _)
  have hzero (Y : PolarPoint → PolarPoint) (t : ℕ) (ht : t ≤ B) :
      ‖iteratedFDeriv ℝ t
        (n07bMaterialNormalizedDirectionChainCoefficient T K z m β (fun _ => Y) c 0 ()) y‖ ≤ R := by
    change ‖iteratedFDeriv ℝ t (fun v => n07bSourceNormalizer T K z m β
      (n07bMaterialRadiusChart T v) * c (n07bMaterialRadiusChart T v)) y‖ ≤ R
    exact hinit t ht
  have hword (Y : PolarPoint → PolarPoint)
      (hY : ContDiffOn ℝ ∞ Y (physicalPieceOpen S K z m))
      (hYjets : N07bMaterialDirectionJetBound T K z m Y B R y)
      (j : ℕ) (k : n07bAngularChainIndex j) (hj : j ≤ 2)
      (t : ℕ) (ht : t + 2 ≤ B) :
      ‖iteratedFDeriv ℝ t
        (n07bMaterialNormalizedDirectionChainCoefficient T K z m β (fun _ => Y) c j k) y‖ ≤ D₀ := by
    have h := n07b_normalizedDirectionChain_jets_le hD hT hK hz hs m β
      (fun _ => hY) hc hy B hR0 (hzero Y)
      (fun l s hls => (hYjets s (by omega)).1)
      (fun l s hls => (hYjets s (by omega)).2.1)
      (fun l s hls => (hYjets s (by omega)).2.2) j k t (by omega)
    exact h.trans (mul_le_mul
      (pow_le_pow_right₀ hK1 hj) (pow_le_pow_right₀ hR (by omega : j + 1 ≤ 3))
      (pow_nonneg hR0 _) (pow_nonneg (zero_le_one.trans hK1) _))
  have hproduct (Y : PolarPoint → PolarPoint)
      (hY : ContDiffOn ℝ ∞ Y (physicalPieceOpen S K z m))
      (hYjets : N07bMaterialDirectionJetBound T K z m Y B R y)
      (a : Fin 3) (j : ℕ) (k : n07bAngularChainIndex j) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ n (fun v => A a (n07bMaterialRadiusChart T v) *
        n07bMaterialNormalizedDirectionChainCoefficient T K z m β (fun _ => Y) c j k v) y‖ ≤
        n07bReferenceSeedJetConstant B * R ^ 4 := by
    have hmul := n07b_norm_jet_mul_le (n07bSourceMaterialPiece_isOpen hT hK hz hs m)
      (contDiffOn_materialCoefficient hT hK hz hs m (hA a))
      (n07bMaterialNormalizedDirectionChainCoefficient_contDiffOn
        hD hT hK hz hs m β (fun _ => hY) hc j k) hy hR0 hD₀
      (fun t ht => hAjets a t (by omega))
      (fun t ht => hword Y hY hYjets j k hj t (by omega)) (by omega : n ≤ B)
    calc
      _ ≤ n07bFiniteJetProductConstant B * R * D₀ := hmul
      _ = _ := by dsimp only [D₀, n07bReferenceSeedJetConstant]; ring
  rcases i with i | (i | i)
  · exact hproduct Xr hXr hXrjets 0 1 i (by decide)
  · exact hproduct Xr hXr hXrjets 1 2 i le_rfl
  · exact hproduct Xθ hXθ hXθjets 2 2 i le_rfl

end ContinuousFlexibility.Analysis
