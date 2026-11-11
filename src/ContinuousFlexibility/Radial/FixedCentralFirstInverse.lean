import ContinuousFlexibility.Radial.FixedCentralModelColumnCost
import ContinuousFlexibility.Radial.FirstCentralGapInverse

/-!
# A fixed central model gives the actual three-piece inverse

Both positive gaps are constructed on the original reference.  Their
lengths and the two radial dilations do not enter the norm constant.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

def fixedCentralFirstInverseCost {B : FixedCentralBorder} {q : ℕ}
    {T₀ B₁ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T₀ B₁) C K)
    (j T B₀ : ℝ) : ℝ :=
  max (fixedCentralModelDirichletCost T B₀ C) 4 +
    (max (2 * fixedCentralModelColumnCost M j) 4) ^ 2 / 2

theorem fixedCentralFirstInverseCost_nonneg {B : FixedCentralBorder} {q : ℕ}
    {T₀ B₁ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T₀ B₁) C K)
    (j T B₀ : ℝ) : 0 ≤ fixedCentralFirstInverseCost M j T B₀ := by
  unfold fixedCentralFirstInverseCost
  exact add_nonneg ((by norm_num : (0 : ℝ) ≤ 4).trans (le_max_right _ _))
    (div_nonneg (sq_nonneg _) (by norm_num))

theorem exists_fixedCentralThreePieceInverse
    (B : FixedCentralBorder) (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (G : InnerRadialChainGeometry D 2) (q : ℕ) (hq : 1 ≤ q)
    {T B₀ C K : ℝ} (hC : 0 < C) (hT : 8 ≤ T)
    (hcap : sqrt centralOscillatorA + 2 ≤ T)
    (hcolumn : referenceColumn D = fixedCentralColumn B.chi)
    (hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore D)
    (hw : ∀ x ∈ Icc (-T) T,
      D.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x)
    (hleft : G.left 1 = centralRadius (-T))
    (hright : G.right 1 = centralRadius T)
    (hslope : ∀ p : Fin 3, p ≠ 1 → ∀ r ∈ Icc (G.left p) (G.right p),
      (3 : ℝ) / 4 ≤ r * deriv D.w r / D.w r)
    (hB : BufferHypotheses (B.modelBuffer q T B₀))
    (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (hk : ∀ i, 0 < fixedCentralModelCutEnergy M i)
    (herror : ∀ sign : Bool,
      ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M) (fun _ => 1)
        (M.physicalFluxError 1
          (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
        (1 : ℝ) / 8) :
    ∃ hwD : ContDiff ℝ ∞ D.w,
    ∃ inverse : InnerRadialPhysicalSource D G (centralModelBordered q) →L[ℝ]
        InnerRadialPhysicalSource D G (centralModelBordered q),
      (∀ u F, InnerRadialPhysicalWeakGraph D hwD.continuous G
        (centralModelBordered q) (2 * (q : ℝ)) 1 (matchingBorderVector D hD hborder)
        u F ↔ inverse F = u) ∧
      ‖inverse‖ ≤ fixedCentralFirstInverseCost M (2 * (q : ℝ)) T B₀ ∧
      IsSelfAdjoint inverse := by
  have hg : RadialProfileGeometry D := (Classical.choose_spec hD).1
  have hj : (2 : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * q)
  have hjpos : 0 < 2 * (q : ℝ) := lt_of_lt_of_le (by norm_num) hj
  let A := fixedCentralPhysicalModelChart B D hD hborder G 1 q hT hcap hcolumn hcore hw
    hleft hright hB M
  have hkfun : A.kappa = fixedCentralModelPhysicalKappa M :=
    funext (fixedCentralPhysicalModelChart_kappa B D hD hborder G 1 q hT hcap
      hcolumn hcore hw hleft hright hB M)
  have hκ : ∀ i, 0 < A.kappa i := by
    rw [hkfun]
    exact fixedCentralModelPhysicalKappa_pos M hk
  have hE : ∀ sign : Bool,
      ‖innerTwoCutWeightedError A.kappa (fun _ => 1) A.errorMatrix sign‖ ≤
        (1 : ℝ) / 8 := by
    rw [hkfun]
    exact herror
  have hd : 0 ≤ fixedCentralModelDirichletCost T B₀ C := by
    unfold fixedCentralModelDirichletCost
    positivity
  obtain ⟨inverse, hgraph, hnorm, hself⟩ := exists_innerCentralThreePieceInverse hg G hjpos A
    hslope (fixedCentralModelColumnCost_nonneg M _) hd hj hκ
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4) hE
    (fixedCentralPhysicalModelChart_column_bound B D hD hborder G 1 q hT hcap
      hcolumn hcore hw hleft hright hB M hk hjpos)
    (fixedCentralPhysicalModelChart_dirichlet_bound B D hD hborder G 1 q hT hcap
      hcolumn hcore hw hleft hright hB M hq hC.le)
  exact ⟨hg.2.2.1.1, inverse, hgraph, hnorm, hself⟩

end ContinuousFlexibility.Radial
