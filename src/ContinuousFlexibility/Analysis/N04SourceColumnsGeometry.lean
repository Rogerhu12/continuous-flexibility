import ContinuousFlexibility.Analysis.N04SourceColumnsIdentities

/-!
# The admissible atlas and its actual inverse determinant

The admissibility certificate gives the qualitative chart geometry on the
same neighborhood.  The auxiliary replacement preserves those fields.
The determinant family below is the explicit first-jet polynomial from
`N04SourceColumnsIdentities`, with the stored physical/canonical width ratio.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

theorem n04SourceColumns_unitPoint_mem {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} (hlen : K.left m < K.right m) {p : PolarPoint} (hp : p ∈ unitStrip) :
    canonicalUnitPoint K m p ∈ canonicalOpen S K m := by
  have hl := mul_pos (sub_pos.mpr hlen) hp.1.1
  have hu := mul_lt_of_lt_one_right (sub_pos.mpr hlen) hp.1.2
  refine ⟨?_, mem_univ _⟩
  change K.left m < K.left m + (K.right m - K.left m) * p.1 ∧
    K.left m + (K.right m - K.left m) * p.1 < K.right m
  constructor <;> linarith

private theorem n04SourceColumns_determinant_congr
    (c : ℕ → ℝ) {R R₀ A A₀ : ℕ → PolarPoint → ℝ}
    (hR : R = R₀) (hA : A = A₀) :
    (fun m p => c m *
      (mixedDerivative 1 0 (R m) p * (1 + mixedDerivative 0 1 (A m) p) -
        mixedDerivative 1 0 (A m) p * mixedDerivative 0 1 (R m) p)) =
    (fun m p => c m *
      (mixedDerivative 1 0 (R₀ m) p * (1 + mixedDerivative 0 1 (A₀ m) p) -
        mixedDerivative 1 0 (A₀ m) p * mixedDerivative 0 1 (R₀ m) p)) := by
  rw [hR, hA]

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- Admissibility uses the same supplied family as the atlas; no new
interpolation or transport is chosen by this geometric bridge. -/
theorem sourceColumns_geometry_of_admissible {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) : CanonicalGeometry G.W.D (G.S η) (G.C η) (G.V η) b ε := by
  have hm := h.2.2.2.2.2
  let B := hm.choose
  let lower := hm.choose_spec.choose
  let upper := hm.choose_spec.choose_spec.choose
  have hN : G.N = B.region := hm.choose_spec.choose_spec.choose_spec.1
  have hg := n04Realization_gaugeAtlas_of_family G.W.hT G.W.hS G.W.through03 G.W.field
    G.X.e₀ G.e G.X.cell G.X.src B G.Y G.H h.2.2.2.1 G.τ G.σ G.Q lower upper
    h.1 h.2.1 h.2.2.1 hm.choose_spec.choose_spec.choose_spec.2 h.2.2.2.2.1
  have hraw : CanonicalGeometry G.W.D G.W.S G.W.C
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N) b ε := by
    rw [hN]
    exact hg.1
  exact canonicalGeometry_replaceAuxiliaryColumn hraw η

theorem sourceColumns_referenceStateConditions :
    referenceStateConditions G.W.D (G.S η) (G.C η) :=
  G.W.through03.1.1.2.2.1

theorem sourceColumns_lift_mem {b : ℕ} {ε : ℝ} {z : Parameter (G.S η)}
    (hz : z ∈ sectorNeighborhood (G.S η) b ε ε) :
    G.lift η z ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
  liftSectorParameter_mem_stateNeighborhood hz le_rfl

theorem sourceColumns_lift_sector (z : Parameter (G.S η)) :
    stateSector (G.S η) (G.lift η z).1 :=
  (G.sourceColumns_referenceStateConditions η).liftSectorParameter_sector z

theorem sourceColumns_lift_zero : G.lift η (0 : Parameter (G.S η)) = G.ref η := by
  simp only [lift, ref, liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
    ZeroMemClass.coe_zero, add_zero]

theorem sourceColumns_atomFamily_zero (a : Atom) :
    G.atomFamily η a (0 : Parameter (G.S η)) = G.atomRef η a := by
  funext m p
  change atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
    (G.lift η 0) m a p = atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
      (G.ref η) m a p
  rw [G.sourceColumns_lift_zero η]

/-- The stored width ratio is independent of the state parameter. -/
def sourceColumnsWidthRatio (m : ℕ) : ℝ :=
  ((G.V η).physicalRight m - (G.V η).physicalLeft m) /
    ((G.V η).right m - (G.V η).left m)

/-- The inverse determinant expressed in the current first mixed jets. -/
def sourceColumnsInverseDeterminant : Parameter (G.S η) → ℕ → PolarPoint → ℝ :=
  fun z m p => G.sourceColumnsWidthRatio η m *
    (mixedDerivative 1 0 (G.atomFamily η .inverseRadial z m) p *
        (1 + mixedDerivative 0 1 (G.atomFamily η .inverseAngleDefect z m) p) -
      mixedDerivative 1 0 (G.atomFamily η .inverseAngleDefect z m) p *
        mixedDerivative 0 1 (G.atomFamily η .inverseRadial z m) p)

/-- The identical polynomial evaluated on the reference atoms. -/
def sourceColumnsInverseDeterminantRef : ℕ → PolarPoint → ℝ :=
  fun m p => G.sourceColumnsWidthRatio η m *
    (mixedDerivative 1 0 (G.atomRef η .inverseRadial m) p *
        (1 + mixedDerivative 0 1 (G.atomRef η .inverseAngleDefect m) p) -
      mixedDerivative 1 0 (G.atomRef η .inverseAngleDefect m) p *
        mixedDerivative 0 1 (G.atomRef η .inverseRadial m) p)

theorem sourceColumns_inverseDeterminant_zero :
    G.sourceColumnsInverseDeterminant η (0 : Parameter (G.S η)) =
      G.sourceColumnsInverseDeterminantRef η :=
  n04SourceColumns_determinant_congr (G.sourceColumnsWidthRatio η)
    (G.sourceColumns_atomFamily_zero η .inverseRadial)
    (G.sourceColumns_atomFamily_zero η .inverseAngleDefect)

/-- The explicit polynomial is the genuine inverse-chart determinant. -/
theorem sourceColumns_inverseDeterminant_eq {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.sourceColumnsInverseDeterminant η z m p =
      planeJacobian ((G.V η).inverseChart (G.lift η z) m)
        (canonicalUnitPoint (G.V η) m p) := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hc := hg.charts (G.lift η z) (G.sourceColumns_lift_mem η hz)
    (G.sourceColumns_lift_sector η z) m
  have hi := (hc.2.2.2.2.2.1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  exact (n04SourceColumns_inverseJacobian_unit_mixed (G.lift η z) m
    (sub_pos.mpr (hg.referenceBounds m).1).ne'
    (sub_pos.mpr (hg.referenceBounds m).2.1).ne'
    ((hG.1 .inverseRadial trivial).1 z hz m trivial).1
    ((hG.1 .inverseAngleDefect trivial).1 z hz m trivial).1 hp hi).symm

theorem sourceColumns_inverseDeterminantRef_eq {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.sourceColumnsInverseDeterminantRef η m p =
      planeJacobian ((G.V η).inverseChart (G.ref η) m)
        (canonicalUnitPoint (G.V η) m p) := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hzero := reference_mem_stateNeighborhood (G.S η) (G.C η) b hA.2.1
  have hc := hg.charts (G.ref η) hzero
    (G.sourceColumns_referenceStateConditions η).stateSector m
  have hi := (hc.2.2.2.2.2.1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  exact (n04SourceColumns_inverseJacobian_unit_mixed (G.ref η) m
    (sub_pos.mpr (hg.referenceBounds m).1).ne'
    (sub_pos.mpr (hg.referenceBounds m).2.1).ne'
    (href.1 m .inverseRadial).1 (href.1 m .inverseAngleDefect).1 hp hi).symm

theorem sourceColumns_factor_eq_absDeterminant {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.atomFamily η .sourceFactor z m p =
      G.pulledHeight η z m p * |G.sourceColumnsInverseDeterminant η z m p| := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  rw [G.sourceColumns_inverseDeterminant_eq η hA hG hz m hp]
  exact n04SourceColumns_sourceFactor_eq_inverseJacobian hg
    (G.sourceColumns_lift_mem η hz) (G.sourceColumns_lift_sector η z) m
      (n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp)

theorem sourceColumns_factorRef_eq_absDeterminant {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.atomRef η .sourceFactor m p =
      G.pulledHeightRef η m p * |G.sourceColumnsInverseDeterminantRef η m p| := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  rw [G.sourceColumns_inverseDeterminantRef_eq η hA href m hp]
  exact n04SourceColumns_sourceFactor_eq_inverseJacobian hg
    (reference_mem_stateNeighborhood (G.S η) (G.C η) b hA.2.1)
    (G.sourceColumns_referenceStateConditions η).stateSector m
      (n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp)

theorem sourceColumns_inverseDeterminant_ne_zero {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.sourceColumnsInverseDeterminant η z m p ≠ 0 := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hz' := G.sourceColumns_lift_mem η hz
  have hs := G.sourceColumns_lift_sector η z
  have hc := hg.charts (G.lift η z) hz' hs m
  have hn := (hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)).2.1
  rw [G.sourceColumns_inverseDeterminant_eq η hA hG hz m hp]
  apply abs_ne_zero.mp
  rw [n07a_actual_inverseChart_jacobian_abs hg hz' hs m hq]
  exact inv_ne_zero (abs_ne_zero.mpr hn)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
