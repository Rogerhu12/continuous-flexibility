import ContinuousFlexibility.Analysis.N04NegativeGeometryAdmissibleExistence
import ContinuousFlexibility.Analysis.N04NegativeGeometryGaugeValues
import ContinuousFlexibility.Analysis.N04NegativeGeometryInteriorFactor
import ContinuousFlexibility.Analysis.N04NegativeGeometryJumpObstruction

/-!
# The frozen negative-geometry obligation is false

The unrestricted directional-tower binder in `CurrentJetDataOn` requires
parameter smoothness even on pieces not satisfying its predicate. Apply
the negative-geometry obligation to an admissible gauge and to the gauge
obtained by the explicit interior height switch. A positive piece then
has two continuous pulled heights which agree at zero but differ by a
factor of two on a punctured scalar-parameter neighborhood. Their common
reference value is strictly positive, giving a contradiction.

This theorem concerns the unchanged frozen obligation. It does not use
any of the five open current-geometry subnodes and does not replace their
statements or change their shared definitions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

/-- The zeroth spatial slice of the frozen interface is a directional
tower on every piece, with no hypothesis involving the piece predicate. -/
private def n04NegativeGeometry_valueTower
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀) (m : ℕ) (y : unitStrip) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => f z m y.val - f₀ m y.val) :=
  (h.2.choose m 0 0 y).congr (fun _ _ => by
    simp only [mixedDerivative, iteratedDeriv_zero])

private theorem n04NegativeGeometry_obligation_contradicts_admissible
    (hneg : N04RealizationNegativeGeometryObligation)
    (G : N04RealizationGauge) (b : ℕ) (ε : ℝ) (hG : G.Admissible b ε) : False := by
  classical
  let B := hG.2.2.2.2.2.choose
  let φ := n04NegativeGeometryBufferFactors B
  let G' := n04NegativeGeometryPerturbedGauge G φ
  have hG' : G'.Admissible b ε :=
    n04NegativeGeometry_perturbedGauge_admissible G hG φ
      (fun i => n04NegativeGeometry_bufferFactors_spec B i)
  let η : (G.W.S.height (3 / 4 : ℝ)).Space := 0
  let i := (n04NegativeGeometry_positiveComponent_nonempty G.W).some
  let m : ℕ := G.e.symm (.inr i)
  have hi : G.e m = .inr i := G.e.apply_symm_apply (.inr i)
  have hyExists := n04NegativeGeometry_canonical_point_at_buffer_center hG B i
  let y : unitStrip := hyExists.choose
  have hy : positiveReferenceCylinderInverse (G.Y i) y.val =
      ((n04PositiveLeft i + B.centerLeft i) / 2, 0) := hyExists.choose_spec
  have hfactor : φ i (positiveReferenceCylinderInverse (G.Y i) y.val) = 2 := by
    change n04NegativeGeometryInteriorFactor (n04PositiveLeft i) (B.centerLeft i)
      (positiveReferenceCylinderInverse (G.Y i) y.val) = 2
    rw [hy]
    exact n04NegativeGeometry_interiorFactor_center _ _ 0
  have h1 := hneg G b ε hG
  let b1 : ℕ := h1.choose
  let ε1 : ℝ := h1.choose_spec.choose
  have hp1 := h1.choose_spec.choose_spec
  have h2 := hneg G' b ε hG'
  let b2 : ℕ := h2.choose
  let ε2 : ℝ := h2.choose_spec.choose
  have hp2 := h2.choose_spec.choose_spec
  let base : ℕ := max b1 b2
  let radius : ℝ := min ε1 ε2
  have hradius : 0 < radius := lt_min hp1.2.1 hp2.2.1
  let U : Set (Parameter (G.S η)) := sectorNeighborhood (G.S η) base radius radius
  have hU : IsOpen U := isOpen_sectorNeighborhood (G.S η) base radius radius
  have hsub1 : U ⊆ sectorNeighborhood (G.S η) b1 ε1 ε1 :=
    sectorNeighborhood_mono (G.S η) (le_max_left _ _) (min_le_left _ _) (min_le_left _ _)
  have hsub2 : U ⊆ sectorNeighborhood (G.S η) b2 ε2 ε2 :=
    sectorNeighborhood_mono (G.S η) (le_max_right _ _) (min_le_right _ _) (min_le_right _ _)
  have hsub : U ⊆ sectorNeighborhood (G.S η) b ε ε :=
    sectorNeighborhood_mono (G.S η) (hp1.1.trans (le_max_left _ _))
      ((min_le_left _ _).trans hp1.2.2.1) ((min_le_left _ _).trans hp1.2.2.1)
  have hzeroU : (0 : Parameter (G.S η)) ∈ U :=
    ⟨(sectorGrading (G.S η) base).map_zero'.trans_lt hradius,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hradius⟩
  let f : Parameter (G.S η) → ℝ := fun z => G.pulledHeight η z m y.val
  let g : Parameter (G.S η) → ℝ := fun z => G'.pulledHeight η z m y.val
  let Jf : SmoothDirections U (fun z => f z - G.pulledHeightRef η m y.val) :=
    (n04NegativeGeometry_valueTower (hp1.2.2.2 η).2 m y).restrict hU hsub1
  let Jg : SmoothDirections U (fun z => g z - G'.pulledHeightRef η m y.val) :=
    (n04NegativeGeometry_valueTower (hp2.2.2.2 η).2 m y).restrict hU hsub2
  have heq : ∀ t : ℝ, t ≠ 0 → (0, t) ∈ U → g (0, t) = f (0, t) / 2 := by
    intro t ht hz
    have hστ := n04NegativeGeometry_admissible_lift_leftInverse G η hG
      (0, t) (hsub hz) i
    have hratio := n04NegativeGeometry_perturbedGauge_pulledHeight_positive
      G φ η (0, t) m i hi hστ y.val
    have hswitch :
        (if t = 0 then (1 : ℝ) else
          φ i (positiveReferenceCylinderInverse (G.Y i) y.val)) = 2 :=
      (if_neg ht).trans hfactor
    change G'.pulledHeight η (0, t) m y.val = G.pulledHeight η (0, t) m y.val / 2
    calc
      G'.pulledHeight η (0, t) m y.val =
          G.pulledHeight η (0, t) m y.val /
            (if t = 0 then 1 else φ i (positiveReferenceCylinderInverse (G.Y i) y.val)) := hratio
      _ = G.pulledHeight η (0, t) m y.val / 2 :=
        congrArg (fun denominator : ℝ => f (0, t) / denominator) hswitch
  have hzero : g 0 = f 0 :=
    (n04NegativeGeometry_gauge_pulledHeight_zero G' η hG' m i hi y.val).trans
      (n04NegativeGeometry_gauge_pulledHeight_zero G η hG m i hi y.val).symm
  have hvalue : f 0 ≠ 0 :=
    (n04NegativeGeometry_gauge_pulledHeight_zero_pos G η hG m i hi y.val).ne'
  exact n04NegativeGeometry_axis_jump_contradiction Jf Jg hzeroU heq hzero hvalue
    (by norm_num : (2 : ℝ) ≠ 1)

/-- The original frozen negative-geometry obligation admits no proof:
its globally indexed tower sees an admissible discontinuous height change
on a positive piece. -/
theorem n04NegativeGeometry_obligation_false : ¬ N04RealizationNegativeGeometryObligation := by
  intro hneg
  exact n04NegativeGeometry_exists_admissible_gauge.elim fun G h =>
    h.elim fun b h => h.elim fun ε hG =>
      n04NegativeGeometry_obligation_contradicts_admissible hneg G b ε hG

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_obligation_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_obligation_false
