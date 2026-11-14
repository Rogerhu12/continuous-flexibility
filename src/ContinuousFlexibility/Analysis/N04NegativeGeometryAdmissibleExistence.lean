module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.N04RealizationLeadOptical
public import ContinuousFlexibility.Analysis.SpacesCutoff

/-!
# Admissible gauges exist independently of the open current-jet statements

The original qualitative positive-family construction supplies the matching
and reference identity required by `N04RealizationGauge.Admissible`.  Neither
the positive nor the negative current-geometry obligation is used here.

Every retained start has a positive component, since its reference profile
vanishes at the left endpoint and is positive in the annulus.  The reference
family certificate makes its displayed height strictly positive everywhere.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- There is an actual admissible gauge, obtained from the existing
qualitative matching construction. -/
theorem n04NegativeGeometry_exists_admissible_gauge :
    ∃ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε := by
  classical
  let W : N04RealizationStart := n04RealizationStart_nonempty.some
  let X : N04RealizationChoice W :=
    (n04RealizationChoice_nonempty n04Realization_opticalObligation W).some
  have hf : Continuous (deriv W.D.w) :=
    (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
  let e : ℕ ≃ N04WholePieceIndex W.D :=
    (n04WholePiece_exists_enumeration (D := W.D) hf).some
  have hborder : RadialTrueBorder W.D := W.radial.2.2.2.1
  let B : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi) :=
    (n04PositiveNormalizationBuffer_nonempty hf hborder.2.1 hborder.2.2.1).some
  have hreference := n04Coordinates_exists_positive_reference_family
    W.hT W.hS W.through03 W.field X.e₀ X.src (show 1 ≤ (4 : ℕ) by decide)
  exact hreference.elim fun Y hY => hY.elim fun H hYH => by
    have hfamily := n04Coordinates_exists_fixed_positive_family
      W.hT W.hS W.through03 W.field X.e₀ X.src B 3
    let b := hfamily.choose
    let ε := hfamily.choose_spec.choose
    have hneighborhood := hfamily.choose_spec.choose_spec
    have hκ := hneighborhood.2.2.2
    let κ := hκ.choose
    have hM := hκ.choose_spec
    let M := hM.choose
    have hHb := hM.choose_spec
    let Hb := hHb.choose
    have hClog := hHb.choose_spec
    let Clog := hClog.choose
    have hMσ := hClog.choose_spec
    let Mσ := hMσ.choose
    have hδ := hMσ.choose_spec
    let δ := hδ.choose
    have hmatched := hδ.choose_spec.2
    let τ := n04FixedPositiveTransport (W.A X.e₀) X.src B 3 κ M Mσ
    let σ := n04FixedPositiveInverse (W.A X.e₀) X.src B 3 κ M Mσ
    let Q := n04FixedPositiveHeight (W.A X.e₀) X.src 3 δ
    let lower : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ := fun i =>
      endpointFiberLower 3 (n04PositiveLeft i) (n04PositiveRight i)
        (B.centerLeft i) (B.centerRight i) (κ i) (Mσ i) * (κ i / 2)
    let upper : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ := fun i =>
      Real.exp 2 * Hb i ^ 2
    let G : N04RealizationGauge := ⟨W, X, e, Y, H, τ, σ, Q, B.region⟩
    have hG : G.Admissible b ε :=
      ⟨hneighborhood.1, hneighborhood.2.1, hneighborhood.2.2.1, hYH,
        hmatched.2, B, lower, upper, rfl, hmatched.1⟩
    exact ⟨G, b, ε, hG⟩

/-- Positivity of the reference profile forces at least one positive
component; its existence does not depend on any current geometry claim. -/
theorem n04NegativeGeometry_positiveComponent_nonempty (W : N04RealizationStart) :
    Nonempty (N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) := by
  have hp := spaces_exists_positive_deriv_interval
    (n04b_profileGeometry_of_through03 W.through03)
  exact hp.elim fun l hr => hr.elim fun r h => by
    have hl : l ∈ n04PositiveRegion W.D.a W.D.b (deriv W.D.w) :=
      ⟨⟨h.1, h.2.1.trans h.2.2.1⟩, h.2.2.2 l ⟨le_rfl, h.2.1.le⟩⟩
    have hi := (n04PositiveComponent_existsUnique_mem_iff l).mpr hl
    exact ⟨hi.choose⟩

theorem n04NegativeGeometry_admissible_referenceHeight_pos
    {G : N04RealizationGauge} {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w)) (r : ℝ) :
    0 < G.H i r :=
  ((hG.2.2.2.1 i).1.height_positive (r, 0))

/-- A point strictly between a positive component's left endpoint and
the central normalization region, with nonzero reference height. -/
theorem n04NegativeGeometry_exists_positive_side_point
    {G : N04RealizationGauge} {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (B : N04PositiveNormalizationBuffer G.W.D.a G.W.D.b
      (deriv G.W.D.w) (tsupport G.W.D.chi)) :
    ∃ (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w)) (r : ℝ),
      n04PositiveLeft i < r ∧ r < B.centerLeft i ∧ 0 < G.H i r := by
  let i := (n04NegativeGeometry_positiveComponent_nonempty G.W).some
  have hbetween := exists_between (B.ordered i).1
  exact hbetween.elim fun r hr =>
    ⟨i, r, hr.1, hr.2, n04NegativeGeometry_admissible_referenceHeight_pos hG i r⟩

end ContinuousFlexibility.Analysis

/--
info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_exists_admissible_gauge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_exists_admissible_gauge
