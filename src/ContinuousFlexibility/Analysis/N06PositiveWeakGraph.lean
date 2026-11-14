module

public import ContinuousFlexibility.Analysis.N06PositiveGraphPieces

/-!
# Actual weak PDE data produce the all-piece positive graph package

The reference geometry assumptions below are explicitly scalar: unit
positive intervals, the coefficients of the proved weak modal estimate,
and the material growth of its constant. They are not claimed as
consequences of N04. Given these geometric facts, the original volume
rows and the actual canonical weak PDE supply every graph witness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The primitive reference coefficient conditions used by the weak graph
proof, imposed only on the actual positive pieces. -/
structure N06PositiveUnitGeometry
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (a c V q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (C : ℝ) : Prop where
  constant_one_le : 1 ≤ C
  left : ∀ m, K.positive m = true → K.left m = 0
  right : ∀ m, K.positive m = true → K.right m = 1
  a_smooth : ∀ m, K.positive m = true → ContDiff ℝ ∞ (a m)
  c_continuous : ∀ m, K.positive m = true → Continuous (c m)
  potential_continuous : ∀ m, K.positive m = true → Continuous (V m)
  q_twice : ∀ m, K.positive m = true → ContDiff ℝ 2 (q m)
  one_le : ∀ m, K.positive m = true → 1 ≤ κ m
  a_lower : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1, 1 / κ m ≤ a m y
  a_upper : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1, a m y ≤ κ m
  a_derivative : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1, |deriv (a m) y| ≤ κ m
  c_lower : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / κ m ≤ c m y
  potential_bound : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1, |V m y| ≤ κ m
  c_eq_aq : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1, c m y = a m y * q m y
  q_second : ∀ m, K.positive m = true → ∀ y ∈ Icc (0 : ℝ) 1,
    |deriv (deriv (q m)) y| ≤ κ m
  material_growth : ∃ Aκ : ℝ, ∀ m, K.positive m = true →
    κ m ≤ C * T.E0 (T.sample (K.cell m)) ^ Aκ

/-- Original volume elements and their actual weak PDE produce all positive
modal families. No modal ODE, graph bound or radial derivative is an input. -/
theorem n06_positiveWeakGraphFamily_nonempty
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Vol : VolumeModelData S K} (hVol : IsVolumeModel T S K Vol)
    (β loss : ℝ) (b : ℕ) (a c V q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (C : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c V q κ C)
    (F : Vol.level β 0 b) (W : Vol.level β (-loss) b)
    (hweak : ∀ m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
      (∫ p, n06MaterialJetRow T K β (-loss) W.val m 0 p *
        n06UnitReferenceTestOperator (a m) (c m) (V m) φ p ∂canonicalMeasure S K m) =
        ∫ p, n06MaterialJetRow T K β 0 F.val m 0 p * φ p ∂canonicalMeasure S K m) :
    Nonempty (N06PositiveWeakGraphFamily T K β loss F.val W.val a c V κ) := by
  have hF : F.val ∈ canonicalVolumeGraph S K b := by
    rw [← hVol.1 β 0 b]
    exact F.property
  have hW : W.val ∈ canonicalVolumeGraph S K b := by
    rw [← hVol.1 β (-loss) b]
    exact W.property
  have hex (m : ℕ) (hm : K.positive m = true) : Nonempty
      (N06UnitWeakGraphData (a m) (c m) (V m)
        (n06MaterialJetRow T K β (-loss) W.val m)
        (n06MaterialJetRow T K β 0 F.val m) (κ m)) :=
    n06_unitWeakGraphData_nonempty (hgeometry.left m hm) (hgeometry.right m hm)
      (n06MaterialJetRow T K β (-loss) W.val m) (n06MaterialJetRow T K β 0 F.val m)
      (n06MaterialJetRow_reflection β (-loss) W.val hW m)
      (n06MaterialJetRow_reflection β 0 F.val hF m)
      (n06MaterialJetRow_weak β (-loss) W.val hW m)
      (n06MaterialJetRow_weak β 0 F.val hF m)
      (hgeometry.a_smooth m hm) (hgeometry.c_continuous m hm)
      (hgeometry.potential_continuous m hm) (hgeometry.q_twice m hm)
      (hweak m hm) (hgeometry.one_le m hm) (hgeometry.a_lower m hm)
      (hgeometry.a_upper m hm) (hgeometry.a_derivative m hm) (hgeometry.c_lower m hm)
      (hgeometry.potential_bound m hm) (hgeometry.c_eq_aq m hm) (hgeometry.q_second m hm)
  exact ⟨fun m hm => Classical.choice (hex m hm)⟩

/-- The genuine full positive graph construction, with one constant chosen
before the original source and height rows. Negative pieces are the zero
branch of n06PositivePhysicalGraphFields, and the raw lp is the one used by
the selected volume model. -/
theorem n06_positiveWeakGraph_material_package
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Vol : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hVol : IsVolumeModel T S K Vol)
    (β A loss : ℝ) (hβ : 0 < β) (b : ℕ)
    (a c V q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (C : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c V q κ C) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ F : Vol.level β 0 b, ∀ W : Vol.level β (-loss) b,
      (∀ m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
        (∫ p, n06MaterialJetRow T K β (-loss) W.val m 0 p *
          n06UnitReferenceTestOperator (a m) (c m) (V m) φ p ∂canonicalMeasure S K m) =
          ∫ p, n06MaterialJetRow T K β 0 F.val m 0 p * φ p ∂canonicalMeasure S K m) →
      ∃ P : N06PositiveWeakGraphFamily T K β loss F.val W.val a c V κ,
      ∃ f : Fin 5 → CanonicalVolumeJets S K b,
        (∀ r m, f r m = T.E0 (T.sample (K.cell m)) ^ A • n06PositivePhysicalGraphFields P r m) ∧
        (∀ r m j, WeakCanonicalAngularDerivative S K m (f r m 0) (f r m j) j.val) ∧
        (∀ r m, (fun p : PolarPoint => f r m 0 (p.1, Real.pi - p.2))
          =ᵐ[canonicalMeasure S K m] fun p => n06CubicGraphParity r * f r m 0 p) ∧
        (∀ r, ‖f r‖ ≤ Q * (‖F‖ + ‖W‖)) := by
  obtain ⟨Aκ, hgrowth⟩ := hgeometry.material_growth
  obtain ⟨Q, hQ, hpack⟩ := n06_positiveGraphFields_package hD hT β A loss C Aκ hβ
    (zero_lt_one.trans_le hgeometry.constant_one_le) a c V κ hgeometry.one_le
      hgrowth (b := b)
  refine ⟨Q, hQ, ?_⟩
  intro F W hweak
  obtain ⟨P⟩ := n06_positiveWeakGraphFamily_nonempty hVol β loss b a c V q κ C hgeometry F W hweak
  obtain ⟨f, hfields, hjets, hparity, hnorm⟩ := hpack F.val W.val P
  exact ⟨P, f, hfields, hjets, hparity, hnorm⟩

end ContinuousFlexibility.Analysis
