import ContinuousFlexibility.Analysis.N04NegativeGeometryNormalizedFactorBounds
import ContinuousFlexibility.Analysis.N04NegativeGeometryRootCollarTowers

/-!
# The bounded normalized factors are the actual root coefficients

The first N01 normalized speed factor is the negative physical drift.
On a common profile locus its second factor is the actual physical speed
ratio. These are pointwise identities of the unchanged fields, and hence
identify their genuine mixed towers on every open subdomain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

theorem normalizedSpeedFactor_eq_rootFields
    (z : AnnularState W.S × ℝ) {p : PolarPoint} (hp : p ∈ annularOpen W.D)
    (hprofile : stateProfile W.D W.S W.C z.1 p.1 = W.D.w p.1) :
    normalizedSpeedFactor W.D W.S W.C 0 z p =
        -(n06PhysicalRootFields W.D W.S W.C z p).1 ∧
      normalizedSpeedFactor W.D W.S W.C 1 z p =
        (n06PhysicalRootFields W.D W.S W.C z p).2 := by
  have hr : p.1 ≠ 0 :=
    (W.through03.1.1.1.1.choose_spec.1.1.trans hp.1.1).ne'
  have hw : stateProfile W.D W.S W.C z.1 p.1 ≠ 0 := by
    rw [hprofile]
    exact (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hp.1).ne'
  have hZ := contDiff_stateHeight_of_n01 W.hS W.hT W.through03.1.1 z
  let Q := heightQ (profileEnergy (stateProfile W.D W.S W.C z.1) p)
    (heightRadial (stateHeight W.D W.S W.C z) p)
    (angularPartial (heightAngular (stateHeight W.D W.S W.C z)) p)
  have hcancel : stateProfile W.D W.S W.C z.1 p.1 *
      (Q / stateProfile W.D W.S W.C z.1 p.1) = Q := by
    field_simp [hw]
  constructor
  · change profileEnergy (stateProfile W.D W.S W.C z.1) p *
        radialPartial (heightAngular (stateHeight W.D W.S W.C z)) p /
        (stateProfile W.D W.S W.C z.1 p.1 *
          (Q / stateProfile W.D W.S W.C z.1 p.1)) =
      -characteristicDrift (stateProfile W.D W.S W.C z.1) (stateHeight W.D W.S W.C z) p
    rw [hcancel, n06_characteristicDrift_eq_polarJets
      (hZ.contDiffAt.of_le (by simp)) hr]
    dsimp only [Q]
    ring
  · change Real.sqrt (polarDiscriminant (stateProfile W.D W.S W.C z.1)
        (stateHeight W.D W.S W.C z) p) /
        (Q / stateProfile W.D W.S W.C z.1 p.1) =
      W.D.w p.1 * Real.sqrt (polarDiscriminant (stateProfile W.D W.S W.C z.1)
        (stateHeight W.D W.S W.C z) p) / Q
    rw [hprofile, div_div_eq_mul_div]
    ring

namespace NegativeRootCollar

variable {W : N04RealizationStart} {m : ℕ} {side : Bool}
  (B : NegativeRootCollar W m side)

theorem coefficients_eq_normalizedSpeedFactors
    (z : AnnularState W.S × ℝ) {p : PolarPoint} (hp : p ∈ B.strip) :
    B.drift z p = -B.orientation *
        normalizedSpeedFactor W.D W.S W.C 0 z (rootProfileShift B.root B.orientation p) ∧
      B.speed z p = B.referenceSpeed p *
        normalizedSpeedFactor W.D W.S W.C 1 z (rootProfileShift B.root B.orientation p) := by
  have hB := B.point p.1 hp.1
  have hpAnn : rootProfileShift B.root B.orientation p ∈ annularOpen W.D :=
    ⟨hB.1, mem_univ _⟩
  have hn := W.normalizedSpeedFactor_eq_rootFields z hpAnn (hB.2.2 z.1)
  have hw : W.D.w (rootProfileShift B.root B.orientation p).1 ≠ 0 :=
    (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hB.1).ne'
  have hf := n06_factoredRootFields_eq_physical W.D W.S W.C
    z B.factor B.root B.orientation p hw
  constructor
  · change orientedCharacteristicDrift _ _ _ _ _ = _
    rw [hf.1, hn.1]
    ring
  · exact hf.2.trans (congrArg (fun a => B.referenceSpeed p * a) hn.2.symm)

end NegativeRootCollar

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootCollar.coefficients_eq_normalizedSpeedFactors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootCollar.coefficients_eq_normalizedSpeedFactors
