import ContinuousFlexibility.Analysis.N04RealizationCubicRegularity
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
import ContinuousFlexibility.Analysis.MixedDerivativeLocality
import ContinuousFlexibility.Analysis.N01cHeightParameterJets

/-!
# The exact positive jets of the normalized coordinate atoms

The physical unit map, the canonical width and the angular identity are
fixed in the state. Hence normalization contributes just one width
coefficient to each positive parameter jet. The same statement treats
the radial coordinate and the angle defect, with their genuine towers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04NegativeChart_coordinatePullback_positiveJet
    {U : Set E} {Ω : Set PolarPoint} {f : E → PolarPoint → ℝ}
    (hU : IsOpen U) (a c d : ℝ) (h : PolarPoint → ℝ)
    (hh : ContDiffOn ℝ ∞ h unitStrip)
    (hf : ∀ z ∈ U, ContDiffOn ℝ ∞ (f z) Ω)
    (hmap : MapsTo (fun q : PolarPoint => (a + c * q.1, q.2)) unitStrip Ω)
    (i j : ℕ) {q : PolarPoint} (hq : q ∈ unitStrip)
    (J : SmoothDirections U
      (fun z => mixedDerivative i j (f z) (a + c * q.1, q.2)))
    (K : SmoothDirections U (fun z => mixedDerivative i j
      (fun p : PolarPoint => d⁻¹ * (f z (a + c * p.1, p.2) - h p)) q))
    {k : ℕ} (hk : 0 < k) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    K.D k x v = (c ^ i / d) * J.D k x v := by
  let JC : SmoothDirections U
      (fun z => c ^ i * mixedDerivative i j (f z) (a + c * q.1, q.2)) :=
    (smoothDirections_postcompCLM J (c ^ i • ContinuousLinearMap.id ℝ ℝ)).congr
      (fun _ _ => by simp only [Function.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul])
  let JS : SmoothDirections U
      (fun z => c ^ i * mixedDerivative i j (f z) (a + c * q.1, q.2) -
        mixedDerivative i j h q) :=
    (smoothDirectionsAdd JC
      (smoothDirections_constant hU (-mixedDerivative i j h q))).congr
        (fun _ _ => (sub_eq_add_neg _ _).symm)
  have hK := n04Realization_smoothDirections_D_const_mul JS K d⁻¹
    (fun z hz => by
      rw [mixedDerivative_const_mul,
        mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
          ((hf z hz).comp
            ((contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk
              contDiff_snd).contDiffOn hmap) hh i j hq,
        n07a_mixedDerivative_radialAffine]) k hx v
  have hS := smoothDirections_D_sub_constant JC JS hk hx v
  have hC := n04Realization_smoothDirections_D_const_mul J JC (c ^ i)
    (fun _ _ => rfl) k hx v
  rw [hK, hS, hC, div_eq_mul_inv]
  ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_coordinatePullback_positiveJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_coordinatePullback_positiveJet
