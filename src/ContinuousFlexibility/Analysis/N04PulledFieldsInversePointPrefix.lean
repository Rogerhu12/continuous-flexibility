import ContinuousFlexibility.Analysis.N04PulledFieldsInverseRawFamily
import ContinuousFlexibility.Analysis.N04PulledFieldsInverseAffineBounds
import ContinuousFlexibility.Analysis.N04PulledFieldsSampleCost
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Prefix bounds for the actual inverse-chart point

The two normalized inverse atoms share one interpolation base. The
reference length atom controls the affine radial rescaling. The angular
projection is retained exactly, so positive parameter orders keep the
sampled height factor. Every tower in the conclusion is a genuine tower
of the retained inverse point on the original neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFieldsInversePoint_coefficient
    {E P B ell : ℝ} (hE : 1 ≤ E) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hell : |ell| ≤ P * E ^ P) :
    |ell| * (B * E ^ B) + B * E ^ B + 1 ≤
      (P * B + B + 1) * E ^ (P + B) := by
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hEB : E ^ B ≤ E ^ (P + B) :=
    Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hP)
  have hone : 1 ≤ E ^ (P + B) := Real.one_le_rpow hE (add_nonneg hP hB)
  calc
    _ ≤ (P * E ^ P) * (B * E ^ B) + B * E ^ (P + B) + E ^ (P + B) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hell (mul_nonneg hB (Real.rpow_nonneg hEpos.le _)))
        (mul_le_mul_of_nonneg_left hEB hB)) hone
    _ = _ := by rw [Real.rpow_add hEpos]; ring

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

/-- Interpolation of the sector grading is independent of the auxiliary
column; it is supplied by the original physical spaces. -/
theorem n04PulledFields_parameter_hasInterpolation
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    HasInterpolation (parameterGrading (G.S η)) := by
  have h : HasInterpolation (parameterGrading G.W.S) :=
    hasInterpolation_of_hasSmoothing (n07aParameterGrading_monotone G.W.S)
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing G.W.hS) hasSmoothing_realGrading)
  exact h

/-- The static physical length has the sampled bound of its own atom
in the same reference certificate. -/
theorem n04PulledFields_reference_physicalLength_bound
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : G.ReferenceData η) :
    ∃ P : ℝ, 0 < P ∧ ∀ m,
      |(G.V η).physicalRight m - (G.V η).physicalLeft m| ≤
        P * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ P := by
  refine (href.2 0).elim fun P hP => ⟨P, hP.1, fun m => ?_⟩
  have hp : ((1 / 2, 0) : PolarPoint) ∈ unitStrip := by
    constructor <;> norm_num
  simpa only [mixedDerivative, iteratedDeriv_zero, atom] using
    hP.2 m .physicalLength (1 / 2, 0) hp 0 0 (by omega)

private def n04PulledFieldsInversePoint_atom : Bool → Atom
  | false => .inverseRadial
  | true => .inverseAngleDefect

private theorem n04PulledFieldsInversePoint_atom_geometry (i : Bool) :
    atomIsGeometry (n04PulledFieldsInversePoint_atom i) := by
  cases i <;> trivial

/-- One low order is selected before every parameter prefix. The bound
holds for any genuine tower of the actual inverse point, with one common
sampled coefficient for all pieces. -/
theorem n04PulledFields_inversePoint_prefix
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ offset : ℕ, ∀ N : ℕ,
      ∃ M A : ℝ, 1 ≤ M ∧ 0 ≤ A ∧
      ∀ m, ∀ Jφ : SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
        (fun z : Parameter (G.S η) × PolarPoint =>
          G.pulledPoint η (G.lift η z.1) m z.2),
      ∀ z ∈ sectorNeighborhood (G.S η) base ε ε, parameterGrading (G.S η) low z ≤ 1 →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R →
      parameterGrading (G.S η) (low + N + offset + 1) z ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
      (∀ i, parameterGrading (G.S η) low (v i).1 ≤ 1) →
      (∀ i, parameterGrading (G.S η) (low + N + offset + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        ‖Jφ.D n (z, q) v‖ ≤ M * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
          parameterHeightWeight
            (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
          (R ^ (1 / (((N + offset : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  let a : Bool → Atom := n04PulledFieldsInversePoint_atom
  have ha : ∀ i, atomIsGeometry (a i) := n04PulledFieldsInversePoint_atom_geometry
  let RF : ∀ i m, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε) unitStrip
      (fun z => G.atomFamily η (a i) z m) :=
    fun i m => n04PulledFields_currentData_rawMixedRegularity (hgeo.1 (a i) (ha i))
      (fun n => (href.1 n (a i)).1) m
  let J : ∀ i m, SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.atomFamily η (a i) z.1 m z.2) :=
    fun i m => n04PulledFields_geometryAtom_jointDirections G η hgeo href (a i) (ha i) m
  refine (n04PulledFields_sampleHeight_bounded G).elim fun Hmax hHmax => ?_
  have hscalar := n04PulledFields_currentData_rawFamily_pureWord
    (ι := Bool) (fun i => hgeo.1 (a i) (ha i))
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1
    (zero_le_one.trans hHmax.1) (hHmax.2 η)
    (fun i m => (href.1 m (a i)).1)
    (fun s => ⟨(href.2 s).choose, (href.2 s).choose_spec.1,
      fun i m q r t hrt => (href.2 s).choose_spec.2 m (a i) q.val q.property r t hrt⟩)
    RF J (n04PulledFields_parameter_hasInterpolation G η)
  refine (n04PulledFields_reference_physicalLength_bound G η href).elim fun P hP => ?_
  refine hscalar.elim fun low hlow => ⟨low, hlow.1, fun K => ?_⟩
  refine (hlow.2 K).elim fun shift hshift => ⟨shift * K, fun N => ?_⟩
  refine (hshift N).elim fun B hB => ?_
  have hM : 1 ≤ P * B + B + 1 := by
    nlinarith [mul_nonneg hP.1.le hB.1.le]
  refine ⟨P * B + B + 1, P + B, hM, add_nonneg hP.1.le hB.1.le, ?_⟩
  intro m Jφ z hz hzlow q hq R hR hzR n hn hnN w hw v hvlow hvR hvphys hvstate hvangle
  have hE : 1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) := (G.cost_nonneg η).2.2 m
  have hH : 0 ≤ G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _
  have ht : 1 ≤ R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1)) :=
    Real.one_le_rpow hR (by positivity)
  have hlen := (n04PulledFields_admissible_physicalLength_pos G η hadm m).ne'
  have hrad := hB.2 false m z hz hzlow q hq R hR hzR n hn hnN w hw
    v hvlow hvR hvphys hvstate hvangle
  have hang := hB.2 true m z hz hzlow q hq R hR hzR n hn hnN w hw
    v hvlow hvR hvphys hvstate hvangle
  have hraw := n04PulledFields_inverseAffine_pureWord_bound (J false m) (J true m) Jφ
    ((G.V η).physicalLeft m) ((G.V η).physicalRight m - (G.V η).physicalLeft m)
    (fun y _ => n04PulledFields_pulledPoint_eq_inverseAtoms G η m hlen y.1 y.2)
    hn w (shift * K) ⟨hz, hq⟩ v hvphys hvangle
    (mul_nonneg hB.1.le (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH ht hrad hang
  have hcoef := n04PulledFieldsInversePoint_coefficient hE hP.1.le hB.1.le (hP.2 m)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (Real.rpow_nonneg (zero_le_one.trans hR) _) _))

end ContinuousFlexibility.Analysis
