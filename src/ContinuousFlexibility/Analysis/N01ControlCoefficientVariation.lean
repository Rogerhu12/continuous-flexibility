import ContinuousFlexibility.Analysis.N01SingletonControl
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Actual coefficient variations on a single optical-control line

The zeroth and first spatial jets of the radial coefficient have genuine
parameter derivatives `w χ` and `w' χ + w χ'`.  The N01 coefficient
tower therefore controls these two products at the actual reference cell
containing the evaluation radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open scoped Topology ContDiff BigOperators

theorem hasDerivAt_opticalLogPerturbation_difference
    (w χ : ℝ → ℝ) (r : ℝ) :
    HasDerivAt (fun t => opticalLogPerturbation w χ t r - w r) (w r * χ r) 0 := by
  simpa only [opticalLogPerturbation, id_eq, zero_mul, Real.exp_zero, one_mul, mul_one] using
    ((((hasDerivAt_id (0 : ℝ)).mul_const (χ r)).exp).const_mul (w r)).sub_const (w r)

theorem hasDerivAt_radial_opticalLogPerturbation_difference
    {w χ : ℝ → ℝ} {r : ℝ} (hw : DifferentiableAt ℝ w r)
    (hχ : DifferentiableAt ℝ χ r) :
    HasDerivAt (fun t => deriv (fun s => opticalLogPerturbation w χ t s - w s) r)
      (deriv w r * χ r + w r * deriv χ r) 0 := by
  have hrad (t : ℝ) :
      deriv (fun s => opticalLogPerturbation w χ t s - w s) r =
        (deriv w r + t * w r * deriv χ r) * Real.exp (t * χ r) - deriv w r := by
    have hd := (hw.hasDerivAt.mul (hχ.hasDerivAt.const_mul t).exp).sub hw.hasDerivAt
    have heq : (w * (fun s => Real.exp (t * χ s)) - w) =
        (fun s => opticalLogPerturbation w χ t s - w s) := by
      funext s
      rfl
    rw [heq] at hd
    rw [hd.deriv]
    ring
  have hlin : HasDerivAt (fun t : ℝ => deriv w r + t * w r * deriv χ r)
      (w r * deriv χ r) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (w r)).mul_const (deriv χ r)).const_add (deriv w r)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * χ r)) (χ r) 0 := by
    simpa only [id_eq, zero_mul, Real.exp_zero, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (χ r)).exp
  have hp := (hlin.mul hexp).sub_const (deriv w r)
  have hp' : HasDerivAt
      (fun t : ℝ => (deriv w r + t * w r * deriv χ r) * Real.exp (t * χ r) - deriv w r)
      (deriv w r * χ r + w r * deriv χ r) 0 := by
    convert hp.congr_of_eventuallyEq (Eventually.of_forall (fun _ => rfl)) using 1
    simp only [zero_mul, add_zero, Real.exp_zero, mul_one]
    ring
  exact hp'.congr_of_eventuallyEq (Eventually.of_forall hrad)

theorem oneHighVariationWeight_one_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight p base high 0 (fun _ : Fin 1 => v) =
      p base v + p high v := by
  classical
  have hu : (Finset.univ : Finset (Fin 1)) = {0} := by
    ext i
    simp [Subsingleton.elim i (0 : Fin 1)]
  simp only [oneHighVariationWeight, hu, Finset.prod_singleton, map_zero, add_zero,
    one_mul, Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, mul_one]

theorem oneHighVariationWeight_state_pair_one_zero
    (S : PhysicalSpacesData) (base high : ℕ) (v : AnnularState S) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high 0 (fun _ : Fin 1 => (v, (0 : ℝ))) =
        stateGrading S base v + stateGrading S high v := by
  rw [oneHighVariationWeight_one_zero]
  simp only [pairGrading, Seminorm.add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_zero, add_zero]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Every spatial radial jet is taken after identifying the actual
coefficient function on the entire radial line. -/
theorem N01Properties.coefficientFamily_singletonKappaLine
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m a : ℕ) (p : PolarPoint) (t : ℝ) :
    coefficientFamily D S C 0 a 0 p
      (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0) =
      iteratedDeriv a (fun r => opticalLogPerturbation D.w (C.control m) t r - D.w r) p.1 := by
  have hcoef (s : ℝ) (q : PolarPoint) :
      (originalCoefficients D S C
        (C.referenceState + s • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0)).a q =
        opticalLogPerturbation D.w (C.control m) s q.1 :=
    (hN.originalCoefficients_zero_single_kappa hS hT
      (singletonKappaLine_nu (hS.2.1 (3 / 4 : ℝ)) hN.2.2.1 m s)
      (fun n => singletonKappaLine_mean (hS.2.1 (3 / 4 : ℝ)) hN.2.2.1 m n s) q).1
  have href (q : PolarPoint) :
      (originalCoefficients D S C (C.referenceState, 0)).a q = D.w q.1 := by
    simpa only [zero_smul, add_zero, opticalLogPerturbation, zero_mul,
      Real.exp_zero, mul_one] using hcoef 0 q
  change mixedDerivative a 0
    (fun q => (originalCoefficients D S C
      (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0)).a q -
      (originalCoefficients D S C (C.referenceState, 0)).a q) p = _
  simp only [mixedDerivative, iteratedDeriv_zero]
  have heq :
      (fun r => (originalCoefficients D S C
        (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0)).a (r, p.2) -
        (originalCoefficients D S C (C.referenceState, 0)).a (r, p.2)) =
      (fun r => opticalLogPerturbation D.w (C.control m) t r - D.w r) := by
    funext r
    rw [hcoef, href]
  rw [heq]

theorem singletonKappa_joint_line
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (t : ℝ) :
    (C.referenceState, (0 : ℝ)) +
        t • (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, (0 : ℝ)) =
      (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0) := by
  change (C.referenceState + t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m,
    (0 : ℝ) + t • (0 : ℝ)) = _
  simp only [smul_zero, add_zero]

theorem N01Properties.coefficientFamily_singleton_line_deriv_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) (p : PolarPoint) :
    deriv (fun t : ℝ => coefficientFamily D S C 0 0 0 p
      ((C.referenceState, 0) +
        t • (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0))) 0 =
      D.w p.1 * C.control m p.1 := by
  have heq : (fun t : ℝ => coefficientFamily D S C 0 0 0 p
      ((C.referenceState, 0) + t • (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0))) =
      (fun t => opticalLogPerturbation D.w (C.control m) t p.1 - D.w p.1) := by
    funext t
    rw [singletonKappa_joint_line hS, hN.coefficientFamily_singletonKappaLine hS hT]
    exact congrFun (iteratedDeriv_zero _) p.1
  rw [heq]
  exact (hasDerivAt_opticalLogPerturbation_difference D.w (C.control m) p.1).deriv

theorem N01Properties.coefficientFamily_singleton_line_deriv_radial
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) (p : PolarPoint) :
    deriv (fun t : ℝ => coefficientFamily D S C 0 1 0 p
      ((C.referenceState, 0) +
        t • (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0))) 0 =
      deriv D.w p.1 * C.control m p.1 + D.w p.1 * deriv (C.control m) p.1 := by
  have heq : (fun t : ℝ => coefficientFamily D S C 0 1 0 p
      ((C.referenceState, 0) + t • (singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0))) =
      (fun t => deriv (fun r => opticalLogPerturbation D.w (C.control m) t r - D.w r) p.1) := by
    funext t
    rw [singletonKappa_joint_line hS, hN.coefficientFamily_singletonKappaLine hS hT,
      iteratedDeriv_one]
  rw [heq]
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  exact (hasDerivAt_radial_opticalLogPerturbation_difference
    (hgeom.1.2.2.1.1.differentiable (by simp) p.1)
    ((hcontrol.2.2.2.2.2.1 m).1.differentiable (by simp) p.1)).deriv

/-- The same constant controls the two product jets at every actual
reference cell, independently of the control label. -/
theorem N01Properties.control_product_jets_cell_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j r, r ∈ D.cells j →
      let v := singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m
      let A := B * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
        (stateGrading S base v + stateGrading S (1 + loss) v)
      |D.w r * C.control m r| ≤ A ∧
        |deriv D.w r * C.control m r + D.w r * deriv (C.control m) r| ≤ A := by
  have hdata := hN
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hcoeff, _⟩
  obtain ⟨B, hB, hbound⟩ := hcoeff 1 1
  refine ⟨B, hB, fun m j r hr => ?_⟩
  dsimp only
  let v := singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m
  have hz0 : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · simpa only [sub_self, map_zero] using hN.2.1
    · simpa only [abs_zero] using hN.2.1
  obtain ⟨J0, hJ0⟩ := hbound j 0 0 0 (r, 0) (by norm_num) hr
  obtain ⟨J1, hJ1⟩ := hbound j 0 1 0 (r, 0) (by norm_num) hr
  have hd0 : J0.D 1 (C.referenceState, 0) (fun _ => (v, (0 : ℝ))) =
      D.w r * C.control m r :=
    (J0.deriv_line (C.referenceState, 0) (v, 0) hz0).symm.trans
      (hN.coefficientFamily_singleton_line_deriv_zero hS hT m (r, 0))
  have hd1 : J1.D 1 (C.referenceState, 0) (fun _ => (v, (0 : ℝ))) =
      deriv D.w r * C.control m r + D.w r * deriv (C.control m) r :=
    (J1.deriv_line (C.referenceState, 0) (v, 0) hz0).symm.trans
      (hN.coefficientFamily_singleton_line_deriv_radial hS hT m (r, 0))
  have hb0 := hJ0 (C.referenceState, 0) hz0 (fun _ => (v, (0 : ℝ)))
  have hb1 := hJ1 (C.referenceState, 0) hz0 (fun _ => (v, (0 : ℝ)))
  rw [hd0, sub_self, oneHighVariationWeight_state_pair_one_zero] at hb0
  rw [hd1, sub_self, oneHighVariationWeight_state_pair_one_zero] at hb1
  exact ⟨hb0, hb1⟩

end ContinuousFlexibility.Statements
