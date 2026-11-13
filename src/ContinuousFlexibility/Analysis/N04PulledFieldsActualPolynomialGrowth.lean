import ContinuousFlexibility.Analysis.N04PulledFieldsOriginalFactorsFixedBase
import ContinuousFlexibility.Analysis.N04PulledFieldsVelocityPolynomialFixedBase

/-!
# The actual residual-substituted coefficient error

In the exact correction polynomial, substituting the actual residual
makes both velocity inputs the same genuine actual velocity. Its height
factor is kept in one input and bounded above in the other. Consequently
the polynomial estimate does not require a second quantitative nonlinear
composition with a residual graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

local instance n04PulledFieldsActualPolynomialStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- The actual velocity estimate gives the two actual correction
coefficients, with a common low base before every parameter order. -/
theorem N01Properties.n04PulledFields_actualError_fixedBase_of_velocity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (Jv : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1) m x.2
          (R.residual (liftSectorParameter S C x.1))))
    (Jout : ∀ m, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionCoefficientError D S C R χ (liftSectorParameter S C x.1) x.2
          (R.residual (liftSectorParameter S C x.1))))
    (hv : N04PulledFieldsFixedBaseMixedGrowth
      (pairGrading (sectorGrading S) realGrading)
      (fun m => radialE (D.cellIndex (j m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) Jv) :
    let p := pairGrading (sectorGrading S) realGrading
    let W := fun m => radialE (D.cellIndex (j m))
    let F := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
    N04PulledFieldsFixedBaseMixedGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp (Jout m) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
    N04PulledFieldsFixedBaseMixedGrowth p W F
      (fun m => solveSmoothDirectionsPostcomp (Jout m) (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  let E := StateDirections S × ℝ
  let p : ℕ → Seminorm ℝ E := pairGrading (sectorGrading S) realGrading
  let U : Set E := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let F : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat (D.cellIndex (j m))
  have hF (m : ℕ) : 0 ≤ F m :=
    Real.rpow_nonneg (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT m)).2.1.le _
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    (sectorNeighborhood_convex S base ε ε).prod ((convex_Ioo (l m) (h m)).prod convex_univ)
  let entry : Fin 3 → ℕ → E × PolarPoint → ℝ := fun i _ x =>
    originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2
  let K : ∀ (i : Fin 3) (m : ℕ), SmoothDirections (U ×ˢ V m) (entry i m) :=
    fun i m => hN.originalCoefficient_stripTower hS hT j hcell l h hl hh i m
  let Ja : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun x : E × PolarPoint => (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2) :=
    fun m => (K 0 m).congrOn (fun _ _ => by
      simp only [entry, originalCoefficientEntry, eq_self_iff_true, ite_true])
  let Jb : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun x : E × PolarPoint => (originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2) :=
    fun m => (K 1 m).congrOn (fun _ _ => by
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      simp only [entry, originalCoefficientEntry, h10, eq_self_iff_true, ite_false, ite_true])
  let Jc : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun x : E × PolarPoint => (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2) :=
    fun m => (K 2 m).congrOn (fun _ _ => by
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [entry, originalCoefficientEntry, h20, h21, ite_false])
  have hdisc (m : ℕ) (x : E × PolarPoint) (hx : x ∈ U ×ˢ V m) :
      0 < (originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2 ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2 *
          (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2 := by
    have hd : 0 < lam * radialE (D.cellIndex (j m)) ^ (-P) / 2 :=
      div_pos (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)) (by norm_num)
    exact (sq_pos_of_pos hd).trans_le
      (hpositive _ (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl) m x.2 hx.2.1).2
  let Jq : ∀ m, SmoothDirections (U ×ˢ V m)
      (fun x : E × PolarPoint =>
        Real.sqrt ((originalCoefficients D S C (liftSectorParameter S C x.1)).b x.2 ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C x.1)).a x.2 *
            (originalCoefficients D S C (liftSectorParameter S C x.1)).c x.2)) :=
    fun m => correctionPolynomial_sqrtDirections (Ja m) (Jb m) (Jc m) (hdisc m)
  have hfactors := hN.n04PulledFields_originalCorrectionFactors_fixedBase
    hS hT j hcell l h hl hh hlam hP hpositive Ja Jb Jq
  let hheight := materialSample_H_M_envelope hT hN.1.1
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hFbound (m : ℕ) : F m ≤ hheight.choose * (1 : ℝ) := by
    simpa only [F, Real.rpow_zero, mul_one] using hheight.choose_spec.2 m
  have hv₀ : N04PulledFieldsFixedBaseMixedGrowth p W (fun _ => 1) Jv :=
    hv.factor_le (fun m => zero_le_one.trans (hW m)) hheight.choose_spec.1.le hFbound
  apply n04PulledFields_polynomial_fixedBase_from_velocity p hp hI W F hW hF hU hV hc
    (fun _ y hy => ⟨hy.1, mem_univ _⟩) Ja Jb Jq Jv Jv Jout hfactors hv₀ hv
  intro m x hx y hy
  exact correctionPolynomial_actual_error hN χ l h hl hh m
    (x, R.residual (liftSectorParameter S C x)) ⟨hx, mem_univ _⟩ y hy

end ContinuousFlexibility.Statements
