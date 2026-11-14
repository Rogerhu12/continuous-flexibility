module

public import ContinuousFlexibility.Analysis.N04PrincipalPositiveOrientation
public import ContinuousFlexibility.Scalar.WeightedPartialIdentities

/-!
# Positive principal atoms in the supplied scalar inputs

The canonical interval is exactly the unit interval. The four entries of
the inverse derivative are first derivatives of the two inverse atoms,
with the fixed physical width retained. The positive inverse determinant
then gives one scalar reciprocal and a finite polynomial formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

theorem n04PrincipalPositive_coordinatePair_fderiv
    {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (l w : ℝ) (v : PolarPoint) :
    fderiv ℝ (fun q => (l + w * f q, q.2 + g q)) p v =
      (w * fderiv ℝ f p v, v.2 + fderiv ℝ g p v) := by
  have hsum : DifferentiableAt ℝ (fun q : PolarPoint => q.2 + g q) p :=
    differentiableAt_snd.add hg
  rw [DifferentiableAt.fderiv_prodMk ((hf.const_mul w).const_add l)
    hsum, fderiv_const_add, fderiv_const_mul hf w,
    fderiv_fun_add differentiableAt_snd hg]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, fderiv_snd, ContinuousLinearMap.coe_snd', smul_eq_mul]

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The actual inverse derivative uses only the two stored inverse
atoms and the physical length of the same piece. -/
theorem n04PrincipalPositive_inverse_entries {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood (G.S η) (G.C η) b ε)
    (hs : stateSector (G.S η) z.1) {m : ℕ} (hm : G.Pos η m) (q : PolarPoint) :
    let R := atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseRadial
    let T := atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect
    let W := (G.V η).physicalRight m - (G.V η).physicalLeft m
    let M := fderiv ℝ ((G.V η).inverseChart z m) q
    (M (1, 0)).1 = W * mixedDerivative 1 0 R q ∧
      (M (0, 1)).1 = W * mixedDerivative 0 1 R q ∧
      (M (1, 0)).2 = mixedDerivative 1 0 T q ∧
      (M (0, 1)).2 = 1 + mixedDerivative 0 1 T q := by
  let R := atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseRadial
  let T := atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect
  let W := (G.V η).physicalRight m - (G.V η).physicalLeft m
  have hunit := G.n04PrincipalPositive_unitPoint_eq η hm
  have hgeometry := G.n04PrincipalPositive_rangeGeometry h η hz hs hm
  have hRformula : R = fun p =>
      (((G.V η).inverseChart z m p).1 - (G.V η).physicalLeft m) / W := by
    funext p
    simp only [R, atom, hunit, id_eq, W]
  have hTformula : T = fun p => ((G.V η).inverseChart z m p).2 - p.2 := by
    funext p
    simp only [T, atom, hunit, id_eq]
  have hR : ContDiff ℝ ∞ R := by
    rw [hRformula]
    exact (hgeometry.inverse_smooth.fst.sub contDiff_const).div_const W
  have hT : ContDiff ℝ ∞ T := by
    rw [hTformula]
    exact hgeometry.inverse_smooth.snd.sub contDiff_snd
  have hW : W ≠ 0 :=
    (sub_pos.mpr ((G.n04PrincipalPositive_admissible_parts h η).1.referenceBounds m).1).ne'
  have hmap : (G.V η).inverseChart z m =
      fun p => ((G.V η).physicalLeft m + W * R p, p.2 + T p) := by
    funext p
    apply Prod.ext
    · simp only [R, atom, hunit, id_eq]
      change _ = (G.V η).physicalLeft m + W * ((_ - (G.V η).physicalLeft m) / W)
      rw [mul_div_cancel₀ _ hW]
      ring
    · simp only [T, atom, hunit, id_eq]
      ring
  have he (v : PolarPoint) := n04PrincipalPositive_coordinatePair_fderiv
    (hR.differentiable (by simp) q) (hT.differentiable (by simp) q)
    ((G.V η).physicalLeft m) W v
  rw [← hmap] at he
  have hRr := radialPartial_eq_mixedDerivative_on isOpen_univ hR.contDiffOn (mem_univ q)
  have hRt := angularPartial_eq_mixedDerivative_on isOpen_univ hR.contDiffOn (mem_univ q)
  have hTr := radialPartial_eq_mixedDerivative_on isOpen_univ hT.contDiffOn (mem_univ q)
  have hTt := angularPartial_eq_mixedDerivative_on isOpen_univ hT.contDiffOn (mem_univ q)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg Prod.fst (he (1, 0))).trans (congrArg (W * ·) hRr)
  · exact (congrArg Prod.fst (he (0, 1))).trans (congrArg (W * ·) hRt)
  · exact (congrArg Prod.snd (he (1, 0))).trans ((zero_add _).trans hTr)
  · exact (congrArg Prod.snd (he (0, 1))).trans (congrArg (1 + ·) hTt)

/-- The determinant used by the positive formula is a polynomial in
the first spatial jets of the inverse atoms. -/
theorem n04PrincipalPositive_inverseJacobian_formula {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood (G.S η) (G.C η) b ε)
    (hs : stateSector (G.S η) z.1) {m : ℕ} (hm : G.Pos η m) (q : PolarPoint) :
    let R := atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseRadial
    let T := atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect
    let W := (G.V η).physicalRight m - (G.V η).physicalLeft m
    planeJacobian ((G.V η).inverseChart z m) q =
      (W * mixedDerivative 1 0 R q) * (1 + mixedDerivative 0 1 T q) -
        mixedDerivative 1 0 T q * (W * mixedDerivative 0 1 R q) := by
  have he := G.n04PrincipalPositive_inverse_entries h η hz hs hm q
  simp only [planeJacobian, he.1, he.2.1, he.2.2.1, he.2.2.2]

/-- Exact formulas for all three positive principal atoms. Every input
is a pulled interface field or a first derivative of an inverse atom. -/
theorem n04PrincipalPositive_principal_unit_formula {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    {m : ℕ} (hm : G.Pos η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    let R := G.atomFamily η .inverseRadial z m
    let T := G.atomFamily η .inverseAngleDefect z m
    let W := (G.V η).physicalRight m - (G.V η).physicalLeft m
    let Rr := W * mixedDerivative 1 0 R q
    let Rt := W * mixedDerivative 0 1 R q
    let Tr := mixedDerivative 1 0 T q
    let Tt := 1 + mixedDerivative 0 1 T q
    let J := Rr * Tt - Tr * Rt
    let a := G.pulled η (G.coefficientField η 0) z m q
    let b := G.pulled η (G.coefficientField η 1) z m q
    let c := G.pulled η (G.coefficientField η 2) z m q
    let scale := G.pulledHeight η z m q ^ 2 * J⁻¹
    G.atomFamily η .principalA z m q =
        scale * (a * Tt ^ 2 - 2 * b * Tt * Rt + c * Rt ^ 2) ∧
      G.atomFamily η .principalB z m q =
        scale * (-(a * Tt * Tr) + b * (Tt * Rr + Rt * Tr) - c * Rt * Rr) ∧
      G.atomFamily η .principalC z m q =
        scale * (a * Tr ^ 2 - 2 * b * Tr * Rr + c * Rr ^ 2) := by
  let w := G.lift η z
  have hw : w ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector (G.S η) w.1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hend := G.n04PrincipalDivided_positive_endpoints η hm
  have hunit := G.n04PrincipalPositive_unitPoint_eq η hm
  have hqK : q ∈ canonicalOpen (G.S η) (G.V η) m := by
    simpa only [canonicalOpen, unitStrip, hend.1, hend.2] using hq
  have hraw := G.n04PrincipalPositive_principal_eq_adjugate h η hw hs m hqK
  have hform := n04PrincipalPositive_adjugate_inverseHeight_formula
    ((G.L η).coefficients w) ((G.V η).inverseChart w m)
    (fun p => (G.V η).height w m ((G.V η).inverseChart w m p)) q
  have he := G.n04PrincipalPositive_inverse_entries h η hw hs hm q
  have hJ := G.n04PrincipalPositive_inverseJacobian_formula h η hw hs hm q
  have hJpos := G.n04PrincipalPositive_inverseJacobian_pos h η hw hs hm q
  dsimp only at hform
  rw [abs_of_pos hJpos, hJ, he.1, he.2.1, he.2.2.1, he.2.2.2] at hform
  have hfull := And.intro (hraw.1.trans hform.1)
    (And.intro (hraw.2.1.trans hform.2.1) (hraw.2.2.trans hform.2.2))
  simpa [atomFamily, atom, pulled, pulledHeight, heightField, pulledPoint,
    coefficientField, canonicalCoefficientComponent, hunit, div_eq_mul_inv] using hfull

end N04RealizationGauge

end ContinuousFlexibility.Analysis
