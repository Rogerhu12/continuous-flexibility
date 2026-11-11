import ContinuousFlexibility.Scalar.WeightedCandidateOperatorAnalysis
import ContinuousFlexibility.Scalar.WeightedCommonBall
import ContinuousFlexibility.Scalar.WeightedHomogeneousFamilies
import ContinuousFlexibility.Scalar.WeightedOperatorBounds
import ContinuousFlexibility.Scalar.WeightedWitnessProperties
import ContinuousFlexibility.Scalar.WeightedGeometry

/-!
# The actual weighted scalar witness

All finite realizations and both operator families are assembled here.
The base and loss dominate the previously fixed orders, and a single state
ball lies inside the geometric, scalar-composition, and operator domains.
Every clause uses those same maps and that same ball.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- The unconditional S05 witness on the original physical weighted spaces. -/
theorem scalarWeightedS05 : S05WeightedStatement := by
  intro D T S hD hT hS v₀
  have hp := scalarStateGrading_monotone S
  have hph := scalarHeightGrading_monotone S
  have hpc := weighted_scalarCommonHeightGrading_monotone S
  obtain ⟨εg, hεg, _, hgeometry⟩ := exists_scalarStateBall_geometry hD hT hS v₀
  obtain ⟨V, hV, hxV, hlsmooth, hesmooth⟩ :=
    exists_scalarCandidateOperators_jointSmoothTameOn hD hT hS v₀
  obtain ⟨bl, ll, εl, hεl, hlbound⟩ :=
    uniform_linearFamily_bound_of_jointGerm (scalarCandidateLinear hD hT hS)
      (scalarCandidateLinear_jointUniformTameGerm hD hT hS v₀)
  obtain ⟨be, le, εe, hεe, hebound⟩ :=
    uniform_bilinearFamily_bound_of_jointGerm (scalarCandidateError hD hT hS)
      (scalarCandidateError_jointUniformTameGerm hD hT hS v₀)
  let Ug := scalarStateBall S v₀ 4 εg
  let Ul := scalarStateBall S v₀ bl εl
  let Ue := scalarStateBall S v₀ be εe
  let P : Set (ScalarWeightedState S) := {x | ScalarCandidatePowerBounds hD hT hS x}
  have hng : Ug ∈ 𝓝 (scalarStateCenter S v₀) :=
    (isOpen_scalarStateBall S v₀ 4 εg).mem_nhds (scalarStateCenter_mem_ball S v₀ 4 hεg)
  have hnl : Ul ∈ 𝓝 (scalarStateCenter S v₀) :=
    (isOpen_scalarStateBall S v₀ bl εl).mem_nhds (scalarStateCenter_mem_ball S v₀ bl hεl)
  have hne : Ue ∈ 𝓝 (scalarStateCenter S v₀) :=
    (isOpen_scalarStateBall S v₀ be εe).mem_nhds (scalarStateCenter_mem_ball S v₀ be hεe)
  have hnp : P ∈ 𝓝 (scalarStateCenter S v₀) :=
    eventually_scalarCandidatePowerBounds hD hT hS v₀
  have hn : V ∩ (Ug ∩ (P ∩ (Ul ∩ Ue))) ∈ 𝓝 (scalarStateCenter S v₀) :=
    inter_mem (hV.mem_nhds hxV) (inter_mem hng (inter_mem hnp (inter_mem hnl hne)))
  obtain ⟨base, loss, ε, hbase, hloss, hε, hε1, hsub, hjets, hresidual, hcoefficients⟩ :=
    exists_scalarStateBall_realizations S v₀
      (scalarCandidateJets_uniformTameGerm hD hT hS v₀)
      (scalarCandidateResidual_uniformTameGerm hD hT hS v₀)
      (scalarCandidateCoefficients_uniformTameGerm hD hT hS v₀)
      hn (max 4 (max bl be)) (max ll le)
  let W : WeightedScalarData S :=
    { base := base
      loss := loss
      epsilon := ε
      jets := scalarCandidateJets hD hT hS
      residual := scalarCandidateResidual hD hT hS
      coefficients := scalarCandidateCoefficients hD hT hS
      linear := scalarCandidateLinear hD hT hS
      error := scalarCandidateError hD hT hS }
  let U := scalarStateBall S v₀ base ε
  have hU : IsOpen U := isOpen_scalarStateBall S v₀ base ε
  have hgeom : ∀ x ∈ U, ScalarStateGeometry D S x :=
    fun x hx => hgeometry x (hsub hx).2.1
  have hpower : ∀ x ∈ U, ScalarCandidatePowerBounds hD hT hS x :=
    fun _ hx => (hsub hx).2.2.1
  have hbase4 : 4 ≤ W.base := by change 4 ≤ base; omega
  have hbl : bl ≤ base := by omega
  have hbe : be ≤ base := by omega
  have hll : ll ≤ loss := by omega
  have hle : le ≤ loss := by omega
  have h03 : IsWeightedS03 D S v₀ W := by
    refine ⟨hε, hε1, hU, scalarStateCenter_mem_ball S v₀ base hε, hgeom, ?_, hjets⟩
    intro x hx i p
    exact decode_scalarCandidateJets hD hT hS x (hpower x hx) i p
  have h04 : IsWeightedS04 D S v₀ W :=
    weightedScalar_S04_of_residual hD hT hS v₀ W hgeom
      (fun x hx p => decode_scalarCandidateResidual hD hT hS x (hpower x hx) p)
      hresidual
  refine ⟨W, h03, h04, ?_⟩
  apply weightedScalar_S05_of_operators hD hT hS v₀ W hbase4 h03 h04
  · intro x hx i p
    exact decode_scalarCandidateCoefficients hD hT hS x (hpower x hx) (hgeom x hx) i p
  · exact hcoefficients
  · intro x hx u p
    exact decode_scalarCandidateLinear hD hT hS x (hpower x hx) (hgeom x hx) u p
  · intro x hx R u p
    exact decode_scalarCandidateError hD hT hS x (hpower x hx) (hgeom x hx) R u p
  · exact smoothTameOn_mono hlsmooth (hU.prod isOpen_univ)
      (prod_mono (fun _ hx => (hsub hx).1) (subset_refl univ))
  · exact smoothTameOn_mono hesmooth ((hU.prod isOpen_univ).prod isOpen_univ)
      (prod_mono (prod_mono (fun _ hx => (hsub hx).1) (subset_refl univ))
        (subset_refl univ))
  · intro s hs
    obtain ⟨C, hC, hCs⟩ := hlbound s (hbl.trans hs)
    refine ⟨C, hC, ?_⟩
    intro x hx u
    exact (hCs x (hsub hx).2.2.2.1 u).trans
      (mul_le_mul_of_nonneg_left (weightedLinearFamilyCost_mono hp hpc hbl hll x u) hC)
  · intro s hs
    obtain ⟨C, hC, hCs⟩ := hebound s (hbe.trans hs)
    refine ⟨C, hC, ?_⟩
    intro x hx R u
    exact (hCs x (hsub hx).2.2.2.2 R u).trans
      (mul_le_mul_of_nonneg_left (weightedErrorFamilyCost_mono hp hph hpc hbe hle x R u) hC)

/-- All three frozen weighted scalar milestones, with a common actual
witness for the finite jet, residual, coefficient and operator interfaces. -/
theorem scalarWeighted :
    S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement :=
  scalarWeighted_of_S05 scalarWeightedS05

end ContinuousFlexibility.Statements
