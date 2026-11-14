module

public import ContinuousFlexibility.Scalar.WeightedCandidateOperatorAnalysis
public import ContinuousFlexibility.Scalar.WeightedCommonBall
public import ContinuousFlexibility.Scalar.WeightedHomogeneousFamilies
public import ContinuousFlexibility.Scalar.WeightedOperatorBounds
public import ContinuousFlexibility.Scalar.WeightedWitnessProperties
public import ContinuousFlexibility.Scalar.WeightedGeometry

/-!
# The actual weighted scalar witness

All finite realizations and both operator families are assembled here.
The base and loss dominate the previously fixed orders, and a single state
ball lies inside the geometric, scalar-composition, and operator domains.
Every clause uses those same maps and that same ball.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- Restriction and order enlargement use only the numerical family estimate. -/
private theorem linearFamily_bound_restrict_weaken
    {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {U V : Set X} {base base' loss loss' : ℕ} {value : ℕ → X → Y → ℝ}
    (hp : Monotone p) (hq : Monotone q)
    (hbase : base ≤ base') (hloss : loss ≤ loss') (hsub : U ⊆ V)
    (hbound : ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ V, ∀ u, value s x u ≤ C *
        (q (s + loss) u + (1 + p (s + loss) x) * q base u)) :
    ∀ s : ℕ, base' ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ u, value s x u ≤ C *
        (q (s + loss') u + (1 + p (s + loss') x) * q base' u) := by
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hbound s (hbase.trans hs)
  refine ⟨C, hC, ?_⟩
  intro x hx u
  have hcost := weightedLinearFamilyCost_mono
    (p := p) (q := q) (base := base) (base' := base')
    (loss := loss) (loss' := loss') (s := s) hp hq hbase hloss x u
  exact le_trans (hCs x (hsub hx) u) (mul_le_mul_of_nonneg_left hcost hC)

private theorem bilinearFamily_bound_restrict_weaken
    {X Y Z : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {U V : Set X} {base base' loss loss' : ℕ} {value : ℕ → X → Y → Z → ℝ}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r)
    (hbase : base ≤ base') (hloss : loss ≤ loss') (hsub : U ⊆ V)
    (hbound : ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ V, ∀ R u, value s x R u ≤ C *
        (q (s + loss) R * r base u + q base R * r (s + loss) u +
          (1 + p (s + loss) x) * q base R * r base u)) :
    ∀ s : ℕ, base' ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U, ∀ R u, value s x R u ≤ C *
        (q (s + loss') R * r base' u + q base' R * r (s + loss') u +
          (1 + p (s + loss') x) * q base' R * r base' u) := by
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hbound s (hbase.trans hs)
  refine ⟨C, hC, ?_⟩
  intro x hx R u
  have hcost := weightedErrorFamilyCost_mono
    (p := p) (q := q) (r := r) (base := base) (base' := base')
    (loss := loss) (loss' := loss') (s := s) hp hq hr hbase hloss x R u
  exact le_trans (hCs x (hsub hx) R u) (mul_le_mul_of_nonneg_left hcost hC)

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
  · exact linearFamily_bound_restrict_weaken
      (p := scalarStateGrading S) (q := scalarCommonHeightGrading S)
      (value := fun s x u => scalarHeightGrading S s (W.linear x u))
      (U := U) (V := Ul) (base := bl) (base' := base) (loss := ll) (loss' := loss)
      hp hpc hbl hll (fun _ hx => (hsub hx).2.2.2.1) hlbound
  · exact bilinearFamily_bound_restrict_weaken
      (p := scalarStateGrading S) (q := scalarHeightGrading S)
      (r := scalarCommonHeightGrading S)
      (value := fun s x R u => scalarHeightGrading S s (W.error x R u))
      (U := U) (V := Ue) (base := be) (base' := base) (loss := le) (loss' := loss)
      hp hph hpc hbe hle (fun _ hx => (hsub hx).2.2.2.2) hebound

/-- All three frozen weighted scalar milestones, with a common actual
witness for the finite jet, residual, coefficient and operator interfaces. -/
theorem scalarWeighted :
    S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement :=
  scalarWeighted_of_S05 scalarWeightedS05

end ContinuousFlexibility.Statements
