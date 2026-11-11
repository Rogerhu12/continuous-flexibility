import ContinuousFlexibility.Analysis.SolveApplication
import ContinuousFlexibility.Analysis.SolveNormalization
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.SolveResidualSpaces
import ContinuousFlexibility.Analysis.SolveReturnEquations
import ContinuousFlexibility.Analysis.SolveTameSubspace

/-!
# Applying the quadratic-error iteration to the coupled annular system

The iteration runs on the closed kernel of the actual normalization row
inside the physical sector. No normalization condition is discarded, and
all data are the same data supplied by N10. The parameter cylinder is
shrunk once to the smaller of the two existing positive radii.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem solve_coupled_exists_normalized_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {P : ResidualData S} {B : ControlColumnData S} {N : ControlInverseData S}
    {V : CoupledInverseData S} {Q : QuadraticErrorData S}
    {base loss : ℕ} {ε q0 : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    (h10 : N10Properties D S C R L P B V Q base ε q0) :
    ∃ x : AnnularState S, ∃ τ : ℝ, τ ≠ 0 ∧
      (x, τ) ∈ stateNeighborhood S C base ε ∧ stateSector S x ∧
      referenceRow D (stateU S x) = 1 ∧ jointResidual S P (x, τ) = 0 := by
  classical
  have h8' := h8
  rcases h8' with ⟨hclosed, _, _, _, hzero, _, _, _, _, _, _, _, _, _, _, _, _, hRTame, _⟩
  have h9' := h9
  rcases h9' with ⟨hq0, hqε, _, _, _, hVident, hVTame⟩
  have h10' := h10
  rcases h10' with ⟨_, _, _, _, hRight, hQTame⟩
  have href := h1.2.2.1
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.1 (3 / 4 : ℝ)).2.1 n).completeSpace_coe
  letI : ∀ n, CompleteSpace ((S.circle (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.2.1 (3 / 4 : ℝ)).2.1 n).completeSpace_coe
  letI : CompleteSpace (StateDirections S) := hclosed.completeSpace_coe
  let row : StateDirections S →L[ℝ] ℝ := sectorReferenceRowCLM h1.1 hT hS
  let W : Submodule ℝ (StateDirections S) := row.toLinearMap.ker
  letI : CompleteSpace W := row.isClosed_ker.completeSpace_coe
  let p : ℕ → Seminorm ℝ W := fun n => (sectorGrading S n).comp W.subtype
  have hp : Monotone p := fun _ _ h x => solve_sectorGrading_monotone S h x.val
  have hwp : WithSeminorms p :=
    (Topology.IsInducing.subtypeVal).withSeminorms (f := W.subtype)
      (solve_sectorGrading_withSeminorms S)
  let ψ : StateDirections S := ⟨C.referenceState, href.stateSector⟩
  have hψ : referenceRow D (stateU S ψ.val) = 1 := href.2.2.2.2.2
  have hψrow : row ψ = 1 := (sectorReferenceRowCLM_apply h1.1 hT hS ψ).trans hψ
  have hSX : HasSmoothing p := hasSmoothing_ker_of_continuous (sectorGrading S)
    (solve_sectorGrading_withSeminorms S) (solve_sectorGrading_monotone S)
    (solve_sector_hasSmoothing hS) row ψ hψrow
  let ρ : ℝ := min ε q0
  have hρ : 0 < ρ := lt_min h1.2.1 hq0
  let U : Set (W × ℝ) := {z | p base z.1 < ρ ∧ |z.2| < ρ}
  let a := pairGrading p realGrading
  let Lz : (W × ℝ) →L[ℝ] (StateDirections S × ℝ) :=
    W.subtypeL.prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hUopen : IsOpen U :=
    (isOpen_lt ((hwp.continuous_seminorm base).comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have hnear (z : W × ℝ) (hz : z ∈ U) :
      Lz z ∈ sectorNeighborhood S base ε q0 :=
    ⟨hz.1.trans_le (min_le_left _ _), hz.2.trans_le (min_le_right _ _)⟩
  have hnearε (z : W × ℝ) (hz : z ∈ U) :
      Lz z ∈ sectorNeighborhood S base ε ε :=
    ⟨(hnear z hz).1, (hnear z hz).2.trans_le hqε⟩
  have hactual (z : W × ℝ) (hz : z ∈ U) :
      liftSectorParameter S C (Lz z) ∈ coupledNeighborhood S C base ε q0 := by
    constructor
    · simpa only [liftSectorParameter, add_sub_cancel_left, sectorGrading,
        Seminorm.comp_apply, Submodule.subtype_apply] using (hnear z hz).1
    · exact (hnear z hz).2
  have hVmem (z : W × ℝ) (hz : z ∈ U) (y : ResidualSpace S) :
      V.sectorV (Lz z) y ∈ W := by
    apply LinearMap.mem_ker.mpr
    change sectorReferenceRowCLM h1.1 hT hS (V.sectorV (Lz z) y) = 0
    rw [sectorReferenceRowCLM_apply]
    rw [hVident (Lz z) (hnear z hz) y]
    exact h9.referenceRow_coupledInverse_zero hG (hactual z hz)
      (href.liftSectorParameter_sector (Lz z)) y
  let RN : W × ℝ → ResidualSpace S := fun z => sectorJointResidual S C P (Lz z)
  let VN : W × ℝ → ResidualSpace S →ₗ[ℝ] W := fun z =>
    if hz : z ∈ U then (V.sectorV (Lz z)).codRestrict W (hVmem z hz) else 0
  let QN : W × ℝ → ResidualSpace S →ₗ[ℝ] ResidualSpace S →ₗ[ℝ] ResidualSpace S :=
    fun z => Q.Q (liftSectorParameter S C (Lz z))
  have hVN (z : W × ℝ) (hz : z ∈ U) (y : ResidualSpace S) :
      (VN z y).val = V.sectorV (Lz z) y := by
    simp only [VN, dif_pos hz, LinearMap.codRestrict_apply]
  have hLz : ∀ n z, pairGrading (sectorGrading S) realGrading n (Lz z) ≤
      1 * a n z := by intro n z; rw [one_mul]; exact le_rfl
  have hRN : SmoothTameOn a (residualGrading S) U RN := by
    have h := solve_smoothTameOn_precomp hRTame Lz le_rfl hLz
    exact smoothTameOn_mono h hUopen (fun z hz => hnearε z hz)
  let Lv : ((W × ℝ) × ResidualSpace S) →L[ℝ]
      ((StateDirections S × ℝ) × ResidualSpace S) :=
    Lz.prodMap (ContinuousLinearMap.id ℝ (ResidualSpace S))
  have hLv : ∀ n z,
      pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S) n (Lv z) ≤
        1 * pairGrading a (residualGrading S) n z := by
    intro n z
    rw [one_mul]
    exact le_rfl
  have hVpre : SmoothTameOn (pairGrading a (residualGrading S)) (sectorGrading S)
      (U ×ˢ univ) (fun z : (W × ℝ) × ResidualSpace S => V.sectorV (Lz z.1) z.2) := by
    have h := solve_smoothTameOn_precomp hVTame Lv le_rfl hLv
    exact smoothTameOn_mono h (hUopen.prod isOpen_univ)
      (fun z hz => ⟨hnear z.1 hz.1, mem_univ _⟩)
  have hVN_tame : SmoothTameOn (pairGrading a (residualGrading S)) p
      (U ×ˢ univ) (fun z : (W × ℝ) × ResidualSpace S => VN z.1 z.2) :=
    solve_smoothTameOn_codRestrict W row.isClosed_ker hVpre
      (fun z => VN z.1 z.2) (fun z hz => hVN z.1 hz.1 z.2)
  let Lq : (((W × ℝ) × ResidualSpace S) × ResidualSpace S) →L[ℝ]
      (((StateDirections S × ℝ) × ResidualSpace S) × ResidualSpace S) :=
    Lv.prodMap (ContinuousLinearMap.id ℝ (ResidualSpace S))
  have hLq : ∀ n z,
      pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading) (residualGrading S))
        (residualGrading S) n (Lq z) ≤
      1 * pairGrading (pairGrading a (residualGrading S)) (residualGrading S) n z := by
    intro n z
    rw [one_mul]
    exact le_rfl
  have hQN : SmoothTameOn (pairGrading (pairGrading a (residualGrading S)) (residualGrading S))
      (residualGrading S) ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((W × ℝ) × ResidualSpace S) × ResidualSpace S => QN z.1.1 z.1.2 z.2) := by
    have h := solve_smoothTameOn_precomp hQTame Lq le_rfl hLq
    exact smoothTameOn_mono h ((hUopen.prod isOpen_univ).prod isOpen_univ)
      (fun z hz => ⟨⟨hnear z.1.1 hz.1.1, mem_univ _⟩, mem_univ _⟩)
  have hzeroN : RN (0, 0) = 0 := by
    simpa only [RN, Lz, ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.id_apply,
      Submodule.subtypeL_apply, ZeroMemClass.coe_zero, sectorJointResidual,
      liftSectorParameter, add_zero] using hzero
  have hRightN : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => RN (x, z.2))
      (y + QN z (RN z) y) z.1 (VN z y) := by
    intro z hz y
    have h := hRight (Lz z) (hnear z hz) y
    rw [← hVN z hz y] at h
    exact HasProjectiveLineDerivAt.comp_linear W.subtype (x := z.1) (v := VN z y) h
  obtain ⟨x, τ, hτ, hmem, hz⟩ := solve_exists_nonzero_zero p (residualGrading S)
    hp hwp (solveResidualEquiv hS) (solveResidualEquiv_grading_le hS)
    (solve_residualGrading_le_two hS) base ρ hρ RN VN QN hzeroN
    hSX (solve_residual_hasSmoothing hS) hRN hVN_tame hQN hRightN
  refine ⟨C.referenceState + x.val.val, τ, hτ, ?_, ?_, ?_, hz⟩
  · exact liftSectorParameter_mem_stateNeighborhood (hnear (x, τ) hmem) hqε
  · exact href.liftSectorParameter_sector (Lz (x, τ))
  · exact referenceRow_affine_of_mem_kernel h1.1 hT hS href x.val
      (LinearMap.mem_ker.mp x.property)

end ContinuousFlexibility.Analysis
