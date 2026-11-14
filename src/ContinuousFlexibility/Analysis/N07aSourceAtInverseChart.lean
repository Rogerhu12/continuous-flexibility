module

public import ContinuousFlexibility.Analysis.N07aActualMaterialComparison
public import ContinuousFlexibility.Analysis.N07aSourceFrechetDecay
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Actual source jets at the true inverse-chart points

The derived current-domain material certificate compares the actual
inverse-chart point with the sampled weights. Its powers remain a single
subpower envelope at each order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε γ : ℝ} {A : SobolevModelData}

theorem n07a_source_jets_at_inverseChart
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hA : IsSobolevModel D T γ A) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε) (n c : ℕ) :
    ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ (u : A.Space) m y,
        y ∈ canonicalOpen S K m →
          ‖iteratedFDeriv ℝ n (A.decode u)
            (K.inverseChart (liftSectorParameter S C z) m y)‖ ≤
            e m * (T.H (T.sample (K.cell m)) ^ γ *
              (T.M (T.sample (K.cell m)) ^ c)⁻¹) * A.grading (c + n + 3) u := by
  let e : ℕ → ℝ := hRatio.choose
  have he := hRatio.choose_spec.1
  have he1 := hRatio.choose_spec.2.1
  have heb := hRatio.choose_spec.2.2
  have hDecay := n07a_iteratedFDeriv_decode_decay hT hA n c
  let C₀ : ℝ := hDecay.choose
  have hC₀ := hDecay.choose_spec.1
  have hCb := hDecay.choose_spec.2
  refine ⟨fun m => C₀ * e m ^ (c + 1),
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT C₀)
      (he.nat_pow hD hT (c + 1)),
    fun m => mul_nonneg hC₀ (pow_nonneg (zero_le_one.trans (he1 m)) _), ?_⟩
  intro z hz u m y hy
  let x := K.inverseChart (liftSectorParameter S C z) m y
  have hz' := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl
  have hs := hrefState.liftSectorParameter_sector z
  have hx : x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m :=
    (h04.1.charts _ hz' hs m).2.1 hy
  have hx' : x ∈ annularOpen D := (h04.1.domains _ hz' hs m).2.2.1 hx
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hpos := hT.2.1 x.1 hx'.1
  have hsample := hT.2.1 _ hm
  have hratio := heb z hz m x hx
  have hweight := n07a_material_piece_decay_compare hpos.2.1 hsample.2.1
    (zero_lt_one.trans_le hpos.2.2.2) (zero_lt_one.trans_le hsample.2.2.2)
    (he1 m) hratio.1 hratio.2.2.2 hγ hγ1 c
  have hbound := hCb u x hx'
  calc
    _ ≤ C₀ * T.H x.1 ^ γ * (T.M x.1 ^ c)⁻¹ * A.grading (n + c + 3) u := hbound
    _ = C₀ * (T.H x.1 ^ γ * (T.M x.1 ^ c)⁻¹) * A.grading (n + c + 3) u := by ring
    _ ≤ C₀ * (e m ^ (c + 1) * T.H (T.sample (K.cell m)) ^ γ *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹) * A.grading (n + c + 3) u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC₀)
        (apply_nonneg _ _)
    _ = _ := by rw [Nat.add_comm n c]; ring

end ContinuousFlexibility.Analysis
