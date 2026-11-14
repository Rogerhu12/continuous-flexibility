module

public import ContinuousFlexibility.Analysis.N08ScalarProfileGerms
public import ContinuousFlexibility.Analysis.N08ScalarHeightParameter
public import ContinuousFlexibility.Analysis.N08SourceProjection

/-!
# The weaker-weight scalar formula realizes the actual N08 field

An actual encoded profile perturbation identifies the finite-jet formula
with the frozen scalar residual on the original N01 neighborhood. The
discriminant bounds in N01 supply exactly the range needed by the scalar
power extension. Conservation then identifies the globally projected
source with this same field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {γ : ℝ}

theorem n08_profile_deriv_from_decode (hD : IsAccumulatingProfile D)
    (hS : IsPhysicalSpaces D T S) (m : (S.height γ).Space) (w : ℝ → ℝ)
    (hm : ∀ p ∈ annularOpen D,
      D.w p.1 * (1 + (S.height γ).decode m p) = w p.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    deriv D.w p.1 * (1 + (S.height γ).decode m p) +
      D.w p.1 * radialPartial ((S.height γ).decode m) p = deriv w p.1 := by
  obtain ⟨B, hB⟩ := hD
  have hDw := ((hB.1.2.2.1.1).differentiable (by simp) p.1).hasDerivAt
  have hmp := ((hS.1 γ).2.2.2.1 m).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  have hmd := Radial.hasDerivAt_radialSlice (hmp.differentiableAt (by simp))
  have hprod := hDw.mul ((hasDerivAt_const p.1 (1 : ℝ)).add hmd)
  have heq : w =ᶠ[𝓝 p.1]
      (fun r => D.w r * (1 + (S.height γ).decode m (r, p.2))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with r hr
    exact (hm (r, p.2) ⟨hr, mem_univ _⟩).symm
  simpa only [Pi.add_apply, zero_add] using (hprod.congr_of_eventuallyEq heq).deriv.symm

variable {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem n08_discriminant_substitute
    {a w q t : ℝ} {u v : PolarPoint → ℝ} (p : PolarPoint)
    (hu : u = v) (hq : q = t)
    (h : a = (1 + w ^ 2) * (1 - (q * heightAngular u p) ^ 2) -
      (w + q * radialPartial u p) ^ 2) :
    a = (1 + w ^ 2) * (1 - (t * heightAngular v p) ^ 2) -
      (w + t * radialPartial v p) ^ 2 := by
  subst v t
  exact h

private theorem n08_scalarFormula_substitute
    {a q t : ℝ} {w : ℝ → ℝ} {u v : PolarPoint → ℝ} (p : PolarPoint)
    (hu : u = v) (hq : q = t) (h : a = n08ScalarFiniteFormula w u q p) :
    a = n08ScalarFiniteFormula w v t p := by
  subst v t
  exact h

theorem n08ProfileDiscriminant_state_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hγ : 0 ≤ γ)
    (m : (S.height γ).Space) (z : AnnularState S × ℝ)
    (hm : ∀ p ∈ annularOpen D,
      D.w p.1 * (1 + (S.height γ).decode m p) = stateProfile D S C z.1 p.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    1 + (S.height scalarBeta).decode
      (n08ProfileDiscriminant hN.1.1 hT hS hγ m (n08ScalarHeightParameter S z)) p =
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hcalc := n08ProfileDiscriminant_decode hN.1.1 hT hS hγ m
    (n08ScalarHeightParameter S z) p (hm p hp)
  have hq : (n08ScalarHeightParameter S z).2 = z.2 := rfl
  have hfinite := n08_discriminant_substitute p
    (n08ScalarHeightParameter_increment S z) hq hcalc
  exact hfinite.trans (n08_polarDiscriminant_radialFamily
    (n08_stateRadialHeight_contDiff hT hS hN z.1)
    (n08_stateRadialHeight_hasDerivAt hT hS hN z.1)
    (n08_stateU_contDiff hT hS z.1) z.2 p).symm

theorem n08ProfileDiscriminant_small_on_stateNeighborhood
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hγ : 0 ≤ γ)
    (m : (S.height γ).Space) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : ∀ p ∈ annularOpen D,
      D.w p.1 * (1 + (S.height γ).decode m p) = stateProfile D S C z.1 p.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    |(S.height scalarBeta).decode
      (n08ProfileDiscriminant hN.1.1 hT hS hγ m (n08ScalarHeightParameter S z)) p| ≤ 1 / 2 := by
  have hd := n08ProfileDiscriminant_state_decode hT hS hN hγ m z hm p hp
  obtain ⟨_, _, _, _, _, _, _, _, _, hpositive, _⟩ := hN
  have hb := (hpositive z hz hs p hp).2.2.2.2
  apply abs_le.mpr
  constructor <;> linarith [hb.1, hb.2]

theorem n08ProfileResidual_state_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hγ : 0 ≤ γ)
    (m : (S.height γ).Space) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : ∀ p ∈ annularOpen D,
      D.w p.1 * (1 + (S.height γ).decode m p) = stateProfile D S C z.1 p.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height scalarBeta).decode
      (n08ProfileResidual hN.1.1 hT hS hγ m (n08ScalarHeightParameter S z)) p =
        scalarResidualField D S C z p := by
  have hcalc := n08ProfileResidual_decode hN.1.1 hT hS hγ m (n08ScalarHeightParameter S z) p
    (stateProfile D S C z.1) (hm p hp)
    (n08_profile_deriv_from_decode hN.1.1 hS m (stateProfile D S C z.1) hm p hp)
    (n08ProfileDiscriminant_small_on_stateNeighborhood hT hS hN hγ m hz hs hm p hp)
  have hfinite := n08_scalarFormula_substitute p
    (n08ScalarHeightParameter_increment S z)
    (show (n08ScalarHeightParameter S z).2 = z.2 from rfl) hcalc
  have hr : p.1 ≠ 0 := by
    obtain ⟨B, hB⟩ := hN.1.1
    exact (hB.1.1.trans hp.1.1).ne'
  exact hfinite.trans (n08_scalarResidualField_eq_finiteFormula hT hS hN z hr).symm

def n08ScalarSourceResidual
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hγ : 0 ≤ γ)
    (m : AnnularState S → (S.height γ).Space) (z : AnnularState S × ℝ) : S.Source :=
  n08SourceProjection hS
    (n08ProfileResidual hN.1.1 hT hS hγ (m z.1) (n08ScalarHeightParameter S z))

theorem n08ScalarSourceResidual_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hγ : 0 ≤ γ)
    (m : AnnularState S → (S.height γ).Space)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hm : ∀ p ∈ annularOpen D,
      D.w p.1 * (1 + (S.height γ).decode (m z.1) p) = stateProfile D S C z.1 p.1)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n08ScalarSourceResidual hT hS hN hγ m z).val p =
      scalarResidualField D S C z p :=
  n08SourceProjection_decode_scalarResidual hT hS hN hz hs _
    (n08ProfileResidual_state_decode hT hS hN hγ (m z.1) hz hs hm) p hp

theorem n08ScalarSourceResidual_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hγ : 0 ≤ γ)
    (m : AnnularState S → (S.height γ).Space)
    (hm : UniformTameGerm (pairGrading (stateGrading S) realGrading)
      (S.height γ).grading (C.referenceState, 0) (fun z => m z.1)) :
    UniformTameGerm (pairGrading (stateGrading S) realGrading) S.sourceGrading
      (C.referenceState, 0) (n08ScalarSourceResidual hT hS hN hγ m) := by
  have hp := tamePairGrading_monotone (solve_stateGrading_monotone S)
    weighted_realGrading_monotone
  have ht := withSeminorms_pairGrading (solve_stateGrading_withSeminorms S)
    weighted_realGrading_withSeminorms
  exact n08SourceProjection_postcompose_uniformTameGerm hS hp ht
    (hm.n08ProfileResidual (n08ScalarHeightParameter_uniformTameGerm S (C.referenceState, 0))
      rfl hN.1.1 hT hS hγ hp ht)

end ContinuousFlexibility.Statements
