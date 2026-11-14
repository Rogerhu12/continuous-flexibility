module

public import ContinuousFlexibility.Analysis.N04bNegativeProfile

/-!
# The actual characteristic gap on every negative interior

The profile sign is derived from N01's actual flow tower. The exact
determinant identity then gives strict hyperbolicity of the original
type-corrected operator throughout each negative component, including
the region outside any optical correction collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_original_negative_hyperbolic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    0 < (originalCoefficients D S C z).a p ∧
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨_, hbounds⟩ := hN.1.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hp.1, hp.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have hr : 0 < p.1 := hbounds.1.1.trans hpD.1.1
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hbounds.1.2.2.2.2.1 p.1 hpD.1) (Real.exp_pos _)
  have hgeo := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hpD
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hw).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hgeo.2.2.1)
  have hDisc : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hgeo.2.2.2.2.1
  have ha : 0 < (originalCoefficients D S C z).a p :=
    mul_pos hQ (inverseDThreeHalves_pos _ hDisc)
  have hz0 : (z.1, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    ⟨hz.1, by simpa only [abs_zero] using hN.2.1⟩
  have hnegative := n04b_stateProfile_deriv_neg hN hS hT hz0 m hp
  have hdet := (polar_corrected_determinant_neg_iff (stateHeight D S C z)
    ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) p.1)
    hr hw hDisc hQ.ne').mpr hnegative
  refine ⟨ha, ?_⟩
  change 0 < polarLinearB (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 -
    polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p *
      polarCorrectedC (stateProfile D S C z.1) (stateHeight D S C z) p
  linarith only [hdet]

theorem n04b_original_negative_halfGap_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    0 < Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) /
        (originalCoefficients D S C z).a p := by
  obtain ⟨ha, hd⟩ := n04b_original_negative_hyperbolic hN hS hT hz hs m hp
  exact div_pos (Real.sqrt_pos.mpr hd) ha

end ContinuousFlexibility.Statements
