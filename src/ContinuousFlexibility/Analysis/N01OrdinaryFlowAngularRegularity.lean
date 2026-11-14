module

public import ContinuousFlexibility.Analysis.ContinuousTimeAngularFlow
public import ContinuousFlexibility.Analysis.PolarCharacteristicAngularRegularity
public import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeedExtension
public import ContinuousFlexibility.Analysis.N01CoefficientValueJets

/-!
# Genuine angular regularity at the ordinary return endpoints

The frozen N01 profile and denominator inequalities make the original
speed admissible on a fixed open radial neighborhood of each closed
control interval. Its square-root factor is only used continuously in
time. The existing ordinary time equation then implies actual smooth
angular slices and continuity of every angular jet on the closed strip.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual N01 denominator conditions hold on the whole annulus. -/
theorem n01_stateCharacteristic_admissible
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) :
    ∀ p ∈ annularOpen D,
      0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0 := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hD.1.2.2.2.2.1
  intro p hp
  have hlow := hN.2.2.2.2.2.2.2.2.2.1 z hz hsector p hp
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (hwref p.1 hp.1)).trans_le
      ((le_div_iff₀ (hwref p.1 hp.1)).mp hlow.1)
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hw).trans_le
      ((le_div_iff₀ hw).mp hlow.2.2.1)
  exact ⟨(by norm_num : (0 : ℝ) < 1 / 2).trans_le hlow.2.2.2.2.1, hQ.ne'⟩

/-- The derivatives here are the ordinary derivatives of the actual
angular slices, including at each closed radial endpoint. -/
def OrdinaryFlowAngularRegularity
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Prop :=
  (∀ r ∈ Icc (C.left m) (C.right m), ContDiff ℝ ∞ (C.minusFlow z m r)) ∧
    ∀ n : ℕ, ContinuousOn
      (fun p : PolarPoint => iteratedDeriv n (C.minusFlow z m p.1) p.2)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ))

/-- Only the actual frozen N01 hypotheses are inputs. In particular,
endpoint angular smoothness is a consequence of the genuine time flow. -/
theorem n01_ordinaryFlow_angularRegularity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    OrdinaryFlowAngularRegularity S C z m := by
  have hgeometry := hN.2.2.2.1.1 m
  obtain ⟨_, hD⟩ := hN.1.1
  have ha : 0 < D.a := hD.1.1
  obtain ⟨ρ, hρ, hρlt⟩ := exists_between
    (lt_min (sub_pos.mpr hgeometry.1) (sub_pos.mpr hgeometry.2.2))
  have hleft : ρ < C.left m - D.a := hρlt.trans_le (min_le_left _ _)
  have hright : ρ < D.b - C.right m := hρlt.trans_le (min_le_right _ _)
  have hpositive : 0 < C.left m - ρ := by linarith
  have hadm : ∀ p ∈ Ioo (C.left m - ρ) (C.right m + ρ) ×ˢ (univ : Set ℝ),
      0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0 := by
    intro p hp
    apply n01_stateCharacteristic_admissible hN hz hsector p
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hp.1.1, hp.1.2]
  obtain ⟨F, hF, hperiod, heq⟩ :=
    exists_spatiallyRegular_polarMinusCharacteristicSpeed
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z)
      hgeometry.2.1.le hρ hpositive hadm (neighborhood_stateHeight_periodic hS z)
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hresult := continuousTimeCircleFlow_angularSmooth
    (Θ := fun p : PolarPoint => C.minusFlow z m p.2 p.1)
    hgeometry.2.1.le Real.pi_pos hF hperiod
    (fun θ => (hflow z hz m θ).2.1) (fun θ => (hflow z hz m θ).1)
    (fun θ t ht => ((hflow z hz m θ).2.2.1 t ht).congr_deriv
      (heq t (Ioo_subset_Icc_self ht) (C.minusFlow z m t θ)).symm)
  refine ⟨hresult.1, ?_⟩
  intro n
  exact (hresult.2 n).comp (continuousOn_snd.prodMk continuousOn_fst)
    (fun p hp => ⟨mem_univ p.2, hp.1⟩)

end ContinuousFlexibility.Analysis
