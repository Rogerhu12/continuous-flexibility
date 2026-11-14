module

public import ContinuousFlexibility.Analysis.CanonicalFixedGeometryDifferenceJets

/-!
# Ordinary regularity of the actual static geometric and material atoms

The physical unit point is affine and stays in the material core. The
actual positive smooth material functions therefore give smooth lengths,
scales and ratios, including their inverses. Their angular period follows
from radiality. No quantitative reference-jet bound is assumed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff

theorem canonical_staticAtom_contDiffOn_of_core
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} (hT : IsMaterialData D T)
    (z : AnnularState S × ℝ) (m : ℕ) {a : Atom}
    (ha : CanonicalFixedGeometryAtom a ∨ CanonicalMaterialRatioAtom a)
    (hcore : MapsTo (fun p => (physicalUnitPoint K m p).1) unitStrip (Ioo D.a D.b)) :
    ContDiffOn ℝ ∞ (atom D T S C L K z m a) unitStrip := by
  have hmap : ContDiff ℝ ∞ (fun p => (physicalUnitPoint K m p).1) :=
    contDiff_const.add (contDiff_const.mul contDiff_fst)
  have hweight (f : ℝ → ℝ)
      (hf : f ∈ ({T.ell, T.H, T.E0, T.M, T.rho} : Set (ℝ → ℝ))) :
      ContDiffOn ℝ ∞ (fun p => f (physicalUnitPoint K m p).1) unitStrip :=
    (hT.1 f hf).comp hmap.contDiffOn hcore
  have hEll := hweight T.ell (by simp)
  have hH := hweight T.H (by simp)
  have hM := hweight T.M (by simp)
  have hE := hweight T.E0 (by simp)
  have hpos (p : PolarPoint) (hp : p ∈ unitStrip) := hT.2.1 _ (hcore hp)
  have hEllInv := hEll.fun_inv (fun p hp => (hpos p hp).1.ne')
  have hHInv := hH.fun_inv (fun p hp => (hpos p hp).2.1.ne')
  have hMInv := hM.fun_inv (fun p hp =>
    (zero_lt_one.trans_le (hpos p hp).2.2.2).ne')
  have hEInv := hE.fun_inv (fun p hp => (hpos p hp).2.2.1.ne')
  rcases ha with ha | ha
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact hEll
    · exact hEllInv
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · refine (hH.mul (contDiffOn_const (c := (T.H (T.sample (K.cell m)))⁻¹))).congr ?_
      intro p _
      simp only [atom, div_eq_mul_inv]
    · refine ((contDiffOn_const (c := T.H (T.sample (K.cell m)))).mul hHInv).congr ?_
      intro p _
      simp only [atom, div_eq_mul_inv]
    · refine (hM.mul (contDiffOn_const (c := (T.M (T.sample (K.cell m)))⁻¹))).congr ?_
      intro p _
      simp only [atom, div_eq_mul_inv]
    · refine ((contDiffOn_const (c := T.M (T.sample (K.cell m)))).mul hMInv).congr ?_
      intro p _
      simp only [atom, div_eq_mul_inv]
    · refine (hE.mul (contDiffOn_const (c := (T.E0 (T.sample (K.cell m)))⁻¹))).congr ?_
      intro p _
      simp only [atom, div_eq_mul_inv]
    · refine ((contDiffOn_const (c := T.E0 (T.sample (K.cell m)))).mul hEInv).congr ?_
      intro p _
      simp only [atom, div_eq_mul_inv]

theorem canonical_staticAtom_angle_period
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} (z : AnnularState S × ℝ) (m : ℕ) {a : Atom}
    (ha : CanonicalFixedGeometryAtom a ∨ CanonicalMaterialRatioAtom a) (p : PolarPoint) :
    atom D T S C L K z m a (p + (0, Real.pi)) = atom D T S C L K z m a p := by
  rcases ha with ha | ha <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [atom, physicalUnitPoint, Prod.fst_add, add_zero]

end ContinuousFlexibility.Analysis
