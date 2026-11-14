module

public import ContinuousFlexibility.Analysis.N01cCoefficientMixedParameterJets
public import ContinuousFlexibility.Analysis.N01cParametricEndpointDivision
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Joint physical smoothness on actual finite affine state planes

Pointwise continuous-linear evaluation and spatial smoothness of each
state input give a finite coordinate expansion on every affine plane.
This proves joint finite-dimensional smoothness without placing a norm
on the original state space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem contDiffOn_finiteAffine_linearField
    {E X : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : Set X} (F : E → X → ℝ)
    (eval : ∀ p ∈ V, E →L[ℝ] ℝ)
    (heval : ∀ p hp x, eval p hp x = F x p)
    (hF : ∀ x : E, ContDiffOn ℝ ∞ (F x) V)
    {m : ℕ} (x : E) (L : (Fin m → ℝ) →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × X => F (x + L p.1) p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ V) := by
  classical
  let e : Fin m → E := fun i => L (Pi.single i 1)
  have hexp (q : Fin m → ℝ) (p : X) (hp : p ∈ V) :
      F (x + L q) p = F x p + ∑ i : Fin m, q i * F (e i) p := by
    have hL : L q = ∑ i : Fin m, q i • e i := by
      have hh := congrArg L (pi_eq_sum_univ' q)
      simpa only [map_sum, map_smul, e] using hh
    rw [← heval p hp (x + L q), map_add, hL]
    simp only [map_sum, map_smul, smul_eq_mul]
    simp only [heval]
  have hbase : ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × X => F x p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ V) :=
    (hF x).comp contDiff_snd.contDiffOn (fun p hp => hp.2)
  have hsum : ContDiffOn ℝ ∞
      (fun p : (Fin m → ℝ) × X => ∑ i : Fin m, p.1 i * F (e i) p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ V) := by
    apply ContDiffOn.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffOn.mul
      ((hF (e i)).comp contDiff_snd.contDiffOn (fun p hp => hp.2))
  exact (hbase.add hsum).congr (fun p hp => hexp p.1 p.2 hp.2)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem contDiffOn_stateProfileExponent_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) {m : ℕ} (x : AnnularState S)
    (L : (Fin m → ℝ) →L[ℝ] AnnularState S) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × ℝ =>
      (x + L p.1).2.1 * D.chi p.2 + stateControlSum C (x + L p.1) p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ Ioo D.a D.b) := by
  exact contDiffOn_finiteAffine_linearField
    (fun y r => y.2.1 * D.chi r + stateControlSum C y r)
    (stateProfileExponentCLM hS hT hA.1.1 hA.2.2.1)
    (stateProfileExponentCLM_apply hS hT hA.1.1 hA.2.2.1)
    (fun y => (contDiff_const.mul hA.1.2.2.2.1.1).contDiffOn.add
      (contDiffOn_stateControlSum hA.2.2.1 y)) x L

theorem contDiffOn_stateProfile_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) {m : ℕ} (x : AnnularState S)
    (L : (Fin m → ℝ) →L[ℝ] AnnularState S) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × ℝ =>
      stateProfile D S C (x + L p.1) p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ Ioo D.a D.b) := by
  have hw := hA.1.1.choose_spec.1.2.2.1.1
  exact (hw.comp contDiff_snd).contDiffOn.mul
    (contDiffOn_stateProfileExponent_finiteAffine hS hT hA x L).exp

theorem contDiffOn_stateUPolarInput_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hD : 0 < D.a)
    {m : ℕ} (x : AnnularState S) (L : (Fin m → ℝ) →L[ℝ] AnnularState S)
    (i : Fin 5) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      stateUPolarInput S i (x + L p.1) p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ annularOpen D) := by
  exact contDiffOn_finiteAffine_linearField (fun y => stateUPolarInput S i y)
    (fun p hp => stateUPolarInputCLM hT hS p hp i)
    (fun p hp y => stateUPolarInputCLM_apply hT hS p hp (hD.trans hp.1.1).ne' i y)
    (fun y => contDiffOn_stateUPolarInput hT hS hD y i) x L

end ContinuousFlexibility.Statements
