module

public import ContinuousFlexibility.Analysis.N06CurrentOperatorPeriodicity
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Reflection of the actual totalized divergence

Angular reflection is a continuous linear equivalence. Its derivative
formula is valid even at points where a function is not differentiable,
so the actual N03 coefficient signs imply reflection covariance without
unrecorded smoothness assumptions on the corrected coefficient fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private def n06PhysicalReflectionCLE : PolarPoint ≃L[ℝ] PolarPoint :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

theorem n06_radialPartial_comp_reflection (f : PolarPoint → ℝ) (p : PolarPoint) :
    radialPartial (fun q : PolarPoint => f (q.1, -q.2)) p =
      radialPartial f (p.1, -p.2) := by
  have hdir : (n06PhysicalReflectionCLE : PolarPoint →L[ℝ] PolarPoint) (1, 0) =
      (1, 0) := by
    ext <;> simp [n06PhysicalReflectionCLE]
  change fderiv ℝ (f ∘ n06PhysicalReflectionCLE) p (1, 0) =
    fderiv ℝ f (n06PhysicalReflectionCLE p) (1, 0)
  rw [n06PhysicalReflectionCLE.comp_right_fderiv, ContinuousLinearMap.comp_apply, hdir]

theorem n06_angularPartial_comp_reflection (f : PolarPoint → ℝ) (p : PolarPoint) :
    angularPartial (fun q : PolarPoint => f (q.1, -q.2)) p =
      -angularPartial f (p.1, -p.2) := by
  have hdir : (n06PhysicalReflectionCLE : PolarPoint →L[ℝ] PolarPoint) (0, 1) =
      -(0, 1) := by
    ext <;> simp [n06PhysicalReflectionCLE]
  change fderiv ℝ (f ∘ n06PhysicalReflectionCLE) p (0, 1) =
    -fderiv ℝ f (n06PhysicalReflectionCLE p) (0, 1)
  rw [n06PhysicalReflectionCLE.comp_right_fderiv, ContinuousLinearMap.comp_apply, hdir,
    map_neg]

theorem n06_radialPartial_of_even {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint, f (p.1, -p.2) = f p) (p : PolarPoint) :
    radialPartial f (p.1, -p.2) = radialPartial f p := by
  have he : (fun q : PolarPoint => f (q.1, -q.2)) = f := funext hf
  have hd := n06_radialPartial_comp_reflection f p
  rw [he] at hd
  exact hd.symm

theorem n06_angularPartial_of_even {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint, f (p.1, -p.2) = f p) (p : PolarPoint) :
    angularPartial f (p.1, -p.2) = -angularPartial f p := by
  have he : (fun q : PolarPoint => f (q.1, -q.2)) = f := funext hf
  have hd := n06_angularPartial_comp_reflection f p
  rw [he] at hd
  simpa only [neg_neg] using (congrArg Neg.neg hd).symm

theorem n06_angularPartial_of_odd {f : PolarPoint → ℝ}
    (hf : ∀ p : PolarPoint, f (p.1, -p.2) = -f p) (p : PolarPoint) :
    angularPartial f (p.1, -p.2) = angularPartial f p := by
  have he : (fun q : PolarPoint => f (q.1, -q.2)) = fun q => -f q := funext hf
  have hd := n06_angularPartial_comp_reflection f p
  rw [he] at hd
  simp only [angularPartial, fderiv_fun_neg, ContinuousLinearMap.neg_apply] at hd
  exact neg_inj.mp hd.symm

/-- This exact reflection law requires no differentiability assumption. -/
theorem n06_divergenceOperator_even
    {A : SymmetricCoefficients} {f : PolarPoint → ℝ}
    (ha : ∀ p : PolarPoint, A.a (p.1, -p.2) = A.a p)
    (hb : ∀ p : PolarPoint, A.b (p.1, -p.2) = -A.b p)
    (hc : ∀ p : PolarPoint, A.c (p.1, -p.2) = A.c p)
    (hf : ∀ p : PolarPoint, f (p.1, -p.2) = f p) (p : PolarPoint) :
    divergenceOperator A f (p.1, -p.2) = divergenceOperator A f p := by
  have hN : ∀ q : PolarPoint,
      A.a (q.1, -q.2) * radialPartial f (q.1, -q.2) +
        A.b (q.1, -q.2) * angularPartial f (q.1, -q.2) =
      A.a q * radialPartial f q + A.b q * angularPartial f q := by
    intro q
    rw [ha q, hb q, n06_radialPartial_of_even hf q, n06_angularPartial_of_even hf q]
    ring
  have hT : ∀ q : PolarPoint,
      A.b (q.1, -q.2) * radialPartial f (q.1, -q.2) +
        A.c (q.1, -q.2) * angularPartial f (q.1, -q.2) =
      -(A.b q * radialPartial f q + A.c q * angularPartial f q) := by
    intro q
    rw [hb q, hc q, n06_radialPartial_of_even hf q, n06_angularPartial_of_even hf q]
    ring
  exact congrArg₂ (fun x y : ℝ => x + y)
    (n06_radialPartial_of_even
      (f := fun q => A.a q * radialPartial f q + A.b q * angularPartial f q) hN p)
    (n06_angularPartial_of_odd
      (f := fun q => A.b q * radialPartial f q + A.c q * angularPartial f q) hT p)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_heightPairField_even (hS : IsPhysicalSpaces D T S)
    (η : HeightPair S) (p : PolarPoint) :
    heightPairField S η (p.1, -p.2) = heightPairField S η p := by
  have he := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1).2.1 p.1 p.2
  simp only [heightPairField, he]

theorem n06_correctedDivergence_heightPair_even
    (hS : IsPhysicalSpaces D T S) (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (η : HeightPair S) (p : PolarPoint) :
    divergenceOperator (L.coefficients z) (heightPairField S η) (p.1, -p.2) =
      divergenceOperator (L.coefficients z) (heightPairField S η) p :=
  n06_divergenceOperator_even
    (fun q => (h03.2.2.2.1 z hz hs q.1 q.2).1)
    (fun q => (h03.2.2.2.1 z hz hs q.1 q.2).2.1)
    (fun q => (h03.2.2.2.1 z hz hs q.1 q.2).2.2)
    (n06_heightPairField_even hS η) p

theorem n06_correctedDivergence_evenOn_strip
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {l r t : ℝ} (hsub : Ioo l r ⊆ radialCore D) (ht : t ∈ Ioo l r)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ univ))
    (hp : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p + (0, Real.pi)) = f p)
    (he : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p.1, -p.2) = f p) (θ : ℝ) :
    divergenceOperator (L.coefficients z) f (t, -θ) =
      divergenceOperator (L.coefficients z) f (t, θ) := by
  obtain ⟨η, hη⟩ := n06_exists_heightPair_strip_germ hT hS hsub ht hf hp he
  exact (n05_divergenceOperator_congr (L.coefficients z) (hη (-θ))).symm.trans
    ((n06_correctedDivergence_heightPair_even hS h03 hz hs η (t, θ)).trans
      (n05_divergenceOperator_congr (L.coefficients z) (hη θ)))

end ContinuousFlexibility.Statements
