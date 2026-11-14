module

public import ContinuousFlexibility.Analysis.N01cComponentCosineSpeed
public import ContinuousFlexibility.Analysis.N01cFiniteAffineMixedJets

/-!
# Actual physical-speed finite-affine smoothness

On the interior of a component the canonical optical square is positive.
The same actual normalized factors therefore give a jointly smooth
finite-affine formula for the ordinary speed. Arbitrary physical radial
derivatives are taken on that open component before fixing the radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Differentiating the last scalar variable preserves joint smoothness
on the original product of two open sets. -/
theorem n01c_contDiffOn_uncurry_iteratedDeriv_open
    {V : Set P} {I : Set ℝ} (hV : IsOpen V) (hI : IsOpen I)
    {f : P → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ I)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y : P × ℝ => iteratedDeriv n (f y.1) y.2) (V ×ˢ I) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hf
  | succ n ih =>
      intro y hy
      have haux : ContDiffAt ℝ ∞ (fun z : (P × ℝ) × ℝ =>
          iteratedDeriv n (f z.1.1) z.2) (y, y.2) :=
        (ih.contDiffAt ((hV.prod hI).mem_nhds hy)).comp (y, y.2)
          ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
      have hderiv : ContDiffAt ℝ ∞ (fun z : P × ℝ =>
          fderiv ℝ (fun r => iteratedDeriv n (f z.1) r) z.2) y :=
        haux.fderiv contDiffAt_snd (by simp)
      have hvalue := hderiv.clm_apply (contDiffAt_const (c := (1 : ℝ)))
      simpa only [iteratedDeriv_succ, fderiv_apply_one_eq_deriv] using
        hvalue.contDiffWithinAt

/-- Physical radial differentiation retains all finite parameter and
angular variables on the same open component. -/
theorem n01c_contDiffOn_radialIterate_family
    {V : Set P} {I : Set ℝ} (hV : IsOpen V) (hI : IsOpen I)
    {f : P × (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ (I ×ˢ (univ : Set ℝ)))) (a : ℕ) :
    ContDiffOn ℝ ∞ (fun y : P × (ℝ × ℝ) =>
      iteratedDeriv a (fun r => f (y.1, (r, y.2.2))) y.2.1)
      (V ×ˢ (I ×ˢ (univ : Set ℝ))) := by
  let g : (P × ℝ) → ℝ → ℝ := fun y r => f (y.1, (r, y.2))
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g)
      ((V ×ˢ (univ : Set ℝ)) ×ˢ I) :=
    hf.comp ((contDiffOn_fst.fst).prodMk
      (contDiffOn_snd.prodMk (contDiffOn_fst.snd)))
      (fun y hy => ⟨hy.1.1, hy.2, mem_univ _⟩)
  have hd := n01c_contDiffOn_uncurry_iteratedDeriv_open
    (hV.prod isOpen_univ) hI hg a
  exact hd.comp ((contDiffOn_fst.prodMk (contDiffOn_snd.snd)).prodMk
    (contDiffOn_snd.fst))
    (fun y hy => ⟨⟨hy.1, mem_univ _⟩, hy.2.1⟩)

/-- The normalized scalar formula is assembled before instantiating the
actual state-dependent coefficient functions. -/
private theorem n01c_contDiffOn_normalized_sqrt_formula
    {V : Set P} {I R : Set ℝ}
    (F A B : P × (ℝ × ℝ) → ℝ) (Q Qactual : P × ℝ → ℝ)
    (hIR : I ⊆ R)
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (R ×ˢ (univ : Set ℝ))))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (R ×ˢ (univ : Set ℝ))))
    (hQ : ContDiffOn ℝ ∞ Q ((univ : Set P) ×ˢ R))
    (hpos : ∀ x ∈ V, ∀ r ∈ I, 0 < Q (x, r))
    (hformula : ∀ x ∈ V, ∀ q ∈ I ×ˢ (univ : Set ℝ),
      F (x, q) = -A (x, q) - B (x, q) * Real.sqrt (Qactual (x, q.1)))
    (hactual : ∀ x ∈ V, ∀ r ∈ I, Q (x, r) = Qactual (x, r)) :
    ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ (univ : Set ℝ))) := by
  have hsub : V ×ˢ (I ×ˢ (univ : Set ℝ)) ⊆
      V ×ˢ (R ×ˢ (univ : Set ℝ)) :=
    fun p hp => ⟨hp.1, hIR hp.2.1, mem_univ _⟩
  have hQc : ContDiffOn ℝ ∞ (fun p : P × (ℝ × ℝ) => Q (p.1, p.2.1))
      (V ×ˢ (I ×ˢ (univ : Set ℝ))) :=
    hQ.comp (contDiffOn_fst.prodMk (contDiffOn_snd.fst))
      (fun p hp => ⟨mem_univ _, hIR hp.2.1⟩)
  have hs := (hA.mono hsub).neg.sub
    ((hB.mono hsub).mul (hQc.sqrt (fun p hp => (hpos p.1 hp.1 p.2.1 hp.2.1).ne')))
  exact hs.congr (fun p hp =>
    (hformula p.1 hp.1 p.2 hp.2).trans
      (congrArg (fun q : ℝ => -A p - B p * Real.sqrt q)
        (hactual p.1 hp.1 p.2.1 hp.2.1).symm))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The positive divided square gives strict positivity of the actual
optical square at each interior physical point. -/
theorem componentOpticalSquare_pos_of_quotient
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {U : Set (AnnularState S × ℝ)}
    (hA : N01PartA D T S C)
    (hpos : ∀ z ∈ U, ∀ m r, r ∈ Icc (C.left m) (C.right m) →
      0 < twoRootDivided (componentOpticalSquare D S C m z)
        (C.left m) (C.right m) r)
    {z : AnnularState S × ℝ} (hz : z ∈ U) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    0 < componentOpticalSquare D S C m z r := by
  have hv := hpos z hz m r ⟨hr.1.le, hr.2.le⟩
  have hl : 0 < r - C.left m := sub_pos.mpr hr.1
  have hh : 0 < C.right m - r := sub_pos.mpr hr.2
  rw [← twoRootDivided_mul_rootFactors (hA.2.2.1.1 m).2.1
    (componentOpticalSquare_boundary_zero hA m z (Or.inl rfl))
    (componentOpticalSquare_boundary_zero hA m z (Or.inr rfl)) r]
  positivity

/-- The actual ordinary minus speed is jointly smooth on every finite
affine state plane and the physical open component. -/
theorem contDiffOn_minusCharacteristicSpeed_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r)
    (m : ℕ) {n : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState S × ℝ)) :
    ContDiffOn ℝ ∞ (fun p : (Fin n → ℝ) × PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C (x + L p.1)) p.2)
      (((fun y => x + L y) ⁻¹' stateNeighborhood S C base ε) ×ˢ
        (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))) := by
  have hIR : Ioo (C.left m) (C.right m) ⊆ Ioo D.a D.b :=
    fun r hr => ⟨(hA.2.2.1.1 m).1.trans hr.1, hr.2.trans (hA.2.2.1.1 m).2.2⟩
  exact n01c_contDiffOn_normalized_sqrt_formula
    (fun p : (Fin n → ℝ) × PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C (x + L p.1)) p.2)
    (fun p : (Fin n → ℝ) × PolarPoint => normalizedSpeedFactor D S C 0 (x + L p.1) p.2)
    (fun p : (Fin n → ℝ) × PolarPoint => normalizedSpeedFactor D S C 1 (x + L p.1) p.2)
    (fun p : (Fin n → ℝ) × ℝ => componentOpticalSquare D S C m (x + L p.1) p.2)
    (fun p : (Fin n → ℝ) × ℝ =>
      -deriv (stateProfile D S C (x + L p.1).1) p.2 /
        (p.2 * stateProfile D S C (x + L p.1).1 p.2))
    hIR
    (contDiffOn_normalizedSpeedFactor_finiteAffine hS hT hA hB x L 0)
    (contDiffOn_normalizedSpeedFactor_finiteAffine hS hT hA hB x L 1)
    (contDiffOn_componentOpticalSquare_finiteAffine hS hT hA m x L)
    (fun y hy r hr => componentOpticalSquare_pos_of_quotient (z := x + L y) hA hpos hy m hr)
    (fun y hy q hq => minusCharacteristicSpeed_normalized_factors
      (z := x + L y) (q := q) hS hT hA hB hy ⟨hIR hq.1, mem_univ _⟩)
    (fun y _ r hr => componentOpticalSquare_eq_actual hA m (x + L y) hr)

/-- At every fixed interior radius, every actual radial speed jet is
jointly smooth on finite affine state planes and the angular line. The
additional time coordinate is unused. -/
theorem minusCharacteristicSpeed_radialJet_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r)
    (m a : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m)) :
    IsFiniteAffineTimeSmooth (stateNeighborhood S C base ε)
      (fun p : (AnnularState S × ℝ) × PolarPoint =>
        mixedDerivative a 0 (minusCharacteristicSpeed (originalCoefficients D S C p.1))
          (r, p.2.2)) := by
  intro n x L
  have hV : IsOpen ((fun y : Fin n → ℝ => x + L y) ⁻¹'
      stateNeighborhood S C base ε) :=
    (isOpen_stateNeighborhood S C base ε).preimage (continuous_const.add L.continuous)
  have hd := n01c_contDiffOn_radialIterate_family hV isOpen_Ioo
    (contDiffOn_minusCharacteristicSpeed_finiteAffine hS hT hA hB hpos m x L) a
  have hc : ContDiffOn ℝ ∞ (fun p : (Fin n → ℝ) × PolarPoint =>
      iteratedDeriv a (fun s =>
        minusCharacteristicSpeed (originalCoefficients D S C (x + L p.1)) (s, p.2.2)) r)
      (((fun y => x + L y) ⁻¹' stateNeighborhood S C base ε) ×ˢ
        (univ : Set PolarPoint)) :=
    hd.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk (contDiffOn_snd.snd)))
      (fun p hp => ⟨hp.1, hr, mem_univ _⟩)
  simpa only [mixedDerivative, iteratedDeriv_zero, Function.comp_def] using hc

end ContinuousFlexibility.Statements
