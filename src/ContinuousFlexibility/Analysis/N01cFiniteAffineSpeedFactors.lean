module

public import ContinuousFlexibility.Analysis.N01cFiniteAffineInputs
public import ContinuousFlexibility.Analysis.N01cNormalizedSpeedPowerBounds

/-!
# Joint finite-affine smoothness of the actual normalized speed factors

The state exponent and polar inputs are genuine continuous-linear
fields. Their finite-affine restrictions are jointly smooth with the
physical point. The original N01b inequalities keep the two actual
denominators away from zero on the same neighbourhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private def finiteAffineSpeedDiscriminant (w c k pp : ℝ) : ℝ :=
  1 - 2 * w * c * k - c ^ 2 * (k ^ 2 + (1 + w ^ 2) * pp ^ 2)

private def finiteAffineSpeedQuotient (w c k pt : ℝ) : ℝ :=
  1 + c * ((k + (1 + w ^ 2) * pt) / w)

private def finiteAffineSpeedFormula (i : Fin 2) (w c k pp pr pt : ℝ) : ℝ :=
  if i = 0 then (1 + w ^ 2) * (c * pr) / (w * finiteAffineSpeedQuotient w c k pt)
  else Real.sqrt (finiteAffineSpeedDiscriminant w c k pp) /
    finiteAffineSpeedQuotient w c k pt

private theorem finiteAffineSpeedFormula_scalar
    (i : Fin 2) (w c k pp pr pt E Q d p : ℝ)
    (he : E = 1 + w ^ 2)
    (hd : d = 1 - 2 * w * c * k - c ^ 2 * (k ^ 2 + E * pp ^ 2))
    (hq : Q = 1 + c * ((k + E * pt) / w)) (hp : p = c * pr) :
    (if i = 0 then E * p / (w * Q) else Real.sqrt d / Q) =
      finiteAffineSpeedFormula i w c k pp pr pt := by
  subst E
  subst d
  subst Q
  subst p
  rfl

private theorem finiteAffineSpeedInputs_ne_zero_scalar
    (w c k pp pt E Q d : ℝ) (hw : w ≠ 0) (hQ : Q ≠ 0) (hD : d ≠ 0)
    (he : E = 1 + w ^ 2)
    (hd : d = 1 - 2 * w * c * k - c ^ 2 * (k ^ 2 + E * pp ^ 2))
    (hq : Q = 1 + c * ((k + E * pt) / w)) :
    w ≠ 0 ∧ finiteAffineSpeedDiscriminant w c k pp ≠ 0 ∧
      finiteAffineSpeedQuotient w c k pt ≠ 0 := by
  subst E
  subst d
  subst Q
  exact ⟨hw, hD, hQ⟩

private theorem contDiffOn_finiteAffineSpeedFormula
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {V : Set P}
    (w c : P → ℝ) (u : Fin 5 → P → ℝ) (f : Fin 2 → P → ℝ)
    (hw : ContDiffOn ℝ ∞ w V) (hc : ContDiffOn ℝ ∞ c V)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) V)
    (hnz : ∀ p ∈ V, w p ≠ 0 ∧
      finiteAffineSpeedDiscriminant (w p) (c p) (u 0 p) (u 1 p) ≠ 0 ∧
      finiteAffineSpeedQuotient (w p) (c p) (u 0 p) (u 4 p) ≠ 0)
    (hvalue : ∀ i p, p ∈ V → f i p =
      finiteAffineSpeedFormula i (w p) (c p) (u 0 p) (u 1 p) (u 3 p) (u 4 p))
    (i : Fin 2) : ContDiffOn ℝ ∞ (f i) V := by
  let e : P → ℝ := fun p => 1 + w p ^ 2
  let d : P → ℝ := fun p => finiteAffineSpeedDiscriminant (w p) (c p) (u 0 p) (u 1 p)
  let qn : P → ℝ := fun p => finiteAffineSpeedQuotient (w p) (c p) (u 0 p) (u 4 p)
  have he : ContDiffOn ℝ ∞ e V := contDiffOn_const.add (hw.pow 2)
  have hd : ContDiffOn ℝ ∞ d V :=
    (contDiffOn_const.sub (((contDiffOn_const.mul hw).mul hc).mul (hu 0))).sub
      ((hc.pow 2).mul (((hu 0).pow 2).add (he.mul ((hu 1).pow 2))))
  have hq : ContDiffOn ℝ ∞ qn V :=
    contDiffOn_const.add (hc.mul (((hu 0).add (he.mul (hu 4))).div hw
      (fun p hp => (hnz p hp).1)))
  by_cases hi : i = 0
  · have ha : ContDiffOn ℝ ∞
        (fun p => e p * (c p * u 3 p) / (w p * qn p)) V :=
      (he.mul (hc.mul (hu 3))).div (hw.mul hq)
        (fun p hp => mul_ne_zero (hnz p hp).1 (hnz p hp).2.2)
    exact ha.congr (fun p hp => by
      simpa only [finiteAffineSpeedFormula, if_pos hi, e, qn] using hvalue i p hp)
  · have hb : ContDiffOn ℝ ∞ (fun p => Real.sqrt (d p) / qn p) V :=
      (hd.sqrt (fun p hp => (hnz p hp).2.1)).div hq (fun p hp => (hnz p hp).2.2)
    exact hb.congr (fun p hp => by
      simpa only [finiteAffineSpeedFormula, if_neg hi, d, qn] using hvalue i p hp)

private theorem finiteAffineSpeedFormula_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (i : Fin 2) {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {q : PolarPoint} (hq : q ∈ annularOpen D) :
    normalizedSpeedFactor D S C i z q =
      finiteAffineSpeedFormula i (stateProfile D S C z.1 q.1) z.2
        (stateUPolarInput S 0 z.1 q) (stateUPolarInput S 1 z.1 q)
        (stateUPolarInput S 3 z.1 q) (stateUPolarInput S 4 z.1 q) := by
  exact finiteAffineSpeedFormula_scalar i
    (stateProfile D S C z.1 q.1) z.2 (heightRadial (stateU S z.1) q)
    (heightAngular (stateU S z.1) q)
    (radialPartial (heightAngular (stateU S z.1)) q)
    (angularPartial (heightAngular (stateU S z.1)) q)
    (profileEnergy (stateProfile D S C z.1) q)
    (heightQ (profileEnergy (stateProfile D S C z.1) q)
      (heightRadial (stateHeight D S C z) q)
      (angularPartial (heightAngular (stateHeight D S C z)) q) /
        stateProfile D S C z.1 q.1)
    (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q)
    (radialPartial (heightAngular (stateHeight D S C z)) q) rfl
    (n01_polarDiscriminant_stateHeight hS hT hA z q)
    (n01_heightQ_div_profile hS hT hA hB hz hq)
    (radialPartial_heightAngular_stateHeight hS hT hA z
      (hA.1.1.choose_spec.1.1.trans hq.1.1).ne')

private theorem finiteAffineSpeedInputs_actual_ne_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {q : PolarPoint} (hq : q ∈ annularOpen D) :
    stateProfile D S C z.1 q.1 ≠ 0 ∧
      finiteAffineSpeedDiscriminant (stateProfile D S C z.1 q.1) z.2
        (stateUPolarInput S 0 z.1 q) (stateUPolarInput S 1 z.1 q) ≠ 0 ∧
      finiteAffineSpeedQuotient (stateProfile D S C z.1 q.1) z.2
        (stateUPolarInput S 0 z.1 q) (stateUPolarInput S 4 z.1 q) ≠ 0 := by
  have hpos := n01PartB_denominators_pos hA.1.1.choose_spec.1 hS hA.2.1 hB hz hq
  exact finiteAffineSpeedInputs_ne_zero_scalar
    (stateProfile D S C z.1 q.1) z.2 (heightRadial (stateU S z.1) q)
    (heightAngular (stateU S z.1) q)
    (angularPartial (heightAngular (stateU S z.1)) q)
    (profileEnergy (stateProfile D S C z.1) q)
    (heightQ (profileEnergy (stateProfile D S C z.1) q)
      (heightRadial (stateHeight D S C z) q)
      (angularPartial (heightAngular (stateHeight D S C z)) q) /
        stateProfile D S C z.1 q.1)
    (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) q)
    hpos.1.ne' (div_pos hpos.2.1 hpos.1).ne' hpos.2.2.ne' rfl
    (n01_polarDiscriminant_stateHeight hS hT hA z q)
    (n01_heightQ_div_profile hS hT hA hB hz hq)

private theorem contDiffOn_jointStateProfile_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) {m : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (AnnularState S × ℝ)) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      stateProfile D S C (x + L p.1).1 p.2.1)
      ((univ : Set (Fin m → ℝ)) ×ˢ annularOpen D) := by
  have hexp : ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      (x + L p.1).1.2.1 * D.chi p.2.1 + stateControlSum C (x + L p.1).1 p.2.1)
      ((univ : Set (Fin m → ℝ)) ×ˢ annularOpen D) := by
    refine contDiffOn_finiteAffine_linearField
      (fun y : AnnularState S × ℝ => fun q : PolarPoint =>
        y.1.2.1 * D.chi q.1 + stateControlSum C y.1 q.1)
      (fun q hq => (stateProfileExponentCLM hS hT hA.1.1 hA.2.2.1 q.1 hq.1).comp
        (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ)) ?_ ?_ x L
    · intro q hq y
      change stateProfileExponentCLM hS hT hA.1.1 hA.2.2.1 q.1 hq.1 y.1 = _
      exact stateProfileExponentCLM_apply hS hT hA.1.1 hA.2.2.1 q.1 hq.1 y.1
    · intro y
      exact ((contDiff_const.mul hA.1.2.2.2.1.1).contDiffOn.add
        (contDiffOn_stateControlSum hA.2.2.1 y.1)).comp contDiff_fst.contDiffOn
          (fun q hq => hq.1)
  exact (hA.1.1.choose_spec.1.2.2.1.1.comp
    (contDiff_fst.comp contDiff_snd)).contDiffOn.mul hexp.exp

private theorem contDiffOn_jointStatePolar_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (hD : 0 < D.a)
    {m : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (AnnularState S × ℝ)) (j : Fin 5) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      stateUPolarInput S j (x + L p.1).1 p.2)
      ((univ : Set (Fin m → ℝ)) ×ˢ annularOpen D) := by
  exact contDiffOn_finiteAffine_linearField
    (fun y : AnnularState S × ℝ => stateUPolarInput S j y.1)
    (fun q hq => (stateUPolarInputCLM hT hS q hq j).comp
      (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ))
    (fun q hq y => by
      change stateUPolarInputCLM hT hS q hq j y.1 = _
      exact stateUPolarInputCLM_apply hT hS q hq (hD.trans hq.1.1).ne' j y.1)
    (fun y => contDiffOn_stateUPolarInput hT hS hD y.1 j) x L

theorem contDiffOn_normalizedSpeedFactor_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {m : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (AnnularState S × ℝ)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      normalizedSpeedFactor D S C i (x + L p.1) p.2)
      (((fun q => x + L q) ⁻¹' stateNeighborhood S C base ε) ×ˢ annularOpen D) := by
  have hsub : (((fun q => x + L q) ⁻¹' stateNeighborhood S C base ε) ×ˢ annularOpen D) ⊆
      ((univ : Set (Fin m → ℝ)) ×ˢ annularOpen D) := fun p hp => ⟨mem_univ _, hp.2⟩
  exact contDiffOn_finiteAffineSpeedFormula
    (P := (Fin m → ℝ) × PolarPoint)
    (fun p => stateProfile D S C (x + L p.1).1 p.2.1)
    (fun p => (x + L p.1).2) (fun j p => stateUPolarInput S j (x + L p.1).1 p.2)
    (fun j p => normalizedSpeedFactor D S C j (x + L p.1) p.2)
    ((contDiffOn_jointStateProfile_finiteAffine hS hT hA x L).mono hsub)
    ((contDiffOn_finiteAffine_linearField (V := annularOpen D)
      (fun y : AnnularState S × ℝ => fun _ : PolarPoint => y.2)
      (fun _ _ => ContinuousLinearMap.snd ℝ (AnnularState S) ℝ)
      (fun _ _ _ => rfl) (fun _ => contDiffOn_const) x L).mono hsub)
    (fun j => (contDiffOn_jointStatePolar_finiteAffine hS hT
      hA.1.1.choose_spec.1.1 x L j).mono hsub)
    (fun p hp => finiteAffineSpeedInputs_actual_ne_zero hS hT hA hB hp.1 hp.2)
    (fun j p hp => finiteAffineSpeedFormula_actual hS hT hA hB j hp.1 hp.2) i

end ContinuousFlexibility.Statements
