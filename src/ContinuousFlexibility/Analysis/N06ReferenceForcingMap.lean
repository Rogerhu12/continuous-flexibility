module

public import ContinuousFlexibility.Analysis.N06ControlledReferenceSources
public import ContinuousFlexibility.Analysis.N06ScalarColumns
public import ContinuousFlexibility.Analysis.N06ReferenceCanonicalEquation

/-!
# The actual reference forcing as a map on the original source space

The three scalar columns are the constructed physical columns in the
selected volume model. They combine with minus the original source to
give the genuine right-hand side of the positive reference equation.
The same N05 inverse supplies both the unknown and its scalar coordinates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem lp_reference_combination_ae
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    (f s k c : Lp ℝ 2 measure) (a mu ell : ℝ) :
    ((-f + (a • s + mu • k + ell • c) : Lp ℝ 2 measure) : α → ℝ)
      =ᵐ[measure] fun p => -f p + a * s p + mu * k p + ell * c p := by
  filter_upwards [Lp.coeFn_add (-f) (a • s + mu • k + ell • c), Lp.coeFn_neg f,
    Lp.coeFn_add (a • s + mu • k) (ell • c), Lp.coeFn_add (a • s) (mu • k),
    Lp.coeFn_smul a s, Lp.coeFn_smul mu k, Lp.coeFn_smul ell c]
    with p htotal hneg hsum hpair hs hk hc
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at htotal hneg hsum hpair hs hk hc
  rw [htotal, hneg, hsum, hpair, hs, hk, hc]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}

def n06ReferenceForcingMap (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
  -(ContinuousLinearMap.id ℝ _) +
    n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2)

theorem n06ReferenceForcingMap_forget (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hcolumns : ∀ i m,
      (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    (V.forget (3 / 4 : ℝ) 0 b (n06ReferenceForcingMap B columns F) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        n06ReferenceCanonicalForcing D S C K (B.inverse F).val.1
          (V.forget (3 / 4 : ℝ) 0 b F) m := by
  let v : CanonicalL2 S K m := V.forget (3 / 4 : ℝ) 0 b F m
  let s : CanonicalL2 S K m := V.forget (3 / 4 : ℝ) 0 b (columns 0) m
  let k : CanonicalL2 S K m := V.forget (3 / 4 : ℝ) 0 b (columns 1) m
  let c : CanonicalL2 S K m := V.forget (3 / 4 : ℝ) 0 b (columns 2) m
  let a : ℝ := (B.inverse F).val.1.2.1
  let μ : ℝ := (B.inverse F).val.1.2.2.1
  let lambdaCoeff : ℝ := (B.inverse F).val.1.2.2.2
  have he : V.forget (3 / 4 : ℝ) 0 b (n06ReferenceForcingMap B columns F) m =
      -v + (a • s + μ • k + lambdaCoeff • c) := by
    simp only [n06ReferenceForcingMap, add_apply,
      neg_apply, ContinuousLinearMap.id_apply,
      n06ScalarColumnOperator_apply, map_add, map_neg, map_smul,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
    rfl
  rw [he]
  apply (lp_reference_combination_ae v s k c a μ lambdaCoeff).trans
  filter_upwards [hcolumns 0 m, hcolumns 1 m, hcolumns 2 m] with p hsc hkc hcc
  change -V.forget (3 / 4 : ℝ) 0 b F m p +
      (B.inverse F).val.1.2.1 * V.forget (3 / 4 : ℝ) 0 b (columns 0) m p +
        (B.inverse F).val.1.2.2.1 * V.forget (3 / 4 : ℝ) 0 b (columns 1) m p +
          (B.inverse F).val.1.2.2.2 * V.forget (3 / 4 : ℝ) 0 b (columns 2) m p = _
  exact congrArg₂ (fun x y : ℝ => x + y)
    (congrArg₂ (fun x y : ℝ => x + y)
      (congrArg (fun x : ℝ => -v p + a * x) hsc)
      (congrArg (fun x : ℝ => μ * x) hkc))
    (congrArg (fun x : ℝ => lambdaCoeff * x) hcc)

set_option backward.isDefEq.respectTransparency true

/-- The original N05 graph supplies the reference PDE with one actual
bounded source map; neither a forcing lift nor its weak PDE is assumed. -/
theorem n06N05_exists_referenceForcingMap
    {B : CanonicalDomainData S K V b}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ J : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      (∀ (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ),
        (V.forget (3 / 4 : ℝ) 0 b (J F) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          n06ReferenceCanonicalForcing D S C K (B.inverse F).val.1
            (V.forget (3 / 4 : ℝ) 0 b F) m) ∧
      ∀ (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ), K.positive m = true →
        ∀ φ : PolarPoint → ℝ, CanonicalTest S K m φ →
        (∫ p, (B.inverse F).val.1.1 m p *
          canonicalOperator S K L (C.referenceState, 0) m φ p ∂canonicalMeasure S K m) =
          ∫ p, V.forget (3 / 4 : ℝ) 0 b (J F) m p * φ p ∂canonicalMeasure S K m := by
  have h05 : N05Properties D T S C K V b B := h.2
  have hV : IsVolumeModel T S K V := h05.2.1
  obtain ⟨columns, hcolumns, _⟩ :=
    n06Volume_exists_controlled_referenceScalarColumns
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K) (V := V)
      (base := base) (loss := loss) (ε := ε) hD hT hS hb hV h.1
      hcoordinates (3 / 4 : ℝ) 0 b
  let J : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
    n06ReferenceForcingMap B columns
  have hJ (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
      (V.forget (3 / 4 : ℝ) 0 b (J F) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        n06ReferenceCanonicalForcing D S C K (B.inverse F).val.1
          (V.forget (3 / 4 : ℝ) 0 b F) m :=
    n06ReferenceForcingMap_forget (D := D) (C := C) B columns hcolumns F m
  refine ⟨J, hJ, ?_⟩
  intro F m hm φ hφ
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have hA : N04PartA D S C K base ε := (n06_N04_qualitative_parts h.1.2.2.2.2.1).1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hweak := n06N05_positive_canonicalWeakPairing hD hb hS h.1.1.2 hA h05
    h01.2.2.1 href hs (B.inverse F) hm hφ
  have hright : (B.inverse F).val.2 = F := h05.2.2.2.2.2.2.2.1 F
  have hweak' :
      (∫ p, (B.inverse F).val.1.1 m p *
        canonicalOperator S K L (C.referenceState, 0) m φ p ∂canonicalMeasure S K m) =
      ∫ p, n06ReferenceCanonicalForcing D S C K (B.inverse F).val.1
        (V.forget (3 / 4 : ℝ) 0 b F) m p * φ p ∂canonicalMeasure S K m := by
    simpa only [hright] using hweak
  exact hweak'.trans (integral_congr_ae (by
    filter_upwards [hJ F m] with p hp
    exact congrArg (fun x : ℝ => x * φ p) hp.symm))

end ContinuousFlexibility.Statements
