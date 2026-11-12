import ContinuousFlexibility.Analysis.N06VolumeFourierCutoff
import ContinuousFlexibility.Analysis.N06ReferenceForcingMap
import ContinuousFlexibility.Analysis.N06NegativeReferenceEquation

/-!
# Reference source approximants retaining the three actual columns

The original inverse fixes three scalar coefficients. Its signed remainder
forcing is JF = -F + C. Cutting JF gives the source F_N = C - cut_N(JF),
which converges in the same volume level. All three physical columns remain
unchanged; in particular the compatibility field need not have finite
angular support.

The finite object is the remainder forcing. No identification of the cut
unknown with the inverse of F_N is made here: that additionally requires
the actual reference operator and domain to commute with the cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n06_cut_source_algebra
    {E : Type*} [AddCommGroup E] (f g q : E) : q = f + g - (f + g - q) := by
  abel

private theorem n06_lp_affineForcing_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g fn gn : Lp ℝ 2 μ) (a b c : ℝ) (s k ell : α → ℝ)
    (hg : (g : α → ℝ) =ᵐ[μ] fun p => -f p + a * s p + b * k p + c * ell p)
    (he : gn = f + g - fn) :
    (gn : α → ℝ) =ᵐ[μ] fun p => -fn p + a * s p + b * k p + c * ell p := by
  rw [he]
  filter_upwards [Lp.coeFn_sub (f + g) fn, Lp.coeFn_add f g, hg]
    with p hsub hadd hforce
  simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd
  rw [hsub, hadd, hforce]
  ring

private theorem n06_lp_negativeForcing_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : Lp ℝ 2 μ) (a b c : ℝ) (s k ell : α → ℝ)
    (hg : (g : α → ℝ) =ᵐ[μ] fun p => -f p + a * s p + b * k p + c * ell p) :
    ((-g : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ]
      fun p => f p - a * s p - b * k p - c * ell p := by
  filter_upwards [Lp.coeFn_neg g, hg] with p hp hq
  simp only [Pi.neg_apply] at hp
  rw [hp, hq]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}

/-- The scalar coefficients are those of the original inverse at F. -/
def n06ReferenceFourierSource (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (N : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) : V.level (3 / 4 : ℝ) 0 b :=
  F + n06ReferenceForcingMap B columns F -
    n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F)

theorem n06ReferenceFourierSource_columns (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (N : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) :
    n06ReferenceFourierSource hV B columns N F =
      n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2) F -
        n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F) := by
  have he : F + n06ReferenceForcingMap B columns F =
      n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2) F := by
    simp only [n06ReferenceForcingMap, add_apply, neg_apply, ContinuousLinearMap.id_apply]
    abel
  exact congrArg (fun G => G -
    n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F)) he

theorem n06ReferenceFourierSource_error (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (N : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) :
    ‖n06ReferenceFourierSource hV B columns N F - F‖ =
      ‖n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F) -
        n06ReferenceForcingMap B columns F‖ := by
  have he : n06ReferenceFourierSource hV B columns N F - F =
      n06ReferenceForcingMap B columns F -
        n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F) := by
    unfold n06ReferenceFourierSource
    abel
  rw [he, norm_sub_rev]

theorem n06ReferenceFourierSource_tendsto (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    Tendsto (fun N => n06ReferenceFourierSource hV B columns N F) atTop (𝓝 F) := by
  have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => F + n06ReferenceForcingMap B columns F) atTop
        (𝓝 (F + n06ReferenceForcingMap B columns F))).sub
    (n06VolumeFourierCut_tendsto hV (3 / 4 : ℝ) 0 b (n06ReferenceForcingMap B columns F))
  simpa only [n06ReferenceFourierSource, add_sub_cancel_right] using h

/-- The same original graph inverse is continuous on these actual sources. -/
theorem n06ReferenceFourierSource_inverse_tendsto (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    Tendsto (fun N => B.inverse (n06ReferenceFourierSource hV B columns N F))
      atTop (𝓝 (B.inverse F)) :=
  (B.inverse.continuous.tendsto F).comp
    (n06ReferenceFourierSource_tendsto hV B columns F)

/-- This concerns globalInverse only on the original volume-model image;
no continuity on arbitrary canonical sequences is assumed. -/
theorem n06ReferenceFourierSource_globalInverse_tendsto
    {B : CanonicalDomainData S K V b}
    (h05 : N05Properties D T S C K V b B)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    Tendsto (fun N => B.globalInverse (V.forget (3 / 4 : ℝ) 0 b
      (n06ReferenceFourierSource h05.2.1 B columns N F))) atTop
        (𝓝 (B.globalInverse (V.forget (3 / 4 : ℝ) 0 b F))) := by
  have hV : IsVolumeModel T S K V := h05.2.1
  have hlim := n06ReferenceFourierSource_inverse_tendsto hV B columns F
  have hp : Continuous (fun u : B.Space => u.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have h := (hp.tendsto (B.inverse F)).comp hlim
  obtain ⟨_, _, _, _, _, _, _, _, _, hsame, _⟩ := h05
  simpa only [Function.comp_def, hsame] using h

/-- The unchanged scalar coordinates and the modified source have exactly
the cutoff of the original positive signed remainder forcing. -/
theorem n06ReferenceFourierSource_forcing_ae (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hcolumns : ∀ i m,
      (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
    (N : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    (V.forget (3 / 4 : ℝ) 0 b
      (n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F)) m :
        PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06ReferenceCanonicalForcing D S C K
        (n06CanonicalUnknownFourierCut N (B.inverse F).val.1)
        (V.forget (3 / 4 : ℝ) 0 b (n06ReferenceFourierSource hV B columns N F)) m := by
  let G := n06ReferenceForcingMap B columns F
  let FN := n06ReferenceFourierSource hV B columns N F
  have he : n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N G = F + G - FN :=
    n06_cut_source_algebra F G (n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N G)
  have he' : V.forget (3 / 4 : ℝ) 0 b
      (n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N G) m =
        V.forget (3 / 4 : ℝ) 0 b F m + V.forget (3 / 4 : ℝ) 0 b G m -
          V.forget (3 / 4 : ℝ) 0 b FN m := by
    rw [he]
    simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
  exact n06_lp_affineForcing_ae
    (V.forget (3 / 4 : ℝ) 0 b F m) (V.forget (3 / 4 : ℝ) 0 b G m)
    (V.forget (3 / 4 : ℝ) 0 b FN m)
    (V.forget (3 / 4 : ℝ) 0 b (n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N G) m)
    (B.inverse F).val.1.2.1 (B.inverse F).val.1.2.2.1 (B.inverse F).val.1.2.2.2
    (canonicalSource S K (C.referenceState, 0) m
      (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)))
    (canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D))
    (canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode S.psi))
    (n06ReferenceForcingMap_forget (D := D) (C := C) B columns hcolumns F m) he'

theorem n06ReferenceFourierSource_negative_forcing_ae (hV : IsVolumeModel T S K V)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hcolumns : ∀ i m,
      (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
    (N : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    (V.forget (3 / 4 : ℝ) 0 b
      (-n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F)) m :
        PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06NegativeReferenceForcing D S C K
        (n06CanonicalUnknownFourierCut N (B.inverse F).val.1)
        (V.forget (3 / 4 : ℝ) 0 b (n06ReferenceFourierSource hV B columns N F)) m := by
  simp only [map_neg, Pi.neg_apply]
  exact n06_lp_negativeForcing_ae
    (V.forget (3 / 4 : ℝ) 0 b (n06ReferenceFourierSource hV B columns N F) m)
    (V.forget (3 / 4 : ℝ) 0 b
      (n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (n06ReferenceForcingMap B columns F)) m)
    (B.inverse F).val.1.2.1 (B.inverse F).val.1.2.2.1 (B.inverse F).val.1.2.2.2
    (canonicalSource S K (C.referenceState, 0) m
      (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)))
    (canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D))
    (canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode S.psi))
    (n06ReferenceFourierSource_forcing_ae hV B columns hcolumns N F m)

set_option backward.isDefEq.respectTransparency true

/-- The actual volume-level approximants and their signed remainder forcings.
Keeping this conclusion named avoids unfolding the entire nonlinear history
while constructing the family. -/
def N06ReferenceFourierSourceApproximation
    (D : ReferenceData) (C : NonlinearGeometryData S)
    (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b) : Prop :=
    ∃ Fseq Gseq : ℕ → V.level (3 / 4 : ℝ) 0 b → V.level (3 / 4 : ℝ) 0 b,
      (∀ F, Tendsto (fun N => Fseq N F) atTop (𝓝 F)) ∧
      (∀ F, Tendsto (fun N => B.inverse (Fseq N F)) atTop (𝓝 (B.inverse F))) ∧
      (∀ N F, Gseq N F ∈ n06VolumeFiniteAngularCore (3 / 4 : ℝ) 0 b) ∧
      (∀ N F, Fseq N F =
        n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2) F - Gseq N F) ∧
      (∀ N F m, (V.forget (3 / 4 : ℝ) 0 b (Gseq N F) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          n06ReferenceCanonicalForcing D S C K
            (n06CanonicalUnknownFourierCut N (B.inverse F).val.1)
            (V.forget (3 / 4 : ℝ) 0 b (Fseq N F)) m) ∧
      (∀ N F m, (V.forget (3 / 4 : ℝ) 0 b (-Gseq N F) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          n06NegativeReferenceForcing D S C K
            (n06CanonicalUnknownFourierCut N (B.inverse F).val.1)
            (V.forget (3 / 4 : ℝ) 0 b (Fseq N F)) m)

/-- An approximation family together with the three genuine reference columns. -/
def N06ReferenceFourierSources (D : ReferenceData) (C : NonlinearGeometryData S)
    (B : CanonicalDomainData S K V b) : Prop :=
  ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
    (∀ i m, (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i)) ∧
    N06ReferenceFourierSourceApproximation D C B columns

private theorem n06_referenceFourierSources_of_columns
    (hV : IsVolumeModel T S K V) (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hcolumns : ∀ i m,
      (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i)) :
    N06ReferenceFourierSourceApproximation D C B columns := by
  refine ⟨n06ReferenceFourierSource hV B columns,
    fun N F => n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N
      (n06ReferenceForcingMap B columns F), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun F => n06ReferenceFourierSource_tendsto hV B columns F
  · exact fun F => n06ReferenceFourierSource_inverse_tendsto hV B columns F
  · exact fun N F => n06VolumeFourierCut_mem_finiteAngularCore hV (3 / 4 : ℝ) 0 b N
      (n06ReferenceForcingMap B columns F)
  · exact fun N F => n06ReferenceFourierSource_columns hV B columns N F
  · exact fun N F m => n06ReferenceFourierSource_forcing_ae hV B columns hcolumns N F m
  · exact fun N F m => n06ReferenceFourierSource_negative_forcing_ae hV B columns hcolumns N F m

/-- The actual physical columns are constructed from the retained geometry.
The conclusion gives source convergence, convergence through the same graph
inverse, and finite remainder forcing on both cylinder types. -/
theorem n06N05_exists_referenceFourierSources
    {B : CanonicalDomainData S K V b}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    N06ReferenceFourierSources D C B := by
  have h05 : N05Properties D T S C K V b B := h.2
  have hV : IsVolumeModel T S K V := h05.2.1
  obtain ⟨columns, hcolumns, _⟩ := n06Volume_exists_controlled_referenceScalarColumns
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K) (V := V)
    (base := base) (loss := loss) (ε := ε) hD hT hS hb hV h.1 hcoordinates
      (3 / 4 : ℝ) 0 b
  exact ⟨columns, hcolumns, n06_referenceFourierSources_of_columns hV B columns hcolumns⟩

end ContinuousFlexibility.Statements
