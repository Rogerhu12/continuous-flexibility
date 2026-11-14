module

public import ContinuousFlexibility.Analysis.N06ActualRelativeJetBounds
public import ContinuousFlexibility.Analysis.N06CurrentRelativeSourceIdentity
public import ContinuousFlexibility.Analysis.N06ScalarColumns

/-!
# The actual relative map on one retained source level

The principal difference, signed potential difference, and three actual
scalar columns are combined as continuous linear endomorphisms of the
same N05 source space. The canonical source formula and its operator norm
keep all three contributions explicit.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06ActualRelativeMapLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _
local instance n06ActualRelativeMapLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _
local instance n06ActualRelativeMapGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06ActualRelativeMapGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private theorem n06_actual_lp_combination_ae
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    (f g v s k c : Lp ℝ 2 measure) (a mu ell : ℝ) :
    ((f + (g + v + (a • s + mu • k + ell • c)) : Lp ℝ 2 measure) : α → ℝ)
      =ᵐ[measure] fun p => f p + g p + v p + a * s p + mu * k p + ell * c p := by
  filter_upwards [Lp.coeFn_add f (g + v + (a • s + mu • k + ell • c)),
    Lp.coeFn_add (g + v) (a • s + mu • k + ell • c), Lp.coeFn_add g v,
    Lp.coeFn_add (a • s + mu • k) (ell • c), Lp.coeFn_add (a • s) (mu • k),
    Lp.coeFn_smul a s, Lp.coeFn_smul mu k, Lp.coeFn_smul ell c]
    with p htotal hparts hgv hsum hpair hs hk hc
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at htotal hparts hgv hsum hpair hs hk hc
  rw [htotal, hparts, hgv, hsum, hpair, hs, hk, hc]
  ring

private theorem n06_actual_lp_combination_substitute
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    (total f g v s k c : Lp ℝ 2 measure) (a mu ell : ℝ)
    (he : total = f + (g + v + (a • s + mu • k + ell • c)))
    {v' s' k' c' : α → ℝ}
    (hv : (v : α → ℝ) =ᵐ[measure] v')
    (hs : (s : α → ℝ) =ᵐ[measure] s')
    (hk : (k : α → ℝ) =ᵐ[measure] k')
    (hc : (c : α → ℝ) =ᵐ[measure] c') :
    (total : α → ℝ) =ᵐ[measure]
      fun p => f p + g p + v' p + a * s' p + mu * k' p + ell * c' p := by
  subst total
  apply (n06_actual_lp_combination_ae f g v s k c a mu ell).trans
  filter_upwards [hv, hs, hk, hc] with p hp hs hk hc
  rw [hp, hs, hk, hc]

private theorem n06_actual_linear_combination
    {E X : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup X] [Module ℝ X]
    (decode : E →ₗ[ℝ] X) (f g v s k c : E) (a mu ell : ℝ) :
    decode (f + (g + v + (a • s + mu • k + ell • c))) =
      decode f + (decode g + decode v +
        (a • decode s + mu • decode k + ell • decode c)) := by
  simp only [map_add, map_smul]

private theorem n06_actual_norm_three_terms
    {E : Type*} [SeminormedAddCommGroup E]
    (x y z : E) {Qc Qp Qcol δ s : ℝ}
    (hx : ‖x‖ ≤ Qc * δ) (hy : ‖y‖ ≤ Qp * δ)
    (hz : ‖z‖ ≤ 3 * (Qcol * δ) * s) :
    ‖x + y + z‖ ≤ (Qc + Qp + 3 * Qcol * s) * δ := by
  calc
    ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ :=
      (norm_add_le (x + y) z).trans (add_le_add (norm_add_le x y) le_rfl)
    _ ≤ Qc * δ + Qp * δ + 3 * (Qcol * δ) * s :=
      add_le_add (add_le_add hx hy) hz
    _ = (Qc + Qp + 3 * Qcol * s) * δ := by ring

/-- The three analytic contributions act on the same retained source level. -/
def n06ActualRelativeMap (B : CanonicalDomainData S K V b)
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
  Mc + Mp + n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2)

private theorem n06ActualRelativeMap_apply
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    n06ActualRelativeMap B Mc Mp columns F = Mc F + Mp F +
      ((B.inverse F).val.1.2.1 • columns 0 +
        (B.inverse F).val.1.2.2.1 • columns 1 +
        (B.inverse F).val.1.2.2.2 • columns 2) := by
  change Mc F + Mp F + n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2) F = _
  exact congrArg (fun u : V.level (3 / 4 : ℝ) 0 b => Mc F + Mp F + u)
    (n06ScalarColumnOperator_apply B (columns 0) (columns 1) (columns 2) F)

private theorem n06ActualRelativeMap_forget_value
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    V.forget (3 / 4 : ℝ) 0 b (F + n06ActualRelativeMap B Mc Mp columns F) m =
      V.forget (3 / 4 : ℝ) 0 b F m +
        (V.forget (3 / 4 : ℝ) 0 b (Mc F) m + V.forget (3 / 4 : ℝ) 0 b (Mp F) m +
          ((B.inverse F).val.1.2.1 • V.forget (3 / 4 : ℝ) 0 b (columns 0) m +
            (B.inverse F).val.1.2.2.1 • V.forget (3 / 4 : ℝ) 0 b (columns 1) m +
            (B.inverse F).val.1.2.2.2 • V.forget (3 / 4 : ℝ) 0 b (columns 2) m)) := by
  let decode : V.level (3 / 4 : ℝ) 0 b →ₗ[ℝ] CanonicalL2 S K m :=
    (LinearMap.proj m).comp (V.forget (3 / 4 : ℝ) 0 b)
  have he := congrArg (fun u : V.level (3 / 4 : ℝ) 0 b => decode (F + u))
    (n06ActualRelativeMap_apply (B := B) Mc Mp columns F)
  exact he.trans (n06_actual_linear_combination decode F (Mc F) (Mp F)
    (columns 0) (columns 1) (columns 2) (B.inverse F).val.1.2.1
    (B.inverse F).val.1.2.2.1 (B.inverse F).val.1.2.2.2)

/-- The actual source formula has the required positive/negative potential
sign and retains the coordinate change of all three scalar columns. -/
theorem n06ActualRelativeMap_forget
    {z : AnnularState S × ℝ}
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hMp : ∀ F m,
      (V.forget (3 / 4 : ℝ) 0 b (Mp F) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => (if K.positive m then (-1 : ℝ) else 1) *
          (K.potential z m p - K.potential (C.referenceState, 0) m p) *
            (B.inverse F).val.1.1 m p)
    (hcolumns : ∀ i m,
      (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        n06ActualCanonicalColumnDifference D S C L K z i m)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    (V.forget (3 / 4 : ℝ) 0 b (F + n06ActualRelativeMap B Mc Mp columns F) m :
      PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        n06CurrentRelativeSourceField D S C L K z (B.inverse F).val.1
          (V.forget (3 / 4 : ℝ) 0 b F) (V.forget (3 / 4 : ℝ) 0 b (Mc F)) m := by
  exact n06_actual_lp_combination_substitute
    (V.forget (3 / 4 : ℝ) 0 b (F + n06ActualRelativeMap B Mc Mp columns F) m)
    (V.forget (3 / 4 : ℝ) 0 b F m) (V.forget (3 / 4 : ℝ) 0 b (Mc F) m)
    (V.forget (3 / 4 : ℝ) 0 b (Mp F) m) (V.forget (3 / 4 : ℝ) 0 b (columns 0) m)
    (V.forget (3 / 4 : ℝ) 0 b (columns 1) m) (V.forget (3 / 4 : ℝ) 0 b (columns 2) m)
    (B.inverse F).val.1.2.1 (B.inverse F).val.1.2.2.1 (B.inverse F).val.1.2.2.2
    (n06ActualRelativeMap_forget_value (B := B) Mc Mp columns F m)
    (hMp F m) (hcolumns 0 m) (hcolumns 1 m) (hcolumns 2 m)

theorem norm_n06ActualRelativeMap_le
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b) {Qc Qp Qcol δ : ℝ}
    (hc : ‖Mc‖ ≤ Qc * δ) (hp : ‖Mp‖ ≤ Qp * δ)
    (hcolumns : ∀ i, ‖columns i‖ ≤ Qcol * δ) :
    ‖n06ActualRelativeMap B Mc Mp columns‖ ≤
      (Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖) * δ := by
  exact n06_actual_norm_three_terms Mc Mp
    (n06ScalarColumnOperator B (columns 0) (columns 1) (columns 2)) hc hp
    (norm_n06ScalarColumnOperator_small B (columns 0) (columns 1) (columns 2)
      (hcolumns 0) (hcolumns 1) (hcolumns 2))

end ContinuousFlexibility.Statements
