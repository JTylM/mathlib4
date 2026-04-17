import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
 [FiniteDimensional 𝕜 E]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
 [FiniteDimensional 𝕜 F]
variable (f : E →L[𝕜] F)

open InnerProductSpace

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
lemma SVD_helper_symm (f : E →L[𝕜] F) : (f.adjoint ∘L f).IsSymmetric :=
f.isPositive_adjoint_comp_self.isSymmetric

noncomputable abbrev SVD_basis_left {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
  OrthonormalBasis (Fin n) 𝕜 E := (SVD_helper_symm f).eigenvectorBasis hn

noncomputable abbrev SingularValues {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
  Fin n → ℝ := fun k ↦ Real.sqrt ((SVD_helper_symm f).eigenvalues hn k)

omit [FiniteDimensional 𝕜 F] in
public theorem SingularValues_Antitone {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
    Antitone <| SingularValues hn f :=
  fun _ _ h ↦ Real.sqrt_le_sqrt <| (SVD_helper_symm f).eigenvalues_antitone _ h

omit [FiniteDimensional 𝕜 F] in
public theorem apply_SVD_basis_left {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F)
    (k : Fin n) : (f.adjoint ∘L f) (SVD_basis_left hn f k)
     = ((SVD_helper_symm f).eigenvalues hn k : 𝕜) • SVD_basis_left hn f k := by
  change (f.adjoint ∘L f).toLinearMap (SVD_basis_left hn f k)
   = ((SVD_helper_symm f).eigenvalues hn k : 𝕜) • SVD_basis_left hn f k
  rw [(SVD_helper_symm f).apply_eigenvectorBasis]

omit [FiniteDimensional 𝕜 F] in
lemma helper_eigenvalues_nonneg {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) (k : Fin n) :
    0 ≤ (SVD_helper_symm f).eigenvalues hn k :=
  LinearMap.IsPositive.nonneg_eigenvalues f.isPositive_adjoint_comp_self hn k

omit [FiniteDimensional 𝕜 F] in
public theorem SingularValue_eq_norm {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F)
 (k : Fin n) : SingularValues hn f k = ‖f (SVD_basis_left hn f k)‖ := by
  apply Real.sqrt_eq_cases.mpr
  left
  refine ⟨?_, norm_nonneg _⟩
  rw [← inner_self_eq_norm_mul_norm (𝕜 := 𝕜), ← f.adjoint_inner_right, ← f.adjoint.comp_apply,
   apply_SVD_basis_left, inner_smul_right]
  simp only [ContinuousLinearMap.coe_comp, inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one,
    map_one, one_pow, mul_one, RCLike.ofReal_re]

--omit [FiniteDimensional 𝕜 F]
public theorem norm_of_map_of_SingularValues {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F)
 (x : E) : ‖f x‖^2 = ∑ k, (SingularValues hn f k)^2 * ‖⟪x, SVD_basis_left hn f k⟫_𝕜‖^2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← f.adjoint_inner_right, ← f.adjoint.comp_apply]
  nth_rw 2 [← (SVD_basis_left hn f).sum_repr' x]
  rw [map_sum, inner_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, inner_smul_right, apply_SVD_basis_left, inner_smul_right, mul_comm, mul_assoc]
  nth_rw 2 [← inner_conj_symm]
  rw [RCLike.mul_conj]
  simp only [ContinuousLinearMap.coe_comp, RCLike.mul_re, RCLike.ofReal_re, RCLike.re_ofReal_pow,
    RCLike.ofReal_im, RCLike.im_ofReal_pow, mul_zero, sub_zero, SingularValues,
    mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero]
  left
  exact (Real.sq_sqrt (helper_eigenvalues_nonneg hn f k)).symm

--helper lemma, should be removed/renamed
lemma ker_spanned_by_SVD_basis_left {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
    f.ker = Submodule.span 𝕜 ({k | SingularValues hn f k = 0}.image (SVD_basis_left hn f)) := by
  apply le_antisymm
  · intro x hx
    replace hx : ‖f x‖^(2: ℕ) = 0 := by
      simpa [hx]
    rw [norm_of_map_of_SingularValues hn f x] at hx
    have : (fun i ↦ SingularValues hn f i ^ 2 * ‖⟪x, (SVD_basis_left hn f) i⟫_𝕜‖ ^ 2) ≥ 0 := by
      refine Pi.le_def.mpr fun k ↦ ?_
      simp only [Pi.zero_apply, Real.sqrt_nonneg, pow_succ_nonneg, norm_nonneg, mul_nonneg]
    apply (Fintype.sum_eq_zero_iff_of_nonneg this).1 at hx
    rw [← (SVD_basis_left hn f).sum_repr' x]
    apply Submodule.sum_mem
    intro k _
    replace hx : SingularValues hn f k ^ 2 * ‖⟪x, (SVD_basis_left hn f) k⟫_𝕜‖ ^ 2 = 0 := by
      symm
      calc 0 = (0 : Fin n → ℝ) k := rfl
        _ = _ := by rw [← hx]
    simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero] at hx
    obtain h|h := hx
    · refine Submodule.smul_mem _ _ <| Submodule.mem_span_of_mem ?_
      use k
      simp only [Set.mem_setOf_eq, h, and_self]
    rw [← inner_conj_symm, h, map_zero, zero_smul]
    exact Submodule.zero_mem _
  apply Submodule.span_le.2
  simp only [Set.image_subset_iff]
  intro k hk
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  rw [← norm_eq_zero, ← SingularValue_eq_norm, hk]

open Classical in
lemma ker_rank_eq_card_SV_eq_zero {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
    Module.finrank 𝕜 f.ker = {k | SingularValues hn f k = 0}.toFinset.card := by
  rw [ker_spanned_by_SVD_basis_left hn f, finrank_span_set_eq_card]
  · simp only [Set.toFinset_image, Set.toFinset_setOf]
    refine Finset.card_image_of_injective {x | SingularValues hn f x = 0} ?_
    intro k l hkl
    by_contra! h
    apply zero_ne_one (α := 𝕜)
    rw [((SVD_basis_left hn f).inner_eq_zero h).symm, ← hkl, (SVD_basis_left hn f).inner_eq_one k]
  refine LinearIndepOn.id_image ?_
  suffices LinearIndepOn 𝕜 (SVD_basis_left hn f) ⊤ by
    exact LinearIndepOn.mono this fun ⦃a⦄ a_1 ↦ trivial
  apply LinearIndependent.linearIndepOn (SVD_basis_left hn f).orthonormal.linearIndependent

/- The k-th singular value vanishes ↔ k ≥ rank f -/
public theorem SingularValue_eq_zero_iff_gt_rank {n : ℕ} (hn : Module.finrank 𝕜 E = n)
 (f : E →L[𝕜] F) (k : Fin n) : k ≥ f.rank.toNat ↔ SingularValues hn f k = 0 := by
  have : f.rank.toNat = n - Module.finrank 𝕜 f.ker := by
    rw [← hn, ← f.finrank_range_add_finrank_ker, add_tsub_cancel_right,
     LinearMap.rank, Module.finrank]
  rw [this, ker_rank_eq_card_SV_eq_zero hn]
  have : n - {k | SingularValues hn f k = 0}.toFinset.card
   = {k | SingularValues hn f k ≠ 0}.toFinset.card := by
    refine (Nat.eq_sub_of_add_eq' ?_).symm
    rw [← Finset.card_union_of_disjoint]
    · simp only [Set.toFinset_setOf, ne_eq, Finset.filter_union_filter_not_eq, Finset.card_univ,
      Fintype.card_fin]
    simpa only [Set.toFinset_setOf, ne_eq] using
     Finset.disjoint_filter_filter_not Finset.univ Finset.univ _
  rw [this]
  constructor
  · intro h
    by_contra!
    have : {l : Fin n | l < k.1 + 1}.toFinset ⊆ {k | SingularValues hn f k ≠ 0}.toFinset   := by
      refine Set.toFinset_subset_toFinset.mpr ?_
      intro l hl
      replace this := lt_of_le_of_ne (Real.sqrt_nonneg _) this.symm
      by_contra! h
      simp only [Order.lt_add_one_iff, Fin.val_fin_le, Set.mem_setOf_eq, ne_eq,
        Decidable.not_not] at hl h
      apply SingularValues_Antitone hn f at hl
      linarith
    apply Finset.card_le_card at this
    rw [Set.toFinset_setOf, ← Fintype.card_subtype, Fintype.card_fin_lt_of_le] at this
    · linarith
    simp only [Order.add_one_le_iff, Fin.is_lt]
  intro h
  have : {k | SingularValues hn f k ≠ 0}.toFinset ⊆ {l : Fin n | l < k}.toFinset := by
    refine Set.toFinset_subset_toFinset.mpr ?_
    intro l hl
    by_contra!
    simp only [Set.mem_setOf_eq, not_lt] at this
    apply SingularValues_Antitone hn f at this
    rw [h] at this
    exact hl <| le_antisymm this (Real.sqrt_nonneg _)
  apply le_of_le_of_eq (Finset.card_le_card this)
  rw [Set.toFinset_setOf, (Fintype.card_subtype fun x ↦ x < k).symm]
  refine Fintype.card_fin_lt_of_le ?_
  exact Fin.is_le'

/- The k-th singular value is positive ↔ k < rank f -/
public theorem SingularValue_pos_iff_lt_rank {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F)
    (k : Fin n) : k < f.rank.toNat ↔ 0 < SingularValues hn f k := by
  by_contra! h
  obtain h|h := h
  · linarith [h.1,
     (SingularValue_eq_zero_iff_gt_rank hn f k).2 <| le_antisymm h.2 (Real.sqrt_nonneg _)]
  linarith [h.2, (SingularValue_eq_zero_iff_gt_rank hn f k).1 h.1]

--helper lemma, should be removed/renamed
omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional 𝕜 F] in
private lemma rank_le_domain {n : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
    f.rank.toNat ≤ n := by
  rw [← hn]
  exact Cardinal.toNat_le_toNat f.rank_le_domain <| Module.rank_lt_aleph0 𝕜 E

--helper lemma, should be removed/renamed
omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional 𝕜 E] in
private lemma rank_le_range {m : ℕ} (hm : Module.finrank 𝕜 F = m) (f : E →L[𝕜] F) :
    f.rank.toNat ≤ m := by
  rw [← hm]
  exact Cardinal.toNat_le_toNat f.rank_le_range <| Module.rank_lt_aleph0 𝕜 F

noncomputable abbrev SVD_basis_rightAux {n m : ℕ} (hn : Module.finrank 𝕜 E = n)
 (f : E →L[𝕜] F) : Fin m → F := fun k ↦ if h : k < f.rank.toNat
   then ((SingularValues hn f ⟨k, lt_of_lt_of_le h (rank_le_domain hn f)⟩)⁻¹ : 𝕜)
    • f (SVD_basis_left hn f ⟨k, lt_of_lt_of_le h (rank_le_domain hn f)⟩)
   else 0

lemma SVD_basis_rightAux_Orthonormal {n m : ℕ} (hn : Module.finrank 𝕜 E = n) (f : E →L[𝕜] F) :
    Orthonormal 𝕜 ({k : Fin m | k.val < f.rank.toNat}.restrict (SVD_basis_rightAux hn f)) := by
  constructor
  · intro ⟨⟨k, hkm⟩, hk⟩
    replace hk : k < f.rank.toNat := hk
    simp only [Set.mem_setOf_eq, Set.restrict_apply, SVD_basis_rightAux, SingularValue_eq_norm,
      dif_pos hk]
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, ← SingularValue_eq_norm,
     abs_of_nonneg (Real.sqrt_nonneg _)]
    apply inv_mul_cancel₀
    linarith
     [(SingularValue_pos_iff_lt_rank hn f ⟨k, lt_of_lt_of_le hk (rank_le_domain hn f)⟩).mp hk]
  intro ⟨⟨k, hkm⟩, hk⟩ ⟨⟨l, hlm⟩, hl⟩ hkl
  replace hk : k < f.rank.toNat := hk
  replace hl : l < f.rank.toNat := hl
  simp only [Set.mem_setOf_eq, Set.restrict_apply, SVD_basis_rightAux, dif_pos hk, dif_pos hl]
  simp only [inner_smul_left, inner_smul_right, map_inv₀, mul_eq_zero, inv_eq_zero]
  right; right
  rw [← f.adjoint_inner_right, ← f.adjoint.comp_apply, apply_SVD_basis_left, inner_smul_right]
  simp only [ContinuousLinearMap.coe_comp, mul_eq_zero]
  right
  refine (SVD_basis_left hn f).inner_eq_zero  ?_
  simpa only [ne_eq, Fin.mk.injEq, Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq] using hkl

--helper lemma, should be removed/renamed
omit [FiniteDimensional 𝕜 F] [CompleteSpace F] in
private lemma cardAux {m : ℕ} (hm : Module.finrank 𝕜 F = m) :
 Module.finrank 𝕜 F = Fintype.card (Fin m) := by simp only [hm, Fintype.card_fin]

noncomputable def SVD_basis_right {n m : ℕ} (hn : Module.finrank 𝕜 E = n)
  (hm : Module.finrank 𝕜 F = m) (f : E →L[𝕜] F) :
    OrthonormalBasis (Fin m) 𝕜 F := Classical.choose <|
     (SVD_basis_rightAux_Orthonormal hn f).exists_orthonormalBasis_extension_of_card_eq (cardAux hm)

public theorem SVD_basis_right_spec {n m : ℕ} (hn : Module.finrank 𝕜 E = n)
  (hm : Module.finrank 𝕜 F = m) (f : E →L[𝕜] F) (k : Fin m) (hk : k < f.rank.toNat) :
    SVD_basis_right hn hm f k = SVD_basis_rightAux hn f k := by
  apply Classical.choose_spec <| Orthonormal.exists_orthonormalBasis_extension_of_card_eq
   (cardAux hm) (SVD_basis_rightAux_Orthonormal hn f)
  exact hk

/- f maps left singular vectors to the corresponding right singular vector times singular value -/
public theorem SVD_basis_diagonal_left {n m : ℕ} (hn : Module.finrank 𝕜 E = n)
  (hm : Module.finrank 𝕜 F = m) (f : E →L[𝕜] F) (k : Fin n) (hk : k < m) :
    f (SVD_basis_left hn f k) =
     ((SingularValues hn f k) : 𝕜) • (SVD_basis_right hn hm f ⟨k, hk⟩) := by
  by_cases! hkf : k < f.rank.toNat
  · rw [SVD_basis_right_spec hn hm f ⟨k, hk⟩ hkf, SVD_basis_rightAux, dif_pos hkf,
     smul_smul, mul_inv_cancel₀, one_smul]
    simp only [ne_eq, map_eq_zero]
    exact fun h ↦ by linarith [(SingularValue_eq_zero_iff_gt_rank hn f k).mpr h]
  simp [zero_smul, ← norm_eq_zero, ← SingularValue_eq_norm,
    (SingularValue_eq_zero_iff_gt_rank hn f k).mp hkf]
/- f† maps right singular vectors to the corresponding left singular vector times singular value -/
public theorem SVD_basis_diagonal_right {n m : ℕ} (hn : Module.finrank 𝕜 E = n)
  (hm : Module.finrank 𝕜 F = m) (f : E →L[𝕜] F) (k : Fin m) (hk : k < n) :
    f.adjoint (SVD_basis_right hn hm f k) =
     ((SingularValues hn f ⟨k, hk⟩) : 𝕜) • (SVD_basis_left hn f ⟨k, hk⟩) := by
  by_cases! hkf : k < f.rank.toNat
  · rw [SVD_basis_right_spec hn hm f k hkf, SVD_basis_rightAux, dif_pos hkf,
     map_smul, ← f.adjoint.comp_apply, apply_SVD_basis_left, smul_smul, SingularValues]
    apply Mathlib.Tactic.LinearCombination.smul_eq_const
    rw [← RCLike.ofReal_inv, ← RCLike.ofReal_mul]
    apply RCLike.ofReal_inj.2
    nth_rw 2 [← Real.mul_self_sqrt (helper_eigenvalues_nonneg hn f ⟨k, hk⟩)]
    field_simp
  rw [(SingularValue_eq_zero_iff_gt_rank hn f ⟨k, hk⟩).mp hkf, RCLike.ofReal_zero, zero_smul,
   ← (SVD_basis_left hn f).sum_repr' (f.adjoint <| (SVD_basis_right hn hm f) k)]
  refine Fintype.sum_eq_zero _ fun l ↦ ?_
  rw [f.adjoint_inner_right]
  by_cases! hlf : l < f.rank.toNat
  · rw [SVD_basis_diagonal_left hn hm f l (lt_of_lt_of_le hlf (rank_le_range hm f)),
    inner_smul_left]
    have : ⟪(SVD_basis_right hn hm f) ⟨l.1, lt_of_lt_of_le hlf (rank_le_range hm f)⟩,
     (SVD_basis_right hn hm f) k⟫_𝕜 = 0 := by
      apply OrthonormalBasis.inner_eq_zero (SVD_basis_right hn hm f)
      intro h
      apply Fin.val_eq_of_eq at h
      linarith
    simp only [this, mul_zero, zero_smul]
  have : f ((SVD_basis_left hn f) l) = 0 := by
    rw [← norm_eq_zero, ← SingularValue_eq_norm, (SingularValue_eq_zero_iff_gt_rank hn f l).1 hlf]
  rw [this, inner_zero_left, zero_smul]
