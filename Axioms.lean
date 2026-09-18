import Erdos960

/- # Axiom audit — every declaration this development exports.

Only `propext`, `Classical.choice`, `Quot.sound` are permitted. Any `sorryAx` or custom
`axiom` appearing below is an acceptance failure for the whole task.

Note in particular that `Erdos960.erdos960` — the main theorem — must appear with exactly
those three. `CurveModelAssumption` (paper Lemma 2.2 + the collinearity criterion) is *not*
an axiom: it is a `def … : Prop` that enters `erdos960` as an explicit hypothesis, so it
cannot and does not show up here. -/

/-! ## Main theorem (Theorem 2.1) and its assembly -/

#print axioms Erdos960.erdos960
#print axioms Erdos960.erdos960_of_curveModelAssumption
#print axioms Erdos960.exists_admissible

/-! ## Anti-vacuity instances -/

#print axioms Erdos960.bound_at_72
#print axioms Erdos960.bound_pos_at_72
#print axioms Erdos960.construction_at_72
#print axioms Erdos960.construction_clears_bound
#print axioms Erdos960.decomp_at_72
#print axioms Erdos960.decomp_at_73
#print axioms Erdos960.construction_at_73
#print axioms Erdos960.bound_at_73_lt_construction
#print axioms Erdos960.ordValues_nonempty_of_admissible
#print axioms Erdos960.F_ne_neg_one_of_admissible
#print axioms Erdos960.F_ne_neg_one_of_erdos960_hyps

/-! ## Defs.lean — the paper's §2.1 definitions and their basic properties -/

#print axioms Erdos960.IsLine
#print axioms Erdos960.ptsOn
#print axioms Erdos960.ptsOn_finite
#print axioms Erdos960.ptsOn_subset
#print axioms Erdos960.line_comm
#print axioms Erdos960.collinear_coe_of_isLine
#print axioms Erdos960.IsLine.eq_line_of_mem
#print axioms Erdos960.ordinaryLine
#print axioms Erdos960.ordinaryLines
#print axioms Erdos960.mem_ordinaryLines
#print axioms Erdos960.ptsOn_eq_pair_of_mem
#print axioms Erdos960.ordinaryLine.exists_pair
#print axioms Erdos960.ptsOn_injOn
#print axioms Erdos960.ordinaryLines_finite
#print axioms Erdos960.ord
#print axioms Erdos960.ord_le_choose
#print axioms Erdos960.ordGraph
#print axioms Erdos960.ordGraph_adj_iff
#print axioms Erdos960.lineOfEdge
#print axioms Erdos960.lineOfEdge_mk
#print axioms Erdos960.ptsOn_line_eq_pair_of_adj
#print axioms Erdos960.edge_eq_of_line_eq
#print axioms Erdos960.card_edgeFinset_ordGraph
#print axioms Erdos960.cliqueFree_of_isBipartite
#print axioms Erdos960.NoKCollinear
#print axioms Erdos960.Admissible
#print axioms Erdos960.ordValues
#print axioms Erdos960.ordValues_bddAbove
#print axioms Erdos960.F
#print axioms Erdos960.F_eq_sSup
#print axioms Erdos960.F_eq_neg_one
#print axioms Erdos960.F_eq_of_nonempty
#print axioms Erdos960.le_F

/-! ## Bridge.lean — geometry ⇄ group law -/

#print axioms Erdos960.card_edgeFinset_eq_ncard
#print axioms Erdos960.ordPairs
#print axioms Erdos960.mem_ordPairs
#print axioms Erdos960.card_ordPairs_eq_two_mul
#print axioms Erdos960.card_filter_ordAdj_eq
#print axioms Erdos960.edgeCount_eq_ord

/-! ## Curve.lean — the curve side -/

#print axioms Erdos960.HasCyclicSubgroupOfOrder
#print axioms Erdos960.zmod_hasCyclicSubgroup
#print axioms Erdos960.addCircle_hasCyclicSubgroup
#print axioms Erdos960.CurveModel
#print axioms Erdos960.third
#print axioms Erdos960.sum_third
#print axioms Erdos960.third_eq_iff
#print axioms Erdos960.CurveModel.pts
#print axioms Erdos960.CurveModel.card_pts
#print axioms Erdos960.CurveModel.emb_ne
#print axioms Erdos960.CurveModel.mem_pts
#print axioms Erdos960.CurveModel.mem_line_iff
#print axioms Erdos960.CurveModel.no_four_collinear
#print axioms Erdos960.CurveModel.ordinaryLine_iff
#print axioms Erdos960.CurveModel.noKCollinear_pts
#print axioms Erdos960.CurveModelAssumption
#print axioms Erdos960.Concrete.E
#print axioms Erdos960.Concrete.E_Δ
#print axioms Erdos960.Concrete.E_Δ_eq_sixteen_mul_paper
#print axioms Erdos960.Concrete.paper_discriminant
#print axioms Erdos960.Concrete.E_Δ_ne_zero
#print axioms Erdos960.Concrete.E_nonsingular
#print axioms Erdos960.Concrete.E_equation_iff
#print axioms Erdos960.Concrete.lineCubic
#print axioms Erdos960.Concrete.lineCubic_eval
#print axioms Erdos960.Concrete.lineCubic_natDegree_le
#print axioms Erdos960.Concrete.lineCubic_coeff_three
#print axioms Erdos960.Concrete.lineCubic_coeff_two
#print axioms Erdos960.Concrete.lineCubic_ne_zero
#print axioms Erdos960.Concrete.card_le_three_of_line

/-! ## Combinatorial.lean — the `ZMod (7m)` side (Prop. 2.4, 2.5 and §2.3) -/

#print axioms Erdos960.resid
#print axioms Erdos960.C
#print axioms Erdos960.H
#print axioms Erdos960.card_C
#print axioms Erdos960.card_H
#print axioms Erdos960.C_disjoint
#print axioms Erdos960.mem_C_iff
#print axioms Erdos960.A₀
#print axioms Erdos960.card_A₀
#print axioms Erdos960.A₀_disjoint_H
#print axioms Erdos960.ordAdj
#print axioms Erdos960.ordAdj_symm
#print axioms Erdos960.ordAdj_of_superset
#print axioms Erdos960.not_ordAdj_of_third
#print axioms Erdos960.edgeCount
#print axioms Erdos960.le_edgeCount
#print axioms Erdos960.ordAdj_residues
#print axioms Erdos960.ordAdj_crosses
#print axioms Erdos960.ordAdj_of_dual
#print axioms Erdos960.card_Dual
#print axioms Erdos960.ord_A₀_ge
#print axioms Erdos960.hgen
#print axioms Erdos960.addOrderOf_hgen
#print axioms Erdos960.hgen_mem_H
#print axioms Erdos960.zsmul_hgen_inj
#print axioms Erdos960.T
#print axioms Erdos960.card_T
#print axioms Erdos960.T_ne_zero
#print axioms Erdos960.T_subset_H
#print axioms Erdos960.Aset
#print axioms Erdos960.card_Aset
#print axioms Erdos960.no_edge_A₀_T
#print axioms Erdos960.T_induced_bipartite
#print axioms Erdos960.Aset_bipartite
#print axioms Erdos960.card_destroyed_by
#print axioms Erdos960.ord_Aset_ge
#print axioms Erdos960.key_identity
#print axioms Erdos960.final_bound
#print axioms Erdos960.m_ge_twelve
#print axioms Erdos960.exists_decomp
