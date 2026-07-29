import Mathlib.Tactic
import «wasm2.0»
import «custom_notation»
open functype list

set_option pp.parens true
set_option pp.numericTypes true

def ai_principal_typing
    -- p_* for params to keep track of which variables come from parameters in
    -- this huge definition
    (p_store      : store)
    (p_context    : context)
    (p_admininstr : admininstr)
    (p_functype   : functype)
    : Prop :=
    match p_admininstr with
        | admininstr.NOP            => p_functype = ([] f-> [])
        | admininstr.UNREACHABLE    => true -- this is equivalent to the spec, which has no effective additonal constraints
        | admininstr.DROP           => ∃ (t : valtype),
                                           p_functype = ([t] f-> [])
        | admininstr.SELECT
            (some [(t : valtype)])  => p_functype = ([t, t, valtype.I32] f-> [t])
        | admininstr.SELECT
            none                    => ∃ (t t' : valtype),
                                           p_functype = ([t, t, valtype.I32] f-> [t])
                                         ∧ t sub< t'
                                         ∧ (
                                              ∃ (nt : numtype), t' = valtype_numtype nt
                                            ∨ ∃ (vt : vectype), t' = valtype_vectype vt
                                           )
        | admininstr.SELECT
            _                       => false
        | admininstr.BLOCK
            (bt : blocktype)
            (instrs : List instr)   => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs
                                               (t1s f-> t2s)
        | admininstr.LOOP
            (bt : blocktype)
            (instrs : List instr)   => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t1s) :: p_context.LABELS}
                                               instrs
                                               (t1s f-> t2s)
        | admininstr.IFELSE
            (bt : blocktype)
            (instrs1 : List instr)
            (instrs2 : List instr)  => ∃ (t1s t2s : List valtype),
                                           p_functype = ((t1s ++ [valtype.I32]) f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs1
                                               (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs2
                                               (t1s f-> t2s)
        | admininstr.BR
            (l : labelidx)          => ∃ (t1s ts t2s : List valtype),
                                           p_functype = ((t1s ++ ts) f-> t2s)
                                         ∧ p_context.LABELS[proj_uN_0 l]? = some (list.mk_list ts)

        | admininstr.BR_IF
            (l : labelidx)          => ∃ (ts : List valtype),
                                           p_functype = ((ts ++ [valtype.I32]) f-> ts)
                                         ∧ p_context.LABELS[proj_uN_0 l]? = some (list.mk_list ts)

        | admininstr.BR_TABLE
            (ls : List labelidx)
            (l' : labelidx)         => ∃ (t1s ts t2s : List valtype),
                                           p_functype = ((t1s ++ ts ++ [valtype.I32]) f-> t2s)
                                         ∧ ∀ l ∈ ls,
                                               ∃ (r : resulttype),
                                                   p_context.LABELS[proj_uN_0 l]? = some r
                                                 ∧ Resulttype_sub (list.mk_list ts) r
                                         ∧ ∃ (r' : resulttype),
                                               p_context.LABELS[proj_uN_0 l']? = some r'
                                             ∧ Resulttype_sub (list.mk_list ts) r'

        | admininstr.CALL
            (x : funcidx)           => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ p_context.FUNCS[proj_uN_0 x]? = some (t1s f-> t2s)

        | admininstr.CALL_INDIRECT
            (x : tableidx)
            (y : typeidx)           => ∃ (t1s t2s : List valtype) (lim : limits),
                                           p_functype = ((t1s ++ [valtype.I32]) f-> t2s)
                                         ∧ p_context.TABLES[proj_uN_0 x]? = (tabletype.mk_tabletype lim reftype.FUNCREF)
                                         ∧ p_context.TYPES[proj_uN_0 y]? = some (t1s f-> t2s)

        | admininstr.RETURN         => ∃ (t1s ts t2s : List valtype),
                                           p_functype = ((t1s ++ ts) f-> t2s)
                                         ∧ p_context.RETURN = some (list.mk_list ts)

        | admininstr.CONST
            (nt : numtype)
            (c : num_)              => p_functype = ([] f-> [valtype_numtype nt])
                                     ∧ wf_num_ nt c

        | admininstr.UNOP
            (nt : numtype)
            (u : unop_)             => p_functype = ([valtype_numtype nt] f-> [valtype_numtype nt])


        | admininstr.BINOP
            (nt : numtype)
            (b : binop_)            => p_functype = ([valtype_numtype nt, valtype_numtype nt] f-> [valtype_numtype nt])

        | admininstr.TESTOP
            (nt : numtype)
            (t : testop_)           => p_functype = ([valtype_numtype nt] f-> [valtype.I32])

        | admininstr.RELOP
            (nt : numtype)
            (r : relop_)            => p_functype = ([valtype_numtype nt, valtype_numtype nt] f-> [valtype.I32])

        -- TODO: I think we don't split into both cvtop-reinterpret and cvtop-convert
        -- because cvtop *includes* REINTERPRET, and that causes the proof to jam.
        -- To solve this, we need to modify the syntax so that they are separate, which
        -- I think is the TODO already in 6-typing.spectec for Wasm 2.0.
        | admininstr.CVTOP
            (nt1 : numtype)
            (nt2 : numtype)
            (c : cvtop)             => p_functype = ([valtype_numtype nt2] f-> [valtype_numtype nt1])

        | admininstr.VCONST
            (vt : vectype)
            (c : vec_)              => ∃ (uN_size : Nat),
                                           size (valtype_vectype vt) = some uN_size
                                         ∧ wf_uN uN_size c
                                         ∧ p_functype = ([] f-> [valtype_vectype vt])

        | admininstr.REF_NULL
            (rt : reftype)          => p_functype = ([] f-> [valtype_reftype rt])
        | admininstr.REF_FUNC
            (x : funcidx)           => ∃ (ft : functype),
                                           p_functype = ([] f-> [valtype_reftype reftype.FUNCREF])
                                         ∧ p_context.FUNCS[proj_uN_0 x]? = some ft

        | admininstr.REF_IS_NULL    => ∃ (rt : reftype),
                                           p_functype = ([valtype_reftype rt] f-> [valtype.I32])

        | admininstr.LOCAL_GET
            (x : localidx)          => ∃ (t : valtype),
                                           p_functype = ([] f-> [t])
                                         ∧ p_context.LOCALS[proj_uN_0 x]? = some t

        | admininstr.LOCAL_SET
            (x : localidx)          => ∃ (t : valtype),
                                           p_functype = ([t] f-> [])
                                         ∧ p_context.LOCALS[proj_uN_0 x]? = some t

        | admininstr.LOCAL_TEE
            (x : localidx)          => ∃ (t : valtype),
                                           p_functype = ([t] f-> [t])
                                         ∧ p_context.LOCALS[proj_uN_0 x]? = some t

        | admininstr.GLOBAL_GET
            (x : globalidx)         => ∃ (t : valtype) (m : «mut»),
                                           p_functype = ([] f-> [t])
                                         ∧ p_context.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype m t)

        | admininstr.GLOBAL_SET
            (x : globalidx)         => ∃ (t : valtype) (m : «mut»),
                                           p_functype = ([t] f-> [])
                                         ∧ p_context.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype m t)

        | admininstr.TABLE_GET
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32] f-> [valtype_reftype rt])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_SET
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32, valtype_reftype rt] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)


        | admininstr.TABLE_SIZE
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([] f-> [valtype.I32])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_GROW
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype_reftype rt, valtype.I32] f-> [valtype.I32])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_FILL
            (x : tableidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32, valtype_reftype rt, valtype.I32] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt)

        | admininstr.TABLE_COPY
            (x1 : tableidx)
            (x2 : tableidx)         => ∃ (rt : reftype) (lim1 lim2 : limits),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x1]? = some (tabletype.mk_tabletype lim1 rt)
                                         ∧ p_context.TABLES[proj_uN_0 x2]? = some (tabletype.mk_tabletype lim2 rt)

        | admininstr.TABLE_INIT
            (x1 : tableidx)
            (x2 : elemidx)          => ∃ (rt : reftype) (lim : limits),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.TABLES[proj_uN_0 x1]? = some (tabletype.mk_tabletype lim rt)
                                         ∧ p_context.ELEMS[proj_uN_0 x2]? = some rt

        | admininstr.ELEM_DROP
            (x : elemidx)           => ∃ (rt : reftype),
                                           p_functype = ([] f-> [])
                                         ∧ p_context.ELEMS[proj_uN_0 x]? = some rt

        | admininstr.LOAD
            (nt : numtype)
            none
            (marg : memarg)         => ∃ (mt : memtype) (s : Nat),
                                           p_functype = ([valtype.I32] f-> [valtype_numtype nt])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ size (valtype_numtype nt) = some s
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (s / 8)

        -- TODO: probably correct, but check ai-gen
        | admininstr.LOAD
            (nt : numtype)
            (
                some (
                    loadop_.mk_loadop__0
                    (inntype : Inn)
                    (
                        loadop_Inn.mk_loadop_Inn
                        (sz.mk_sz (num_bits_to_read : Nat))
                        _ -- (issigned : sx)
                    )
                )
            )
            (marg : memarg)         => nt = numtype_Inn inntype
                                     ∧ ∃ (mt : memtype),
                                           p_functype = ([valtype.I32] f-> [valtype_Inn inntype])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (num_bits_to_read / 8)

        | admininstr.STORE
            (nt : numtype)
            none
            (marg: memarg)          => ∃ (mt : memtype) (s : Nat),
                                           p_functype = ([valtype.I32, valtype_numtype nt] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ size (valtype_numtype nt) = some s
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (s / 8)

        | admininstr.STORE
            (nt : numtype)
            (some (sz.mk_sz (num_bits_to_read : Nat)))
            (marg : memarg)

                                    -- unlike the LOAD case, we need to
                                    -- existentially quantify inntype here
                                    -- because it is not uniquely determined by
                                    -- num_bits_to_read
                                    => ∃ (mt : memtype) (inntype : Inn),
                                           nt = numtype_Inn inntype
                                         ∧ p_functype = ([valtype.I32, valtype_numtype nt] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ 2^(proj_uN_0 marg.ALIGN) ≤ (num_bits_to_read / 8)

        | admininstr.MEMORY_SIZE    => ∃ (mt : memtype),
                                           p_functype = ([] f-> [valtype.I32])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_GROW    => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32] f-> [valtype.I32])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_FILL    => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_COPY    => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt

        | admininstr.MEMORY_INIT
            (x : dataidx)           => ∃ (mt : memtype),
                                           p_functype = ([valtype.I32, valtype.I32, valtype.I32] f-> [])
                                         ∧ p_context.MEMS[0]? = some mt
                                         ∧ p_context.DATAS[proj_uN_0 x]? = some datatype.OK

        | admininstr.DATA_DROP
            (x : dataidx)           => p_functype = ([] f-> [])
                                     ∧ p_context.DATAS[proj_uN_0 x]? = some datatype.OK

        | admininstr.REF_FUNC_ADDR
            (a : funcaddr)          => ∃ (ft : functype),
                                           p_functype = ([] f-> [valtype_reftype reftype.FUNCREF])
                                         ∧ Externaddr_ok p_store (externaddr.FUNC a) (externtype.FUNC ft)

        | admininstr.CALL_ADDR
            (a : funcaddr)          => ∃ (ts1 ts2 : List valtype),
                                           p_functype = (ts1 f-> ts2)
                                         ∧ Externaddr_ok p_store (externaddr.FUNC a) (externtype.FUNC (ts1 f-> ts2))

        | admininstr.LABEL_
            (_n : n)
            (instrs : List instr)
            (admininstrs : List admininstr)
                                    => ∃ (ts t's : List valtype),
                                           p_functype = ([] f-> ts)
                                         ∧ t's.length = _n
                                         ∧ Instrs_ok2
                                               p_store
                                               p_context
                                               (instrs.map admininstr_instr)
                                               (t's f-> ts)
                                         ∧ Instrs_ok2
                                               p_store
                                               {p_context with LABELS := (list.mk_list t's) :: p_context.LABELS}
                                               admininstrs
                                               ([] f-> ts)

        | admininstr.FRAME_
            (n_ : n)
            (f : frame)
            (admininstrs : List admininstr)
                                    => ∃ (ts : List valtype) (c' : context),
                                           p_functype = ([] f-> ts)
                                         ∧ Frame_ok p_store f c'
                                         ∧ Expr_ok2 p_store c' admininstrs (list.mk_list ts)

        | admininstr.TRAP           => true

        -- TODO: I think this hasn't been implemented yet in the spec?
        | admininstr.EXTEND
            (_ : numtype)
            (_ : n)                 => false

        | _                           => true

def instr_principal_typing
    (context : context) (instruction : instr) (functype : functype) : Prop :=
    ai_principal_typing
        -- NOTE!!
        --
        -- We rely on the fact that the store is not used in any instr, so we
        -- pass a dummy store to reduce work.
        (store.MKstore [] [] [] [] [] [])

        context
        (admininstr_instr instruction)
        functype

theorem instr_typing_inversion
    (c : context)
    (instr : instr)
    (t1s t2s : List valtype)
    :
    Instr_ok c instr (t1s f-> t2s) →
    instr_principal_typing c instr (t1s f-> t2s) :=
    by
        intro h
        cases h
        <;> unfold instr_principal_typing
        <;> unfold ai_principal_typing
        <;> simp only [admininstr_instr]
        <;> try simp_all

        case drop t wf_drop wf_c =>
            exists t

        case select_impl
            t t' nt vt subt
            t'_constraints wf_select wf_c =>
            exists t
            apply And.intro
            · rfl
            · exists t'
              apply And.intro
              · exact subt
              · exists nt
                rcases t'_constraints with t'_constraint | t'_constraint
                · left
                  exact t'_constraint
                · right
                  exists vt

        case block
            bt instrs wf_block wf_c wf_c' bt_ok instrs_ok =>
            exists t1s
            exists t2s

        case loop
            bt instrs wf_loop wf_c wf_c' bt_ok instrs_ok =>
            exists t1s
            exists t2s

        case «if»
            bt instrs1 instrs2 t wf_if wf_c wf_c' bt_ok instrs1_ok instrs2_ok =>
            exists t
            exists t2s

        case br
            lidx t1s ts wf_br lidx_within_LABELS LABELS_gives_ts wf_c =>
            exists t1s
            exists ts
            apply And.intro
            · exists t2s
            · unfold proj_list_0 at LABELS_gives_ts
              have hlab : c.LABELS[proj_uN_0 lidx] = mk_list ts :=
                Eq.subst (motive := fun z => c.LABELS[proj_uN_0 lidx] = mk_list z) LABELS_gives_ts rfl
              exact hlab

        case br_if
            lidx wf_br_if lidx_within_LABELS wf_c LABELS_gives_t2s =>
            exists t2s
            apply And.intro
            · rfl
            · unfold proj_list_0 at LABELS_gives_t2s
              have h : c.LABELS[(proj_uN_0 lidx)] = (mk_list t2s) :=
                Eq.subst (motive := fun x => c.LABELS[(proj_uN_0 lidx)] = mk_list x) LABELS_gives_t2s rfl
              exact h

        case br_table
            ls l' t1s ts wf_br_table ls_within_LABELS l'_within_LABELS ts_sub_ls l'_within_LABELS2 ts_sub_l' wf_c =>
            exists t1s
            exists ts
            apply And.intro
            · exists t2s
            · intro l hl
              have l_within_LABELS : (proj_uN_0 l) < c.LABELS.length :=
                ls_within_LABELS l hl
              refine ⟨c.LABELS[proj_uN_0 l]'l_within_LABELS, by simp, ?_, ts_sub_l'⟩
              have h : Resulttype_sub (mk_list ts) (c.LABELS[(proj_uN_0 l)]?.getD default) :=
                ts_sub_ls l hl
              have hh : c.LABELS[(proj_uN_0 l)]?.getD default = c.LABELS[(proj_uN_0 l)] :=
                by
                  simp [l_within_LABELS]
              rw [hh] at h
              exact h

        · case call
            idx wf_call idx_within_FUNCS wf_c FUNCS_gives_ft =>
            exists t1s
            exists t2s

        · case call_indirect
            idx1 idx2 t1s lim wf_call_indirect wf_tt idx1_within_TABLES idx2_within_TYPES
            TABLES_gives_tt idx2_within_TYPES2 wf_c TYPES_gives_ft =>
            exists t1s, t2s

        · case «return»
            t1s ts wf_return RETURN_gives_ts wf_c =>
            exists t1s, t2s

        · case const
            nt n wf_const wf_c =>
            cases wf_const with
            | instr_case_13 nt n h =>
                exact h

            -- cases wf_const
            -- rename_i blah
            -- exact blah

            -- rcases wf_const with ⟨s⟩
            -- rename_i blah
            -- exact blah

        · case ref_func
            idx ft wf_ref_func idx_in_FUNCS FUNCS_gives_ft wf_c =>
            rfl

        · case ref_is_null
            rt wr_ref_is_null wf_c =>
            exists rt

        · case vconst
            vec wf_vconst wf_c =>
            cases wf_vconst with
            | instr_case_20 vt v not_none_size wf_vec =>
                refine ⟨(size (valtype_vectype vectype.V128)).get!, ?_, ?_, ?_⟩
                -- · have x := Option.ne_none_iff_exists.mp not_none_size
                · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp not_none_size
                  rfl

                · exact wf_vec

                · rfl


                -- refine ⟨?_, ?_, ?_, ?_⟩
                -- · cases wf_vec with
                --   | uN_case_0 n i h =>
                --       exists n


                -- cases wf_vec with
                -- | uN_case_0 n i =>
                --     exists n

        · case load_val
            nt marg mt MEMS_length_nonzero nt_size_not_none
            size_constraint wf_mt wf_load MEMS_length_nonzero2
            mt_at_MEMS_0_idx wf_c =>
            refine ⟨(size (valtype_numtype nt)).get!, ?_, ?_⟩
            · cases nt <;>
              simp [size, valtype_numtype]
            · cases nt <;>
              simp [size, valtype_numtype] at size_constraint ⊢ <;>
              norm_num at size_constraint <;>
              exact_mod_cast size_constraint

        · case load_pack
            inn m is_signed marg mt size_constraint wf_inn
            wf_load MEMS_not_empty MEMS_0_is_marg wf_c =>
            cases m
            · norm_num at size_constraint ⊢
              have h_false : False := by
                have h_pos : (2 ^ (proj_uN_0 marg.ALIGN)) > (0 : Rat) := by positivity
                linarith only [size_constraint, h_pos]
              exact h_false
            · rename_i n
              have bridge :
                ∀ (n0 n1 n2 : Nat), n0 ≤ ((n1 : Rat) / n2) → n0 ≤ (n1 / n2) := by
                    intros n0 n1 n2 h
                    rcases Nat.eq_zero_or_pos n2 with hz | hpos
                    · subst hz
                      simp at h ⊢
                      exact_mod_cast h
                    · rcases lt_or_ge ((n1:Rat) / n2) (n0 + 1 : Rat) with hlt | hge
                      · have heq : n1 / n2 = n0 := by
                          have hmul_le : n0 * n2 ≤ n1 := by
                            rw [le_div_iff₀ (by exact_mod_cast hpos : (0:Rat) < n2)] at h
                            exact_mod_cast h
                          have hmul_lt : n1 < (n0 + 1) * n2 := by
                            rw [div_lt_iff₀ (by exact_mod_cast hpos : (0:Rat) < n2)] at hlt
                            exact_mod_cast hlt
                          have h1 : n0 ≤ (n1 / n2) := (Nat.le_div_iff_mul_le hpos).mpr hmul_le
                          have h2 : (n1 / n2) < (n0 + 1) := (Nat.div_lt_iff_lt_mul hpos).mpr hmul_lt
                          omega
                        omega
                      · have : n0 + 1 ≤ n1 / n2 := by
                          rw [Nat.le_div_iff_mul_le hpos]
                          rw [le_div_iff₀ (by exact_mod_cast hpos)] at hge
                          exact_mod_cast hge
                        omega
              exact_mod_cast
                bridge (2 ^ (proj_uN_0 marg.ALIGN)) n.succ 8
                  (by exact_mod_cast size_constraint)

                    -- rcases Nat.eq_zero_or_pos n2 with hz_n2 | hpos_n2
                    -- · subst hz_n2
                    --   simp at h ⊢
                    --   exact h
                    -- · rcases Nat.eq_zero_or_pos n1 with hz_n1 | hpos_n1
                    --   · subst hz_n1
                    --     simp at h ⊢
                    --     exact h
                    --   ·

        · case store_val
            nt marg mt MEMS_length_nonzero nt_size_not_none size_constraint
            wf_mt wf_store MEMS_length_nonzero2 mt_at_MEMS_0_idx wf_c =>
            refine ⟨(size (valtype_numtype nt)).get!, ?_, ?_⟩
            · cases nt <;>
              simp [size, valtype_numtype]
            · cases nt <;>
              simp [size, valtype_numtype, Option.bind, Option.get] at size_constraint ⊢ <;>
              norm_num at size_constraint <;>
                exact_mod_cast size_constraint

        · case store_pack
            inn m marg mt size_constraint wf_mt wf_store
            MEMS_not_empty MEMS_0_is_mt wf_c =>
            apply And.intro
            · cases inn <;>
              simp [valtype_Inn, valtype_numtype] <;>
              rfl
            · have bridge :
                ∀ (n0 n1 n2 : Nat), n0 ≤ ((n1 : Rat) / n2) → n0 ≤ (n1 / n2) := by
                    intros n0 n1 n2 h
                    rcases Nat.eq_zero_or_pos n2 with h_zero | h_pos
                    · subst h_zero
                      simp [*] at h ⊢
                      exact h
                    · rcases lt_or_ge (n1 / n2) (n0 + 1) with h2_near | h_far
                      · have lower_limit : n1/n2 = n0 := by
                            let upper := h2_near
                            have lower : n0 ≤ n1/n2 := by
                                have h_throwaway : n0 * n2 ≤ n1 := by
                                    rw [le_div_iff₀ (by exact_mod_cast h_pos)] at h
                                    exact_mod_cast h
                                exact (Nat.le_div_iff_mul_le h_pos).mpr h_throwaway
                            omega
                        omega
                      · omega
              have applied_bridge := bridge ((2 : ℕ) ^ (proj_uN_0 marg.ALIGN)) m 8 (
                by
                exact_mod_cast size_constraint
              )
              exact applied_bridge
























-- theorem instr_typing_inversion
--     (context : context) (instruction : instr) (t1 : valtype) (t2 : valtype) :
--     Instr_ok context instruction (t1 :-> t2) →
--     instr_principal_typing context instruction (t1 :-> t2) :=
